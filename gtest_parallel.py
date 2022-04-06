# Copyright 2013 Google Inc. All rights reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
from enum import Enum
import errno
from functools import total_ordering
import gzip
import io
import json
import multiprocessing
import optparse
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import xml.etree.ElementTree as ET

if sys.version_info.major >= 3:
    long = int
    import _pickle as cPickle
    import _thread as thread
else:
    import cPickle
    import thread

from pickle import HIGHEST_PROTOCOL as PICKLE_HIGHEST_PROTOCOL

if sys.platform == 'win32':
  import msvcrt
else:
  import fcntl


# An object that catches SIGINT sent to the Python process and notices
# if processes passed to wait() die by SIGINT (we need to look for
# both of those cases, because pressing Ctrl+C can result in either
# the main process or one of the subprocesses getting the signal).
#
# Before a SIGINT is seen, wait(p) will simply call p.wait() and
# return the result. Once a SIGINT has been seen (in the main process
# or a subprocess, including the one the current call is waiting for),
# wait(p) will call p.terminate() and raise ProcessWasInterrupted.
class SigintHandler(object):
  class ProcessWasInterrupted(Exception): pass
  class ProcessTimeout(Exception): pass
  sigint_returncodes = {-signal.SIGINT,  # Unix
                        -1073741510,     # Windows
                        }
  def __init__(self):
    self.__lock = threading.Lock()
    self.__processes = set()
    self.__got_sigint = False
    self.__timeout = False
    signal.signal(signal.SIGINT, lambda signal_num, frame: self.interrupt())
  def __on_sigint(self):
    if not self.__timeout:
      self.__got_sigint = True
      while self.__processes:
        try:
          self.__processes.pop().terminate()
        except OSError:
          pass
  def interrupt(self):
    with self.__lock:
      self.__on_sigint()
  def got_sigint(self):
    with self.__lock:
      return self.__got_sigint
  def wait(self, p, timeout=None):
    with self.__lock:
      if self.__got_sigint:
        p.terminate()
      self.__processes.add(p)
    try:
      code = p.wait(timeout=timeout)
    except (subprocess.TimeoutExpired):
      with self.__lock:
        self.__timeout = True
        p.terminate()
      pass

    with self.__lock:
      self.__processes.discard(p)
      if self.__timeout:
        self.__timeout = False
        raise self.ProcessTimeout
      if code in self.sigint_returncodes:
        self.__on_sigint()
      if self.__got_sigint:
        raise self.ProcessWasInterrupted
    return code
sigint_handler = SigintHandler()


# Return the width of the terminal, or None if it couldn't be
# determined (e.g. because we're not being run interactively).
def term_width(out):
  if not out.isatty():
    return None
  try:
    p = subprocess.Popen(["stty", "size"],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (out, err) = p.communicate()
    if p.returncode != 0 or err:
      return None
    return int(out.split()[1])
  except (IndexError, OSError, ValueError):
    return None


# Output transient and permanent lines of text. If several transient
# lines are written in sequence, the new will overwrite the old. We
# use this to ensure that lots of unimportant info (tests passing)
# won't drown out important info (tests failing).
class Outputter(object):
  def __init__(self, out_file):
    self.__out_file = out_file
    self.__previous_line_was_transient = False
    self.__width = term_width(out_file)  # Line width, or None if not a tty.
  def transient_line(self, msg):
    if self.__width is None:
      self.__out_file.write(msg + "\n")
      self.__out_file.flush()
    else:
      self.__out_file.write("\r" + msg[:self.__width].ljust(self.__width))
      self.__previous_line_was_transient = True
  def flush_transient_output(self):
    if self.__previous_line_was_transient:
      self.__out_file.write("\n")
      self.__previous_line_was_transient = False
  def permanent_line(self, msg):
    self.flush_transient_output()
    self.__out_file.write(msg + "\n")
    if self.__width is None:
      self.__out_file.flush()


def get_save_file_path():
  """Return path to file for saving transient data."""
  if sys.platform == 'win32':
    default_cache_path = os.path.join(os.path.expanduser('~'),
                                      'AppData', 'Local')
    cache_path = os.environ.get('LOCALAPPDATA', default_cache_path)
  else:
    # We don't use xdg module since it's not a standard.
    default_cache_path = os.path.join(os.path.expanduser('~'), '.cache')
    cache_path = os.environ.get('XDG_CACHE_HOME', default_cache_path)

  if os.path.isdir(cache_path):
    return os.path.join(cache_path, 'gtest-parallel')
  else:
    sys.stderr.write('Directory {} does not exist'.format(cache_path))
    return os.path.join(os.path.expanduser('~'), '.gtest-parallel-times')


@total_ordering
class Task(object):
  """Stores information about a task (single execution of a test).

  This class stores information about the test to be executed (gtest binary and
  test name), and its result (log file, exit code and runtime).
  Each task is uniquely identified by the gtest binary, the test name and an
  execution number that increases each time the test is executed.
  Additionaly we store the last execution time, so that next time the test is
  executed, the slowest tests are run first.
  """
  def __init__(self, 
               test_binary, 
               test_name, 
               test_command,
               test_timeout,
               should_log_xml, 
               execution_number,
               last_execution_time, 
               output_dir):
    self.test_name = test_name
    self.output_dir = output_dir
    self.test_binary = test_binary
    self.test_command = test_command
    self.test_timeout = test_timeout
    self.should_log_xml = should_log_xml
    self.execution_number = execution_number
    self.last_execution_time = last_execution_time

    self.exit_code = None
    self.runtime_ms = None
    self.process_timeout = False

    self.test_id = (test_binary, test_name)
    self.task_id = (test_binary, test_name, self.execution_number)
    self.log_file = Task._logname(self.output_dir, self.test_binary,
                                  test_name, self.execution_number)
    
    # xml file is located in the same space as the log file,
    # with the same root name, but a different extension (.xml)
    self.xml_file = None
    self.__complete_command = self.test_command[:]
    if should_log_xml:
      self.xml_file = os.path.splitext(self.log_file)[0] + '.xml'
      self.__complete_command += ['--gtest_output=xml:' + os.path.abspath(self.xml_file)]

  def __sorting_key(self):
    # Unseen or failing tests (both missing execution time) take precedence over
    # execution time. Tests are greater (seen as slower) when missing times so
    # that they are executed first.
    return (1 if self.last_execution_time is None else 0,
            self.last_execution_time)

  def __eq__(self, other):
      return self.__sorting_key() == other.__sorting_key()

  def __ne__(self, other):
      return not (self == other)

  def __lt__(self, other):
      return self.__sorting_key() < other.__sorting_key()

  @staticmethod
  def _normalize(string):
    return re.sub('[^A-Za-z0-9]', '_', string)

  @staticmethod
  def _logname(output_dir, test_binary, test_name, execution_number):
    # Store logs to temporary files if there is no output_dir.
    if output_dir is None:
      (log_handle, log_name) = tempfile.mkstemp(prefix='gtest_parallel_',
                                                suffix=".log")
      os.close(log_handle)
      return log_name

    log_name = '%s-%s-%d.log' % (Task._normalize(os.path.basename(test_binary)),
                                 Task._normalize(test_name), execution_number)

    return os.path.join(output_dir, log_name)

  def run(self):
    begin = time.time()
    with open(self.log_file, 'w') as log:
      task = subprocess.Popen(self.__complete_command, stdout=log, stderr=log)
      try:
        self.exit_code = sigint_handler.wait(task, timeout = self.test_timeout)
      except sigint_handler.ProcessWasInterrupted:
        thread.exit()
      except sigint_handler.ProcessTimeout:
        self.process_timeout = True
        pass
    self.runtime_ms = int(1000 * (time.time() - begin))
    self.last_execution_time = None if self.exit_code else self.runtime_ms

class TaskOutcome(Enum):
  """
  Handy enum type used to interpret Task outcomes
  """
  PASS = 0
  FAIL = 1
  TIMEOUT = 2

class XMLLogger(object):
  """
  Aggregates XML data from individual test log files into a single XML file
  """
  def __init__(self, xml_dump_filepath):
    self.test_results_lock = threading.Lock()
    self.xml_dump_filepath = xml_dump_filepath
    self.output_xml = None

  def __fetch_test_output(self, test_name, log_file):
    """
    Read from a test's log file and return all text after the initial
    RUN/OK/FAILED preamble
    """
    output = ""
    start_pattern = re.compile(".*\[ *RUN *\].*" + test_name)
    success_pattern = re.compile(".*\[ *OK *\].*" + test_name)
    failure_pattern = re.compile(".*\[ *FAILED *\].*" + test_name)
    with open(log_file) as log:
      for line in log:
        if start_pattern.search(line.strip()) is not None:
          break
      for line in log:
        stripped = line.strip()
        if ((success_pattern.search(stripped) is not None) or 
            (failure_pattern.search(stripped) is not None)):
          break
        output += line
    return output

  def __generate_blank_xml(self, test_name, runtime_ms):
    """
    Generate blank XML for a test matching the GoogleTest XML format, 
    given the test's name and runtime.
    """
    suites_state = {'tests': '1', 
                    'failures': '0',
                    'disabled': '0',
                    'errors': '0',
                    'name': 'AllTests'}
    suites = ET.Element('testsuites', suites_state)
    suite_and_test_name = test_name.split('.')
    suite_state = {'name': suite_and_test_name[0],
                  'tests': '1',
                  'failures': '0',
                  'disabled': '0',
                  'skipped': '0',
                  'errors': '0'}
    suite = ET.SubElement(suites, 'testsuite', suite_state)
    test_state = {'name': suite_and_test_name[1],
                  'status': 'run',
                  'time': str(runtime_ms / 1000.0),
                  'classname': suite_and_test_name[0]}
    test = ET.SubElement(suite, 'testcase', test_state)
    return ET.ElementTree(suites)
  
  def __construct_from_timeout(self, task):
    """
    Helper: Construct conformant XML from a test that has timed out (and thus hasn't
    produced valid XML on its own)
    """
    xml = self.__generate_blank_xml(task.test_name, task.runtime_ms)
    root = xml.getroot()
    root.set('failures', '1')
    suite = root.find('testsuite')
    suite.set('failures', '1')
    case = suite.find('testcase')
    timeout_state = {
      'message': 'The test timed out after ' + str(task.runtime_ms / 1000.0) + ' seconds'
    }
    ET.SubElement(case, 'failure', timeout_state)
    return xml

  def __construct_from_failure(self, task):
    """
    Helper: Construct conformant XML from a test that has failed. If the test crashed,
    it may not have generated valid XML. Handle this case by manually-constructing
    conformant XML from stdout/stderr output
    """
    try:
      return ET.parse(task.xml_file)
    except:
      xml = self.__generate_blank_xml(task.test_name, task.runtime_ms)
      root = xml.getroot()
      root.set('failures', '1')
      suite = root.find('testsuite')
      suite.set('failures', '1')
      case = suite.find('testcase')
      msg = self.__fetch_test_output(task.test_name, task.log_file)
      ET.SubElement(case, 'failure', {'message': msg})
      return xml

  def __generate_new_xml(self, task, result):
    """
    Helper: Generate valid / conformant XML given a Task and its Result. Handles
    PASS, TIMEOUT, and FAILURE TaskOutcomes.
    """
    if result is TaskOutcome.PASS: 
      return ET.parse(task.xml_file)
    if result is TaskOutcome.TIMEOUT:
      return self.__construct_from_timeout(task)
    if result is TaskOutcome.FAIL:
      return self.__construct_from_failure(task)

  def __combine_xml(self, suites_to_add):
    """
    Add new XML test results to existing XML test results
    """
    testsuites = self.output_xml.getroot()
    new_suites = suites_to_add.getroot()

    def increment_count(element, attrib_name):
      element.set(attrib_name, str(int(element.get(attrib_name)) + 1))

    for suite_to_add in new_suites:
      for existing_suite in testsuites:
        if suite_to_add.get('name') == existing_suite.get('name'):
          # found: update element attributes
          # here we're relying on the fact that suite_to_add will only have one testcase
          if suite_to_add.get('failures') != '0':
            increment_count(existing_suite, 'failures')
            increment_count(testsuites, 'failures')
          if suite_to_add.get('disabled') != '0':
            increment_count(existing_suite, 'disabled')
            increment_count(testsuites, 'disabled')
          if suite_to_add.get('errors') != '0':
            increment_count(existing_suite, 'errors')
            increment_count(testsuites, 'errors')
          if suite_to_add.get('skipped') != '0':
            increment_count(existing_suite, 'skipped') # skipped not a member of `testsuites` 
          # then, append each test case to main_XML testsuite
          for case in suite_to_add:
            increment_count(existing_suite, 'tests')
            increment_count(testsuites, 'tests')
            existing_suite.append(case)
          suite_to_add.clear() # clear out appended suites, sets attribs to None

    # add any testsuites that don't match existing to the list of testsuites
    for suite_to_add in new_suites:
      if suite_to_add.get('name') is not None:
        increment_count(testsuites, 'tests')
        if suite_to_add.get('failures') != '0':
          increment_count(testsuites, 'failures')
        if suite_to_add.get('disabled') != '0':
          increment_count(testsuites, 'disabled')
        if suite_to_add.get('errors') != '0':
          increment_count(testsuites, 'errors')
        testsuites.append(suite_to_add)

  def log_xml(self, task, result):
    """
    Log a test's result, aggregating it with existing results
    """
    with self.test_results_lock:
      if self.output_xml is None:
        # first XML file found: just directly copy XML from temp file
        self.output_xml = self.__generate_new_xml(task, result)
      else:
        new_xml = self.__generate_new_xml(task, result)
        self.__combine_xml(new_xml)

  def dump_to_file_and_close(self):
    """
    Dump tests results to the XML file specified at construction
    """
    if(self.output_xml):
      self.output_xml.write(self.xml_dump_filepath)

class TaskManager(object):
  """Executes the tasks and stores the passed, failed and interrupted tasks.

  When a task is run, this class keeps track if it passed, failed or was
  interrupted. After a task finishes it calls the relevant functions of the
  Logger, TestResults and TestTimes classes, and in case of failure, retries the
  test as specified by the --retry_failed flag.
  """
  def __init__(self, times, logger, xml_logger, task_factory, output_dir, times_to_retry,
               initial_execution_number):
    self.times = times
    self.logger = logger
    self.xml_logger = xml_logger
    self.task_factory = task_factory
    self.output_dir = output_dir
    self.times_to_retry = times_to_retry
    self.initial_execution_number = initial_execution_number

    self.global_exit_code = 0

    self.passed = []
    self.failed = []
    self.started = {}
    self.execution_number = {}

    self.lock = threading.Lock()

  def __get_next_execution_number(self, test_id):
    with self.lock:
      next_execution_number = self.execution_number.setdefault(
          test_id, self.initial_execution_number)
      self.execution_number[test_id] += 1
    return next_execution_number

  def __register_start(self, task):
    with self.lock:
      self.started[task.task_id] = task

  def __register_exit(self, task):
    self.logger.log_exit(task)
    self.times.record_test_time(task.test_binary, task.test_name,
                                task.last_execution_time)

    def try_remove_file(log):
      """ Try to remove the file 100 times (sleeping for 0.1 second in between).
      This is a workaround for a process handle seemingly holding on to the
      file for too long inside os.subprocess. This workaround is in place
      until we figure out a minimal repro to report upstream (or a better
      suspect) to prevent os.remove exceptions."""
      num_tries = 100
      for i in range(num_tries):
        try:
          os.remove(log)
        except OSError as e:
          if e.errno is not errno.ENOENT: 
            if i is num_tries - 1:
              self.out.permanent_line('Could not remove temporary log file: ' + str(e))
            else:
              time.sleep(0.1)
            continue
        break

    if self.xml_logger:
      result = TaskOutcome.FAIL
      if task.process_timeout:
        result = TaskOutcome.TIMEOUT
      elif task.exit_code == 0:
        result = TaskOutcome.PASS
      self.xml_logger.log_xml(task, result)
      # Always remove temporary xml file
      # (these will be aggregated into one file)
      try_remove_file(task.xml_file)

    # Only remove log file if output dir not specified
    if self.output_dir is None:
      try_remove_file(task.log_file)

    with self.lock:
      self.started.pop(task.task_id)
      if task.exit_code == 0:
        self.passed.append(task)
      else:
        self.failed.append(task)

  def run_task(self, task):
    for try_number in range(self.times_to_retry + 1):
      self.__register_start(task)
      task.run()
      self.__register_exit(task)

      if task.exit_code == 0:
        break

      if try_number < self.times_to_retry:
        execution_number = self.__get_next_execution_number(task.test_id)
        # We need create a new Task instance. Each task represents a single test
        # execution, with its own runtime, exit code and log file.
        task = self.task_factory(task.test_binary, 
                                 task.test_name,
                                 task.test_command,
                                 task.test_timeout,
                                 task.should_log_xml,
                                 execution_number,
                                 task.last_execution_time,
                                 task.output_dir)

    with self.lock:
      if task.exit_code != 0:
        self.global_exit_code = task.exit_code


class FilterFormat(object):
  def __init__(self, output_dir):
    if sys.stdout.isatty():
      # stdout needs to be unbuffered since the output is interactive.
      if isinstance(sys.stdout, io.TextIOWrapper):
        # workaround for https://bugs.python.org/issue17404
        sys.stdout = io.TextIOWrapper(sys.stdout.detach(),
                                      line_buffering=True,
                                      write_through=True,
                                      newline='\n')
      else:
        sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', 0)

    self.output_dir = output_dir

    self.total_tasks = 0
    self.finished_tasks = 0
    self.out = Outputter(sys.stdout)
    self.stdout_lock = threading.Lock()

  def move_to(self, destination_dir, tasks):
    if self.output_dir is None:
      return

    destination_dir = os.path.join(self.output_dir, destination_dir)
    os.makedirs(destination_dir)
    for task in tasks:
      shutil.move(task.log_file, destination_dir)

  def print_tests(self, message, tasks, print_try_number):
    self.out.permanent_line("%s (%s/%s):" %
                            (message, len(tasks), self.total_tasks))
    for task in sorted(tasks):
      runtime_ms = 'Interrupted'
      if task.runtime_ms is not None:
        runtime_ms = '%d ms' % task.runtime_ms
      if task.process_timeout:
        runtime_ms = 'Timeout'
      self.out.permanent_line("%11s: %s %s%s" % (
          runtime_ms, task.test_binary, task.test_name,
          (" (try #%d)" % task.execution_number) if print_try_number else ""))

  def log_exit(self, task):
    with self.stdout_lock:
      self.finished_tasks += 1
      self.out.transient_line("[%d/%d] %s (%d ms)"
                              % (self.finished_tasks, self.total_tasks,
                                 task.test_name, task.runtime_ms))
      if task.exit_code != 0:
        with open(task.log_file) as f:
          for line in f.readlines():
            self.out.permanent_line(line.rstrip())
        if task.process_timeout:
          self.out.permanent_line(
            "[%d/%d] %s timed out"
            % (self.finished_tasks, self.total_tasks, task.test_name))
        else:
          self.out.permanent_line(
            "[%d/%d] %s returned/aborted with exit code %d (%d ms)"
            % (self.finished_tasks, self.total_tasks, task.test_name,
               task.exit_code, task.runtime_ms))

  def log_tasks(self, total_tasks):
    self.total_tasks += total_tasks
    self.out.transient_line("[0/%d] Running tests..." % self.total_tasks)

  def summarize(self, passed_tasks, failed_tasks, interrupted_tasks):
    stats = {}
    def add_stats(stats, task, idx):
      task_key = (task.test_binary, task.test_name)
      if not task_key in stats:
        # (passed, failed, interrupted) task_key is added as tie breaker to get
        # alphabetic sorting on equally-stable tests
        stats[task_key] = [0, 0, 0, task_key]
      stats[task_key][idx] += 1

    for task in passed_tasks:
      add_stats(stats, task, 0)
    for task in failed_tasks:
      add_stats(stats, task, 1)
    for task in interrupted_tasks:
      add_stats(stats, task, 2)

    self.out.permanent_line("SUMMARY:")
    for task_key in sorted(stats, key=stats.__getitem__):
      (num_passed, num_failed, num_interrupted, _) = stats[task_key]
      (test_binary, task_name) = task_key
      total_runs = num_passed + num_failed + num_interrupted
      if num_passed == total_runs:
        continue
      self.out.permanent_line(
          "  %s %s passed %d / %d times%s." %
              (test_binary, task_name, num_passed, total_runs,
               "" if num_interrupted == 0 else (" (%d interrupted)" % num_interrupted)))

  def flush(self):
    self.out.flush_transient_output()

# Record of test runtimes. Has built-in locking.
class TestTimes(object):
  class LockedFile(object):
    def __init__(self, filename, mode):
      self._filename = filename
      self._mode = mode
      self._fo = None

    def __enter__(self):
      self._fo = open(self._filename, self._mode)

      # Regardless of opening mode we always seek to the beginning of file.
      # This simplifies code working with LockedFile and also ensures that
      # we lock (and unlock below) always the same region in file on win32.
      self._fo.seek(0)

      try:
        if sys.platform == 'win32':
          # We are locking here fixed location in file to use it as
          # an exclusive lock on entire file.
          msvcrt.locking(self._fo.fileno(), msvcrt.LK_LOCK, 1)
        else:
          fcntl.flock(self._fo.fileno(), fcntl.LOCK_EX)
      except IOError:
        self._fo.close()
        raise

      return self._fo

    def __exit__(self, exc_type, exc_value, traceback):
      # Flush any buffered data to disk. This is needed to prevent race
      # condition which happens from the moment of releasing file lock
      # till closing the file.
      self._fo.flush()

      try:
        if sys.platform == 'win32':
          self._fo.seek(0)
          msvcrt.locking(self._fo.fileno(), msvcrt.LK_UNLCK, 1)
        else:
          fcntl.flock(self._fo.fileno(), fcntl.LOCK_UN)
      finally:
        self._fo.close()

      return exc_value is None

  def __init__(self, save_file):
    "Create new object seeded with saved test times from the given file."
    self.__times = {}  # (test binary, test name) -> runtime in ms

    # Protects calls to record_test_time(); other calls are not
    # expected to be made concurrently.
    self.__lock = threading.Lock()

    try:
      with TestTimes.LockedFile(save_file, 'rb') as fd:
        times = TestTimes.__read_test_times_file(fd)
    except IOError:
      # We couldn't obtain the lock.
      return

    # Discard saved times if the format isn't right.
    if type(times) is not dict:
      return
    for ((test_binary, test_name), runtime) in times.items():
      if (type(test_binary) is not str or type(test_name) is not str
          or type(runtime) not in {int, long, type(None)}):
        return

    self.__times = times

  def get_test_time(self, binary, testname):
    """Return the last duration for the given test as an integer number of
    milliseconds, or None if the test failed or if there's no record for it."""
    return self.__times.get((binary, testname), None)

  def record_test_time(self, binary, testname, runtime_ms):
    """Record that the given test ran in the specified number of
    milliseconds. If the test failed, runtime_ms should be None."""
    with self.__lock:
      self.__times[(binary, testname)] = runtime_ms

  def write_to_file(self, save_file):
    "Write all the times to file."
    try:
      with TestTimes.LockedFile(save_file, 'a+b') as fd:
        times = TestTimes.__read_test_times_file(fd)

        if times is None:
          times = self.__times
        else:
          times.update(self.__times)

        # We erase data from file while still holding a lock to it. This
        # way reading old test times and appending new ones are atomic
        # for external viewer.
        fd.seek(0)
        fd.truncate()
        with gzip.GzipFile(fileobj=fd, mode='wb') as gzf:
          cPickle.dump(times, gzf, PICKLE_HIGHEST_PROTOCOL)
    except IOError:
      pass  # ignore errors---saving the times isn't that important

  @staticmethod
  def __read_test_times_file(fd):
    try:
      with gzip.GzipFile(fileobj=fd, mode='rb') as gzf:
        times = cPickle.load(gzf)
    except Exception:
      # File doesn't exist, isn't readable, is malformed---whatever.
      # Just ignore it.
      return None
    else:
      return times


def parse_test_names(test_binary, list_command, run_disabled_tests):

  try:
    test_list = subprocess.check_output(list_command,
                                        stderr=subprocess.STDOUT)
  except subprocess.CalledProcessError as e:
    sys.exit("%s: %s\n%s" % (test_binary, str(e), e.output))

  try:
      test_list = test_list.split('\n')
  except TypeError:
      # subprocess.check_output() returns bytes in python3
      test_list = test_list.decode(sys.stdout.encoding).split('\n')

  tests = []
  test_group = ''

  for line in test_list:
    if not line.strip():
      continue
    if line[0] != " ":
      # Remove comments for typed tests and strip whitespace.
      test_group = line.split('#')[0].strip()
      continue
    # Remove comments for parameterized tests and strip whitespace.
    line = line.split('#')[0].strip()
    if not line:
      continue

    test_name = test_group + line
    if not run_disabled_tests and 'DISABLED_' in test_name:
      continue

    # Skip PRE_ tests which are used by Chromium.
    if '.PRE_' in test_name :
      continue
    
    tests.append(test_name)

  return tests

def find_tests(binaries, additional_args, options, times):
  test_count = 0
  tasks = []

  for test_binary in binaries:

    # build dict of test size -> test names for each binary
    test_sizes_command = [test_binary] + additional_args
    test_sizes = {'s': [], 'm': [], 'l':[], 'x': []}
    for size in test_sizes.keys():
      test_sizes_command += ['--size=' + size]
      test_sizes_command += ['--gtest_list_tests']
      test_sizes[size] = parse_test_names(test_binary, test_sizes_command, options.gtest_also_run_disabled_tests)

    command = [test_binary] + additional_args
    if options.gtest_also_run_disabled_tests:
      command += ['--gtest_also_run_disabled_tests']
    if options.size != '':
      command += ['--size=' + options.size]

    list_command = command + ['--gtest_list_tests']
    if options.test != '':
      list_command += ['--test=' + options.test]
    if options.gtest_filter != '':
      list_command += ['--gtest_filter=' + options.gtest_filter]

    command += ['--gtest_color=' + options.gtest_color]
    
    test_names = parse_test_names(test_binary, list_command, options.gtest_also_run_disabled_tests)
    for test_name in test_names:
      
      test_command = command + ['--gtest_filter=' + test_name]

      # enforce timeout based on test size:
      # - if in S, append timeout = 60s
      # - if in M, append timeout = 300s
      # - if in L, append timeout = 900s
      # - if in X, append timeout = 3600s
      timeout = 60 
      if test_name in test_sizes['m']:
        timeout = 300
      elif test_name in test_sizes['l']:
        timeout = 900
      elif test_name in test_sizes['x']:
        timeout = 3600

      last_execution_time = times.get_test_time(test_binary, test_name)
      if options.failed and last_execution_time is not None:
        continue
      
      should_log_xml = options.dump_xml_test_results
      if (test_count - options.shard_index) % options.shard_count == 0:
        for execution_number in range(options.repeat):
          tasks.append(Task(test_binary, 
                            test_name,
                            test_command,
                            timeout,
                            should_log_xml,
                            execution_number + 1,
                            last_execution_time,
                            options.output_dir))

      test_count += 1

  # Sort the tasks to run the slowest tests first, so that faster ones can be
  # finished in parallel.
  return sorted(tasks, reverse=True)


def execute_tasks(tasks, pool_size, task_manager,
                  timeout, serialize_test_cases):
  class WorkerFn(object):
    def __init__(self, tasks, running_groups):
      self.tasks = tasks
      self.running_groups = running_groups
      self.task_lock = threading.Lock()

    def __call__(self):
      while True:
        with self.task_lock:
          for task_id in range(len(self.tasks)):
            task = self.tasks[task_id]

            if self.running_groups is not None:
              test_group = task.test_name.split('.')[0]
              if test_group in self.running_groups:
                # Try to find other non-running test group.
                continue
              else:
                self.running_groups.add(test_group)

            del self.tasks[task_id]
            break
          else:
            # Either there is no tasks left or number or remaining test
            # cases (groups) is less than number or running threads.
            return

        task_manager.run_task(task)

        if self.running_groups is not None:
          with self.task_lock:
            self.running_groups.remove(test_group)

  def start_daemon(func):
    t = threading.Thread(target=func)
    t.daemon = True
    t.start()
    return t

  try:
    if timeout:
      timeout.start()
    running_groups = set() if serialize_test_cases else None
    worker_fn = WorkerFn(tasks, running_groups)
    workers = [start_daemon(worker_fn) for _ in range(pool_size)]
    for worker in workers:
      worker.join()
  finally:
    if timeout:
      timeout.cancel()


def default_options_parser():
  parser = optparse.OptionParser(
      usage = 'usage: %prog [options] binary [binary ...] -- [additional args]')

  parser.add_option('-d', '--output_dir', type='string', default=None,
                    help='Output directory for test logs. Logs will be '
                         'available under gtest-parallel-logs/, so '
                         '--output_dir=/tmp will results in all logs being '
                         'available under /tmp/gtest-parallel-logs/.')
  parser.add_option('-r', '--repeat', type='int', default=1,
                    help='Number of times to execute all the tests.')
  parser.add_option('--retry_failed', type='int', default=0,
                    help='Number of times to repeat failed tests.')
  parser.add_option('--failed', action='store_true', default=False,
                    help='run only failed and new tests')
  parser.add_option('-w', '--workers', type='int',
                    default=multiprocessing.cpu_count(),
                    help='number of workers to spawn')
  parser.add_option('--gtest_color', type='string', default='yes',
                    help='color output')
  parser.add_option('--gtest_filter', type='string', default='',
                    help='test filter')
  parser.add_option('--test', type='string', default='',
                    help='select a specific test or tests to run')
  parser.add_option('--size', type='string', default='', 
                    help='select a test size (S, M, L, XL, *) to run')
  parser.add_option('--gtest_also_run_disabled_tests', action='store_true',
                    default=False, help='run disabled tests too')
  parser.add_option('--print_test_times', action='store_true', default=False,
                    help='list the run time of each test at the end of execution')
  parser.add_option('--shard_count', type='int', default=1,
                    help='total number of shards (for sharding test execution '
                         'between multiple machines)')
  parser.add_option('--shard_index', type='int', default=0,
                    help='zero-indexed number identifying this shard (for '
                         'sharding test execution between multiple machines)')
  parser.add_option('--dump_xml_test_results', type='string', default=None,
                    help='Saves the results of the tests as an XML machine-'
                         'readable file. The format of the file is specified at '
                         'https://github.com/google/googletest/blob/1b18723e874b256c1e39378c6774a90701d70f7a/docs/advanced.md#generating-an-xml-report')
  parser.add_option('--timeout', type='int', default=None,
                    help='Interrupt all remaining processes after the given '
                         'time (in seconds).')
  parser.add_option('--serialize_test_cases', action='store_true',
                    default=False, help='Do not run tests from the same test '
                                        'case in parallel.')
  return parser


def main():
  # Remove additional arguments (anything after --).
  additional_args = []

  for i in range(len(sys.argv)):
    if sys.argv[i] == '--':
      additional_args = sys.argv[i+1:]
      sys.argv = sys.argv[:i]
      break

  parser = default_options_parser()
  (options, binaries) = parser.parse_args()

  if (options.output_dir is not None and
      not os.path.isdir(options.output_dir)):
    parser.error('--output_dir value must be an existing directory, '
                 'current value is "%s"' % options.output_dir)

  # Append gtest-parallel-logs to log output, this is to avoid deleting user
  # data if an user passes a directory where files are already present. If a
  # user specifies --output_dir=Docs/, we'll create Docs/gtest-parallel-logs
  # and clean that directory out on startup, instead of nuking Docs/.
  if options.output_dir:
    options.output_dir = os.path.join(options.output_dir,
                                      'gtest-parallel-logs')

  if binaries == []:
    parser.print_usage()
    sys.exit(1)

  if options.shard_count < 1:
    parser.error("Invalid number of shards: %d. Must be at least 1." %
                 options.shard_count)
  if not (0 <= options.shard_index < options.shard_count):
    parser.error("Invalid shard index: %d. Must be between 0 and %d "
                 "(less than the number of shards)." %
                 (options.shard_index, options.shard_count - 1))

  # Check that all test binaries have an unique basename. That way we can ensure
  # the logs are saved to unique files even when two different binaries have
  # common tests.
  unique_binaries = set(os.path.basename(binary) for binary in binaries)
  assert len(unique_binaries) == len(binaries), (
      "All test binaries must have an unique basename.")

  if options.output_dir:
    # Remove files from old test runs.
    if os.path.isdir(options.output_dir):
      shutil.rmtree(options.output_dir)
    # Create directory for test log output.
    try:
      os.makedirs(options.output_dir)
    except OSError as e:
      # Ignore errors if this directory already exists.
      if e.errno != errno.EEXIST or not os.path.isdir(options.output_dir):
        raise e

  timeout = None
  if options.timeout is not None:
    timeout = threading.Timer(options.timeout, sigint_handler.interrupt)

  xml_logger = None
  if options.dump_xml_test_results is not None:
    xml_logger = XMLLogger(options.dump_xml_test_results)

  save_file = get_save_file_path()

  times = TestTimes(save_file)
  logger = FilterFormat(options.output_dir)

  task_manager = TaskManager(times, logger, xml_logger, Task, options.output_dir,
                             options.retry_failed, options.repeat + 1)

  tasks = find_tests(binaries, additional_args, options, times)
  logger.log_tasks(len(tasks))
  execute_tasks(tasks, options.workers, task_manager,
                timeout, options.serialize_test_cases)

  print_try_number = options.retry_failed > 0 or options.repeat > 1
  if task_manager.passed:
    logger.move_to('passed', task_manager.passed)
    if options.print_test_times:
      logger.print_tests('PASSED TESTS', task_manager.passed, print_try_number)

  if task_manager.failed:
    logger.print_tests('FAILED TESTS', task_manager.failed, print_try_number)
    logger.move_to('failed', task_manager.failed)

  if task_manager.started:
    logger.print_tests(
        'INTERRUPTED TESTS', task_manager.started.values(), print_try_number)
    logger.move_to('interrupted', task_manager.started.values())

  if options.repeat > 1 and (task_manager.failed or task_manager.started):
    logger.summarize(task_manager.passed, task_manager.failed,
                     task_manager.started.values())

  logger.flush()
  times.write_to_file(save_file)
  if xml_logger:
    xml_logger.dump_to_file_and_close()

  if sigint_handler.got_sigint():
    return -signal.SIGINT

  return task_manager.global_exit_code

if __name__ == "__main__":
  sys.exit(main())
