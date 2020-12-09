from conans import ConanFile


class GTestParallelConan(ConanFile):
    name = "gtest-parallel"
    version = "11cce5c2872be4849c087afc7d19fbed390fa928" # commit hash
    url = "https://github.com/Esri/gtest-parallel/tree/runtimecore"
    license = "https://github.com/Esri/gtest-parallel/blob/runtimecore/LICENSE"
    description = (
        "gtest-parallel is a script that executes Google Test binaries in parallel"
    )

    # Use the OS default to get the right line endings
    settings = "os"

    def package(self):
        base = self.source_folder + "/"
        relative = "3rdparty/gtest-parallel/"

        # transfer scripts 
        self.copy("gtest-parallel", src=base, dst=relative)
        self.copy("gtest_parallel.py", src=base, dst=relative)

    def package_id(self):
        self.info.header_only()
