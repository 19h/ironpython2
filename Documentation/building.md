# Building IronPython 2

The build requires the .NET 10 SDK. Linux and macOS builds also require [Mono](https://mono-project.com) for `mcs`, `vbc`, and `ilasm`, plus [PowerShell](https://github.com/PowerShell/PowerShell/releases).

See [Getting the Sources](getting-the-sources.md) for information on getting the source for IronPython2.

## Building from Visual Studio

Visual Studio 16.4(2019) or above is required to build IronPython2

 * Open `c:\path\to\ironpython2\IronPython.sln` solution file
 * Select the configuration options (Release,Debug, etc)
 * Press Ctrl+Shift+B or F6 to build the solution

## Building from the command line

IronPython2 uses PowerShell to run the build and testing from the command line. You can either use a PowerShell directly, or prefix the commands below with `powershell` on Windows, or `pwsh` on Linux/macOS. 

On macOS, the required ARM64 or x64 tools can be installed with Homebrew:

```sh
brew install dotnet mono powershell
git submodule update --init
```

The Mono compiler and assembler commands must be discoverable through `PATH`.

Change the working directory to the path where you cloned the sources and run `.\make.ps1` on Windows or `./make.ps1` on Linux/macOS.

By default, with no options, make.ps1 will build Release mode binaries. If you would like to build debug binaries, you can run `.\make.ps1 debug`

Other options available for `make.ps1` are

```
-configuration (debug/release)   The configuration to build for
-platform (x86/x64/Arm64)        The platform to use in running tests; detected automatically
-runIgnored                      Run tests that are marked as ignored in the .ini manifests
-frameworks                      A comma separated list of frameworks to run tests for 
                                 (use nomenclature as is used in msbuild files for TargetFrameworks)
```

There are also other targets available for use with packaging and testing, most come in debug and release (default) versions, such as `package-debug` and `package`

```
package                         Creates packages supported by the current platform
stage                           Stages files ready for packaging
test-*                          Runs tests from `all` categories, `ironpython` specific tests, 
                                `cpython` tests from the C Python stdlib test suite, `smoke` a small
                                set of tests
```

If the build is successful, binaries are stored in `ironpython2/bin/{ConfigurationName}/{Framework}`. The macOS launcher is `bin/Release/net10.0/ipy`.

For a release build, smoke test, and distribution containing the complete Python standard library:

```sh
./make.ps1 clean
./make.ps1 release
./make.ps1 test-smoke
./make.ps1 stage
Package/Release/Stage/IronPython-*/net10.0/ipy -c 'import sys; print(sys.version)'
```
