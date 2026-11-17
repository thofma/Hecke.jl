```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Testing

## Structure

The Hecke tests can be found in `Hecke/test/` and are organized in such a way that the file hierarchy mirrors the source directory
`Hecke/src/`. For example, here is a subset of the `src/QuadForm` and the `test/QuadForm` directories:

```
├── src
│   ├── QuadForm
│   │   ├── Enumeration.jl
│   │   ├── Herm
│   │   │   ├── Genus.jl
│   │   ├── Quad
│   │   │   ├── Genus.jl
│   │   │   ├── GenusRep.jl
│   │   │   ├── NormalForm.jl
│   │   │   ├── Spaces.jl
│   │   │   ├── Types.jl
│   │   │   ├── ZGenus.jl
│   │   │   └── ZLattices.jl
│   │   ├── QuadBin.jl
│   │   ├── Torsion.jl
│   ├── QuadForm.jl
│
│
│
├── test
│   ├── QuadForm
│   │   ├── Enumeration.jl
│   │   ├── Herm
│   │   │   ├── Genus.jl
│   │   ├── Quad
│   │   │   ├── Genus.jl
│   │   │   ├── GenusRep.jl
│   │   │   ├── NormalForm.jl
│   │   │   ├── Spaces.jl
│   │   │   ├── ZGenus.jl
│   │   │   └── ZLattices.jl
│   │   ├── QuadBin.jl
│   │   └── Torsion.jl
│   ├── QuadForm.jl
```

### Adding tests

- If one adds functionality to a file, say `src/QuadForm/Quad/Genus.jl`, a
  test should be added to the corresponding test file. In this
  case this would be `test/QuadForm/Quad/Genus.jl`.
- Assume one adds a new file, say `src/QuadForm/New.jl`, which is included in
  `src/QuadForm.jl`. Then a corresponding file `test/QuadForm/New.jl`
  containing the tests must be added. This new file must then also be included
  in `test/QuadForm.jl`.
- Similar to the above, if a new directory in `src/` is added, the same must apply
  in `test/`.

When a test file has a matching directory, such as `test/AlgAssAbsOrd/PIP.jl`
and `test/AlgAssAbsOrd/PIP/`, the full test runner skips the file and runs the
files inside the directory as separate jobs. Use the skipped file as a wrapper
that includes its child test files. Put all test cases and assertions in the
child files, and shared helper code in `setup_tests.jl` as described below.
Tests written directly in the skipped file will not run in CI.
When creating a directory beside an existing test file, move all of that file's
test cases into child files.

For example, add unit group generator tests to
`test/AlgAssAbsOrd/PIP/unit_group_generators.jl` and include that file from
`test/AlgAssAbsOrd/PIP.jl`. Running the wrapper explicitly with
`Hecke.test_module("AlgAssAbsOrd/PIP")` still runs all of its included tests.

### Shared test setup

If a test directory contains a file `setup_tests.jl`, this file is included into
`Main` before each test file in that directory run by the test runner or
`Hecke.test_module`. It can be used to define common helper functions and
initialize test data. It is not run as a separate test.

Setup files in parent directories are ignored. The setup file is included again
for each test file, so definitions that should only be evaluated once must be
guarded, for example with `isdefined`.

For example, `setup_tests.jl` can define a helper function as follows:

```julia
if !isdefined(@__MODULE__, :test_parent)
  function test_parent(x, R)
    @test parent(x) === R
  end
end
```

Test files run this way do not need to include the setup file themselves. When
including test files manually, the caller is responsible for loading their
setup files.

### Adding long tests

If one knows that running a particular test will take a long time, one can use
`@long_test` instead of `@test` inside the test suite. When running the test
suite, tests annotated with `@long_test` will not be run, unless specifically
asked for (see below). The continuous integration servers will run at least one
job including the long tests.

## Running the tests

### Running all tests

All tests can be run as usual with `Pkg.test("Hecke")`. The whole test suite can be run in parallel using the following options:
- Set the environment variable `NUMPROCS=n`, where `n` is the number of worker processes.
- On julia >= 1.3, run `Pkg.test("Hecke", test_args = ["-j$(n)"])`, where `n` is the number of worker processes.
The tests annotated with `@long_test` can be invoked by setting `HECKE_TESTLONG=1` or adding "long" to the `test_args` keyword argument on julia >= 1.3.

### Running a subset of tests

Because the test structure mirrors the source directory, it is easy to run only a subset of tests. For example, to run all the tests in `test/QuadForm/Quad/Genus.jl`, one can invoke:

```julia
julia> Hecke.test_module("QuadForm/Quad/Genus")
```

This also works on the directory level. If one wants to run all tests for quadratic forms, one can just run

```julia
julia> Hecke.test_module("QuadForm")
```

Several test files can be run in the same Julia session by passing a list:

```julia
julia> Hecke.test_module(["Misc/Integer", "Misc/MSet"])
```

When Hecke is loaded from a Git working tree, the tests corresponding to all
changed source files can be selected and run with:

```julia
julia> Hecke.test_changes()
```

This reports all changed files in `src/` first. For each changed source file it
runs the test file at the matching path, or the test file for the containing
source directory when there is no matching file.
