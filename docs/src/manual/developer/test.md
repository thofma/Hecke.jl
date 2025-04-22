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
  corresponding a test should be added to the corresponding test file. In this
  case this would be `test/QuadForm/Quad/Genus.jl`.
- Assume one adds a new file, say `src/QuadForm/New.jl`, which is included in
  `src/QuadForm.jl`. Then a corresponding file `test/QuadForm/Test.jl`
  containing the tests must be added. This new file must then also be included
  in `test/QuadForm.jl`.
- Similar to the above, if a new directory in `src/` is added, the same must apply
  in `test/`.

### Adding long tests

If one knows that running a particular test will take a long time, one can use
`@long_test` instead of `@test` inside the test suite. When running the test
suite, tests annotated with `@long_test` will not be run, unless specifically
asked for (see below). The continuous integration servers will run at least one
job including the long tests.

## Running the tests

### Running all tests

All tests can be run as usual with `Pkg.test("Hecke")`. The whole test suite can be run in parallel using the following options:
- Set the environment variable `HECKE_TEST_VARIABLE=n`, where `n` is the number of processes.
- On julia >= 1.3, run `Pkg.test("Hecke", test_args = ["-j$(n)"])`, where `n` is the number of processes.
The tests annotated with `@long_test` can be invoked by setting `HECKE_TESTLONG=1` or adding "long" to the `test_args` keyword argument on julia >= 1.3.

### Running a subset of tests

Because the test structure mirrors the source directory, it is easy to run only a subset of tests. For example, to run all the tests in `test/QuadForm/Quad/Genus.jl`, one can invoke:

```julia
julia> Hecke.test_module("QuadForm/Quad/Genus")
```

This also works on the directory level. If one wants to add run all tests for quadratic forms, one can just run

```julia
julia> Hecke.test_module("QuadForm")
```
