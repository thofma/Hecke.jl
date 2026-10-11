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
  `src/QuadForm.jl`. Then a corresponding file `test/QuadForm/New.jl`
  containing the tests must be added. This new file must then also be included
  in `test/QuadForm.jl`.
- Similar to the above, if a new directory in `src/` is added, the same must apply
  in `test/`.

### Adding long tests

Keep long tests in the same files as the related ordinary tests. Mark expensive
testsets, loops, or blocks with `@long_test`:

```julia
@long_test @testset "Expensive examples" begin
  # Expensive setup and tests go here.
end
```

The entire marked expression is skipped unless long tests are enabled. Include
expensive setup in the block, rather than marking only the final assertion.
For tests that extend an ordinary range, the marker can enable additional cases
while keeping a single loop body:

```julia
determinants = 1:3
@long_test determinants = 1:10
for d in determinants
  # Test the case with determinant d.
end
```

Long-only mode scans leaf test files for the `@long_test` token and runs the
matching files with long tests enabled. It runs each selected file completely,
including its ordinary tests and shared setup. Mark the leaf files themselves,
since directory wrappers are replaced by their individual test files. The scan
matches source text, so markers in comments or strings also select a file.

Tests requiring GAP or Polymake can be ordinary or long. Keep ordinary
extension tests in the ordinary files, guarded by `@with_gap` or
`@with_polymake` as appropriate. CI loads both packages in the regular Linux
Julia 1.10 job and in the separate long-only job.

## Running the tests

### Running all tests

Run the ordinary suite with `Pkg.test("Hecke")`. Enable long tests throughout
the suite, or run only files containing long tests, using:

```julia
Pkg.test("Hecke"; test_args = ["long"])      # ordinary and long tests
Pkg.test("Hecke"; test_args = ["long-only"]) # files containing @long_test
```

The corresponding environment variables are `HECKE_TESTLONG=1` and
`HECKE_TESTLONGONLY=1`. Long-only mode skips unmarked files, Aqua, and doctests;
ordinary tests in marked files still run.
The whole test suite can be run in parallel using the following options:

- Set the environment variable `NUMPROCS=n`, where `n` is the number of worker processes.
- Run `Pkg.test("Hecke"; test_args = ["-j$(n)"])`, where `n` is the number of worker processes. This can be combined with `"long"` or `"long-only"`.

The package test runner detects GAP and Polymake when they are available in the
test environment or the default Julia environment. Jobs that require both set
`HECKE_REQUIRE_TEST_EXTENSIONS=1`; this makes a missing package or extension an
error instead of skipping its tests.

### Running a subset of tests

Because the test structure mirrors the source directory, it is easy to run only a subset of tests. For example, to run all the tests in `test/QuadForm/Quad/Genus.jl`, one can invoke:

```julia
julia> Hecke.test_module("QuadForm/Quad/Genus")
```

Enable long blocks in the selected file, or filter the selection to files
containing long tests:

```julia
julia> Hecke.test_module("QuadForm/Quad/Genus"; long = true)

julia> Hecke.test_module("QuadForm/Quad/Genus"; long_only = true)
```

This also works on the directory level. If one wants to add run all tests for quadratic forms, one can just run

```julia
julia> Hecke.test_module("QuadForm")
```

The `long` and `long_only` keywords also apply to directory selections. For
example, `Hecke.test_module("QuadForm"; long_only = true)` selects only the
files containing `@long_test` below that directory. A selection without marked
files runs no tests in long-only mode. The same filtering applies to lists of
files and `Hecke.test_module("all"; long_only = true)`.

Several test files can be run in the same Julia session by passing a list:

```julia
julia> Hecke.test_module(["Misc/Integer", "Misc/MSet"])
```

By default, `test_module` starts a fresh Julia session. Pass `false` as the
second argument to run in the current session. File names may include the
`.jl` suffix. The `with_gap` and `with_polymake` keywords load optional packages
and enable their tests independently of the long-test selection:

```julia
julia> Hecke.test_module("ModAlgAss/Lattices/Absolute"; with_gap = true)

julia> Hecke.test_module("AlgAssRelOrd/Eichler"; with_polymake = true)

julia> Hecke.test_module("FieldFactory"; long_only = true, with_gap = true)
```

When Hecke is loaded from a Git working tree, the tests corresponding to all
changed source files can be selected and run with:

```julia
julia> Hecke.test_changes()
```

This reports all changed files in `src/` first. For each changed source file it
runs the test file at the matching path, or the test file for the containing
source directory when there is no matching file.
It accepts the same keywords as `test_module`, including `long`, `long_only`,
`with_gap`, and `with_polymake`.
