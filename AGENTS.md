# Information for AI agents

Hecke is a Julia package for algebraic number theory, built on Nemo and
AbstractAlgebra and developed as part of the OSCAR project.

These instructions apply to both Codex and Claude Code. `CLAUDE.md` imports
this file so that the repository guidance is maintained in one place.

## Module Organization

- `src/` - Main Julia sources, organized by mathematical area, for example
  `NumField/`, `NumFieldOrd/`, `QuadForm/`, `AlgAss/`, and `LocalField/`.
  The core package uses a single flat `module Hecke` in `src/Hecke.jl`,
  without submodules.
- `src/Foo.jl` typically includes the files in `src/Foo/`. Type definitions
  usually live in `src/Foo/Types.jl`.
- `src/exports.jl` - Hecke's public exports. Add exports here, never in
  individual source files.
- `test/` - Julia test suite. The directory layout mirrors `src/`;
  `test/Foo.jl` includes tests from `test/Foo/`, wrapped in `@testset`.
- `docs/` - Documentation built with Documenter, DocumenterVitepress, and
  DocumenterCitations. Developer documentation is under
  `docs/src/manual/developer/`.
- `ext/` - Extensions for the optional GAP and Polymake dependencies.
- `examples/` and `benchmark/` - Example scripts and benchmarks.
- `etc/` - Auxiliary developer and maintenance scripts.
- `Project.toml` - Package dependencies and compatibility requirements,
  including the supported Julia versions.

## For all changes

- For commits containing changes made with generative AI assistance, add
  `Assisted-by: Generative AI` as a trailer in the commit message.
- Whenever a pull request contains changes made with the assistance of
  generative AI, include `Assisted-by: Generative AI` in the PR description.

## Specific instructions for particular changes

### Writing code

- Read nearby implementations and tests before editing.
- Use established Nemo and AbstractAlgebra APIs instead of reinventing
  functionality.
- Preserve documented mathematical behavior and avoid unnecessary API
  changes.

Honor the formatting and naming conventions in `CONTRIBUTING.md`:

- Use 2-space indentation, no tabs, and no trailing whitespace.
- Aim for an 80-character line length and use spaces after commas.
- Do not introduce Unicode in source code.
- Use `lower_case_with_underscores` for functions and `UpperCamelCase`
  for types.

After writing code, look up the docstring for each function you used. Take
any recommendations or additional considerations into account.

Use the existing macros where appropriate:

| Macro | Purpose |
| --- | --- |
| `@req cond "msg"` | Precondition check from AbstractAlgebra |
| `@hassert :Scope level expr` | Leveled assertion |
| `@attr Type expr` | Cached or lazy attribute on a type |
| `@vprintln :Scope level "msg"` | Verbose debug printing |
| `@show_name`, `@show_special` | Custom `show` methods |

### Mathematical correctness

- For mathematical algorithms, cite the reference and document the
  hypotheses and conventions used.
- Preserve the mathematical invariants and documented guarantees of the
  affected operations, including parent compatibility, normalization,
  exactness, and precision bounds where relevant.
- Verify the hypotheses behind algorithms and simplifications before using
  or modifying them. Make assumptions about the base ring or field,
  characteristic, separability, rank, or invertibility explicit where they
  matter.
- Test mathematical properties and nontrivial edge cases in addition to
  representative examples. Depending on the affected code, consider zero
  and unit inputs, singular or degenerate objects, ramified primes, and
  small characteristics. Where practical, verify defining identities and
  invariants or compare results with an independent method.

### Test changes

Review `docs/src/manual/developer/test.md` before changing tests.

- Add regression tests, including mathematical edge cases, to the
  corresponding existing test file. Do not create a new test file for a
  change to an existing source file unless explicitly instructed.
- When adding source files, follow the documented matching test hierarchy
  and include the new test files in the appropriate test entry point.
- Write one comment at the top of the test to explain what is being tested.
  Otherwise keep comments minimal.
- Tests use Julia's standard library `Test` (`@testset`, `@test`).
- Use `@long_test` for expensive tests. These tests are skipped unless long
  tests are enabled.
- A `setup_tests.jl` in a test file's directory is loaded automatically by
  the test helpers. Setup files in parent directories are ignored.

Run targeted tests for the affected files or modules after code or test
changes, before attempting expensive full-suite testing. From the repository
root:

- Run one test file:
  `julia --project=. -e 'using Hecke; Hecke.test_module("QuadForm/Quad/Genus")'`.
- Run one module:
  `julia --project=. -e 'using Hecke; Hecke.test_module("QuadForm")'`.
- Select tests corresponding to changed source files:
  `julia --project=. -e 'using Hecke; Hecke.test_changes()'`.
- Run all tests:
  `julia --project=. -e 'using Pkg; Pkg.test("Hecke")'`.

`Hecke.test_module` spawns a fresh Julia session by default and loads
`test/setup.jl`. Pass `long=true`, `with_gap=true`, or `with_polymake=true`
when the selected tests require them.

For the full test runner, `HECKE_TESTLONG=1` enables long tests and
`NUMPROCS=N` selects the number of worker processes. `HECKE_TESTSHORT=1`
runs only the short checks (Aqua and precompilation); it does not exercise
the full mathematical test suite.

### Documentation and docstrings

Review `docs/src/manual/developer/documentation.md` before changing the
documentation. Use `@doc raw"""` for docstrings, with an indented function
signature as the first line of the contents, followed by a blank line and
the description.

Build the documentation locally with:
`julia --project=. -e 'using Hecke; Hecke.build_doc()'`.
To build or preview the resulting Vitepress site, run `npm run docs:build`
or `npm run docs:dev` from `docs/`. Register new manual pages in
`docs/src/.vitepress/config.mts`.

### Doctests

Before writing or changing `jldoctest` blocks, review
`docs/src/manual/developer/documentation.md` and nearby examples. Check
whether the doctests need labels, filters, or setup code. Use
`Hecke.doctestsetup()` for Hecke's printing and module setup, as in the
existing documentation.

For EVERY change to a `jldoctest` block, run the documentation build with
doctests explicitly enabled:

```sh
julia --project=. -e 'using Hecke; Hecke.build_doc(; doctest=true)'
```

Both `Hecke.build_doc()` and `docs/make.jl` disable doctests by default.
The full test suite runs docstring doctests only on Julia 1.10, so it is
not a substitute for checking changed manual examples with the command
above. Doctests can take many minutes. Let them finish; do not terminate
them early or impose a timeout.

## Commit Messages and Pull Requests

### Commit messages

Use the format `<type>(<scope>): <description>`, where the scope is optional.

Preferred prefixes:

- `fix`: Bug fixes
- `enh`: New or extended functionality
- `opt`: Performance improvements
- `ref`: Internal refactoring
- `rename`: Renamings
- `docs`: Documentation
- `test`: Tests
- `chore`: Maintenance
- `ci`: CI changes
- `build`: Build and dependency changes
- `revert`: Reverts

Examples:

```text
fix: handle empty input correctly
fix(function fields): correct evaluation of constants
enh(number fields): support additional extensions
opt: reduce allocations in matrix operations
```

Use imperative mood, lowercase descriptions (except proper names), and no
trailing period. Scopes should identify the affected area when useful.
Spaces are allowed; no mandatory hyphenation or naming convention for scopes.

In the commit body, give a brief prose summary of the purpose of the
changes. Do not specifically mention added tests, comments, or documentation
unless that is the main purpose of the change. Do not mention the test plan
unless it differs from these instructions. If the change fixes issues, put
`Fixes #123` at the end of the body, never in the title.

Use GitHub interlinking syntax such as `owner/repo#123` for external issues
and pull requests.

Never include links to CI failures in commit messages or PR descriptions.
Describe the final change and relevant validation, omitting intermediate
development failures and corrections.

### Pull request titles

PR titles must be descriptive, human-readable, and suitable for inclusion
verbatim in the changelog.

- Use sentence case and imperative mood.
- Do not use commit prefixes (`fix:`, `enh:`, etc.).
- Do not require topic or area prefixes.
- Mention the affected area naturally when it improves clarity.
- Avoid trailing periods.

Examples:

```text
Correct evaluation of constant elements
Support additional function field extensions
Improve performance of class group computations
```

### Pull request labels

The changelog is organized using PR labels, not commit prefixes or PR title
prefixes.

- **Topic:** Use the appropriate existing label, e.g. `topic: function fields`,
  `topic: number fields`, `topic: algebras`.
- **Change type:** Use one primary label: `bug`, `enhancement`, `optimization`,
  `renaming`, `documentation`, or `experimental`.
- **Experimental:** Use the `experimental` PR label for experimental
  functionality, rather than a special commit prefix.
- **Release notes:** Use `release notes: use title` to include the PR title
  verbatim, or `release notes: not needed` to exclude it.
- Use `release notes: highlight` for noteworthy changes and `breaking` for
  compatibility-breaking changes.
- `release notes: added` means the entry has already been processed; it does
  not indicate new functionality.

For changelog-relevant PRs, choose one primary topic and one change type.
Internal refactoring, tests, CI, and routine maintenance normally do not need
a changelog entry.

Commit scopes and PR topic labels are independent and need not match.

### Opening pull requests

1. For a single-commit PR, use the commit body as the PR description.
2. For multiple commits, follow the same guidelines as for a commit body.
3. Ensure the base commit is recent (within the past two days); rebase the
   changes first if necessary.
4. Include the AI assistance disclosure required above.

### Squash merges

When squash-merging, retain the commit convention rather than copying the PR
title unchanged.

PR title:

```text
Correct evaluation of constant elements
```

Squash commit:

```text
fix(function fields): correct evaluation of constant elements (#123)
```
