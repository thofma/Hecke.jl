# Hecke.jl — Copilot Instructions

Hecke is a Julia package for algebraic number theory, part of the OSCAR project.
Built on top of `Nemo` and `AbstractAlgebra`.

## Project structure

- **Flat module**: single `module Hecke` in `src/Hecke.jl`, no submodules.
- **Dispatch files**: each `src/Foo.jl` includes files from `src/Foo/`. Types go in `src/Foo/Types.jl`.
- **Exports**: all exports live in `src/exports.jl` — never export from individual source files.
- **Tests mirror src**: `test/Foo.jl` includes `test/Foo/*.jl`, wrapped in `@testset`.

## Code style

- 2-space indentation, no tabs, no trailing whitespace, ~80-char lines.
- No Unicode in source code.
- `lower_case_with_underscores` for functions; `UpperCamelCase` for types.
- Spaces after commas.

## Common macros

| Macro | Purpose |
|---|---|
| `@req cond "msg"` | Precondition check (from AbstractAlgebra) |
| `@hassert :Scope level expr` | Leveled assertion |
| `@attr Type expr` | Cached/lazy attribute on a type |
| `@vprintln :Scope level "msg"` | Verbose debug printing |
| `@show_name`, `@show_special` | Custom `show` methods |

## Docstrings

Use `@doc raw"""` with the function signature on the first line:

```julia
@doc raw"""
    my_function(x::ZZLat) -> Int

Return the thing for `x`.
"""
function my_function(x::ZZLat)
  # ...
end
```

## Testing

- Framework: Julia stdlib `Test` (`@testset`, `@test`).
- Run all tests: `using Pkg; Pkg.test("Hecke")` or `Hecke.test_module("all")`.
- Run one module: `Hecke.test_module("QuadForm")` (runs `test/QuadForm.jl` in a subprocess).
- Helpers in `test/setup.jl`: `@long_test` (skipped unless `HECKE_TESTLONG=1`).
- Environment variables: `HECKE_TESTSHORT=1`, `HECKE_TESTLONG=1`, `HECKE_TEST_PARALLEL=N`.

## Documentation

- Built with **Documenter.jl** + **DocumenterVitepress** + **DocumenterCitations**.
- Build: `julia --project=docs docs/make.jl`.
- See [CONTRIBUTING.md](../CONTRIBUTING.md) for formatting guidelines.

## Key dependencies

- `AbstractAlgebra` — abstract algebra framework
- `Nemo` — number theory (wraps FLINT/Arb via `FLINT_jll`)
- Weak deps / extensions: `GAP`, `Polymake`
