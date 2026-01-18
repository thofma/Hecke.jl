```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Manual

This is the online manual for Hecke.jl. The material contained here is the primary reference for Hecke.jl's established user interface.

!!! warning
    This documentation is under construction. Some functions described in this documentation may not currently be exported
    by Hecke. To access these functions, one may need to refer to the module name explicitly:

    ```julia
    julia> using Hecke
    ...

    julia> K, a = quadratic_field(5)
    (Real quadratic field defined by x^2 - 5, sqrt(5))

    julia> unit_group_rank(K)
    ERROR: UndefVarError: `unit_group_rank` not defined in `Main`
    Suggestion: check for spelling errors or missing imports.
    Stacktrace:
     [1] top-level scope
       @ REPL[12]:1

    julia> Hecke.unit_group_rank(K)
    1
    ```
