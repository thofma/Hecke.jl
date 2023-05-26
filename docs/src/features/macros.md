# Macros
```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```

We describe here various macros provided by Hecke.

## Verbosity macros
There is a list of symbols called *verbosity scopes* which represent keywords used to
trigger some particular macros within the codes. Each of these verbosity scopes is 
associated with a *verbosity level*, being set to $0$ by default. A verbosity macro
is joined to a verbosity scope `S` and a value `k` (set to $1$ by default) such that,
if the current verbosity level `l` of `S` is bigger than or equal to `k`, then the
macro triggers a given action.

```@docs
add_verbosity_scope(s::Symbol)
set_verbosity_level(s::Symbol, l::Int)
get_verbosity_level(s::Symbol)
```

### Printings

```@docs
@vprintln
@vprint
```

### Actions

```@docs
@v_do
```

## Assertion macros
There is a list of symbols called *assertion scopes* which represent keywords used to
trigger some particular macros within the codes. Each of these assertion scopes is
associated with an *assertion level*, being set to $0$ by default. An assertion macro
is joined to an assertion scope `S` and a value `k` (set to $1$ by default) such that,
if the current assertion level `l` of `S` is bigger than or equal to `k`, then the
macro triggers an action on the given assertion

```@docs
add_assertion_scope(s::Symbol)
set_assertion_level(s::Symbol, l::Int)
get_assertion_level(s::Symbol)
```

### Check

```@docs
@hassert
```

## Miscellaneous

```@docs
@req
```
