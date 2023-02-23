# Macros
```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```

We describe here various macros provided by Hecke.

## Verbose macros
There is a list of symbols called *verbosity scopes* which represent keywords used to
trigger some particular macros within the codes. Each of these verbose scopes is 
associated with a *verbosity level*, being set to $0$ by default. A verbose macro
is joined to a verbose scope `S` and a value `k` (set to $1$ by default) such that,
if the current verbose level `l` of `S` is bigger than or equal to `k`, then the
macro triggers a given action.

```@docs
add_verbose_scope(s::Symbol)
set_verbose_level(s::Symbol, l::Int)
get_verbose_level(s::Symbol)
```

### Printings

```@docs
@vprint
```

### Actions

```@docs
@v_do
```

## Assert macros
There is a list of symbols called *assertion scopes* which represent keywords used to
trigger some particular macros within the codes. Each of these assertion scopes is
associated with an *assertion level*, being set to $0$ by default. An assert macro
is joined to an assertion scope `S` and a value `k` (set to $1$ by default) such that,
if the current assertion level `l` of `S` is bigger than or equal to `k`, then the
macro triggers an action on the given assertion

```@docs
add_assert_scope(s::Symbol)
set_assert_level(s::Symbol, l::Int)
get_assert_level(s::Symbol)
```

### Check

```@docs
@hassert
```

## Miscellaneous

```@docs
@req
```
