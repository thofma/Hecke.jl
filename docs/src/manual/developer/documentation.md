```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Documentation

The files for the documentation are located in the
`docs/src/manual/` directory.

## Adding files to the documentation

To add files to the documentation edit directly the file
`docs/src/.vitepress/config.mts`.

## Building the documentation

1. Run julia and execute (with Hecke developed in your current environment)
```julia-repl
julia> using Hecke

julia> Hecke.build_doc() # or Hecke.build_doc(;doctest = false) to speed things up
```

2. In the terminal, navigate to `docs/` and run
```bash
Hecke/docs> npm run docs:build
```
(This step takes place outside of julia.)

!!! note
    To speed up the development process, step 1 can be repeated within the same julia session.
