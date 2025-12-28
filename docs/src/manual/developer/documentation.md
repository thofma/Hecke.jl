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

2. Exit julia and, in the terminal, navigate to the `docs/` directory and run
   ```bash
   .../Hecke/docs$ npm run docs:build
   ```

3. You should now be able to view the documentation on a local server by running
   ```bash
   .../Hecke/docs$ npm run docs:preview
   ```

!!! tip "Recommended Workflow"
    Open a **separate terminal window** and run:
    ```bash
    .../Hecke/docs$ npm run docs:dev
    ```
    This keeps a live server running in the background. You can then keep your Julia session open (from Step 1) and re-run `Hecke.build_doc()` whenever you update the documentation. The server will automatically update with your changes.
