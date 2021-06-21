using Documenter, DocumenterMarkdown, Hecke, Nemo, AbstractAlgebra, Pkg

DocMeta.setdocmeta!(Hecke, :DocTestSetup, :(using Hecke); recursive = true)

if Hecke.html_build[]
  makedocs(
      format = Documenter.HTML(prettyurls = !local_build),
      doctest= true,
      modules = [Hecke],
      sitename = "Hecke documentation",
      pages = [
      "index.md",
      "Number fields" => [ "number_fields/intro.md",
                            "number_fields/basics.md",
                           "number_fields/elements.md",
                           "number_fields/internal.md"],
      "Function fields" => [ "function_fields/intro.md",
			     "function_fields/basics.md",
			     "function_fields/elements.md",
			     "function_fields/internal.md",
			     "function_fields/degree_localization.md"],
      "Orders" => [ "orders/introduction.md",
                    "orders/orders.md",
                    "orders/elements.md",
                    "orders/ideals.md",
                    "orders/frac_ideals.md"
                  ],
#      "Maximal Orders" => [ "MaximalOrders/Introduction.md",
#                            "MaximalOrders/Creation.md",
#                            "MaximalOrders/Elements.md",
#                            "MaximalOrders/Ideals.md"
#                          ],
      "abelian/introduction.md",
      "class_fields/intro.md",
      "sparse/intro.md",
      "FacElem.md"
      ]

  )
else
  makedocs(
      doctest= true,
      modules = [Hecke],
      format = Markdown(),
  )

  docsdir = joinpath(@__DIR__, "build/")

  function _super_cool_example(f, overwrite = true)
    inside = false
    new_file = ""
    collapsing = false
    open(f) do file
      for ln in eachline(file);
        if startswith(ln, "<a id='Example")
          continue
        end
        if startswith(ln, "#### Example")
          if startswith(ln, "#### Example +")
            collapsing = true
          end
          ln = ""
          inside = true
        end
        if inside
          if startswith(ln, "```julia-repl")
            if collapsing
              line = "??? note \"Example\"\n    ```julia"
              collapsing = false
            else
              line = "!!! note \"Example\"\n    ```julia"
            end
          else
            line = "    " * ln
          end
        else
          line = ln;
        end

        if startswith(ln, "```") && !occursin("julia-repl", ln)
          inside = false
        end
        new_file = new_file * "\n" * line
      end
    end
    rm(f)
    open(f, "w") do file
      write(file, new_file)
    end
  end

  for (root, dirs, files) in walkdir(docsdir)
    for file in files
      filename = joinpath(root, file) # path to files
      run(`sed -i 's/.*dash; \*Method.*/---/g' $filename`)
      run(`sed -i 's/.*dash; \*Type.*/---/g' $filename`)
      run(`sed -i 's/.*dash; \*Function.*/---/g' $filename`)
      run(`sed -i '/>source<\/a>/d' $filename`)
      run(`sed -i '/>\#<\/a>/d' $filename`)
      _super_cool_example(filename)
    end
  end
end

deploydocs(
  repo = "github.com/thofma/Hecke.jl.git",
  deps = Deps.pip("pymdown-extensions", "pygments", "mkdocs", "python-markdown-math", "mkdocs-material", "mkdocs-cinder"),
  target = "site",
  make = () -> run(`mkdocs build`),
)

#makedocs(
#    modules = [Hecke, Nemo, AbstractAlgebra],
#    clean   = true,
#    format = :html,
#    sitename = "Hecke",
#    doctest = !false,
#)
#
## Hack around to get syntax highlighting working
##cd(joinpath(dirname(pathof(Hecke)), "..", "docs"))
##
##cp("application-f78e5cb881.palette.css", "build/application-f78e5cb881.palette.css", force = true)
##cp("application-e2807e330f.css", "build/application-e2807e330f.css", force = true)
#
#deploydocs(
#     deps = nothing,
##    deps = Deps.pip()#="pygments",
##                    "mkdocs==0.16.3",
##                    "python-markdown-math",
##                    "mkdocs-cinder")=#,
#    repo = "github.com/thofma/Hecke.jl.git",
#    target = "build",
#    make = nothing,
#    osname = "linux",
#    julia = "1.0",
#)
#
## Try out the following deps = Deps.pip("mkdocs==0.17.5", "mkdocs-material==2.9.4" ,"python-markdown-math", "pygments", "pymdown-extensions")
