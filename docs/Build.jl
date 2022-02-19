#
# This file is included by docs/make.jl and by a helper function
# in src/Hecke.jl
#
module Build

using Documenter, DocumenterMarkdown, DocumenterCitations

pages = [
         "index.md",
         "Number fields" => [ "number_fields/intro.md",
                              "number_fields/fields.md",
                              "number_fields/elements.md",
                              "number_fields/complex_embeddings.md",
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
         "abelian/introduction.md",
         "class_fields/intro.md",
         "Misc" =>  ["FacElem.md",
                     "sparse/intro.md",
                     "pmat/introduction.md",
                     "misc/conjugacy.md",
                     ],
         "examples.md",
         "Developer" => [ "dev/test.md",
                        ]
        ]

# Overwrite printing to make the header not full of redundant nonsense
# Turns
#   Hecke.Order - Method
# into
#   Order - Method

# To remove the '-'
# Documenter.Utilities.print_signature(io::IO, signature)        = print(io, signature)

# To remove the "Method", "Type", "Module" use the following
# Documenter.Utilities.doccat(b::Base.Docs.Binding, ::Type)  = ""
# doccat(::Type)     = ""
# doccat(::Module)   = ""

# Remove the module prefix
Base.print(io::IO, b::Base.Docs.Binding) = print(io, b.var)

function make(Hecke::Module; strict::Bool = false,
                             local_build::Bool = false,
                             doctest::Bool = true,
                             format::Symbol = :mkdocs)

  # Load the bibliography
  bib = CitationBibliography(joinpath(Hecke.pkgdir, "docs", "src", "Hecke.bib"), sorting = :nyt)

  cd(joinpath(Hecke.pkgdir, "docs")) do
    DocMeta.setdocmeta!(Hecke, :DocTestSetup, :(using Hecke); recursive = true)

    if format == :html
      makedocs(
        bib,
        format = Documenter.HTML(prettyurls = !local_build, collapselevel = 1),
        doctest = doctest,
        strict = strict,
        modules = [Hecke],
        sitename = "Hecke documentation",
        pages = pages
      )
    elseif format == :mkdocs
      makedocs(
          bib,
          doctest= doctest,
          strict = strict,
          modules = [Hecke],
          format = Markdown(),
      )
    end
  end
end

end # module Build

using .Build
