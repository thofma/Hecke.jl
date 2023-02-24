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
	 "Quadratic and hermitian forms" => [ "quad_forms/introduction.md",
					      "quad_forms/basics.md",
					      "quad_forms/lattices.md",
					      "quad_forms/genusherm.md",
					      "quad_forms/integer_lattices.md",
					      "quad_forms/Zgenera.md",
					      "quad_forms/discriminant_group.md"
					    ],
         "Abelian groups" => "abelian/introduction.md",
         "Class field theory" => "class_fields/intro.md",
         "Misc" =>  ["FacElem.md",
                     "sparse/intro.md",
                     "pmat/introduction.md",
                     "misc/conjugacy.md",
                     ],
         "Extra features" => ["features/macros.md",
                             ],
         "Examples" => "examples.md",
         "References" => "references.md",
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

function make(Hecke::Module; strict = false,
                             local_build::Bool = false,
                             doctest::Bool = true,
                             format::Symbol = :mkdocs)

  # Load the bibliography
  bib = CitationBibliography(joinpath(Hecke.pkgdir, "docs", "src", "Hecke.bib"), sorting = :nyt)

  @info "Using bibliography: $(bib)"

  cd(joinpath(Hecke.pkgdir, "docs")) do
    DocMeta.setdocmeta!(Hecke, :DocTestSetup, :(using Hecke); recursive = true)

    if format == :html
      makedocs(
        bib,
        format = Documenter.HTML(prettyurls = !local_build, collapselevel = 1),
        doctest = doctest,
        strict = strict,
        modules = [Hecke, Hecke.Nemo],
        sitename = "Hecke documentation",
        pages = pages
      )
    elseif format == :mkdocs
      makedocs(
          bib,
          doctest= doctest,
          strict = strict,
          modules = [Hecke, Hecke.Nemo],
          format = Markdown(),
      )
    end
  end
end

end # module Build

using .Build
