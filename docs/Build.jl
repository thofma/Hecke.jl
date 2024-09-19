#
# This file is included by docs/make.jl and by a helper function
# in src/Hecke.jl
#
module Build

using Pkg, Nemo, Documenter, DocumenterVitepress, DocumenterCitations

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
          "Elliptic curves" => [ "elliptic_curves/intro.md",
                                 "elliptic_curves/basics.md",
                                 "elliptic_curves/finite_fields.md",
                                 "elliptic_curves/number_fields.md",],
          "Abelian groups" => "abelian/introduction.md",
          "Class field theory" => "class_fields/intro.md",
          "Misc" =>  ["FacElem.md",
                      "sparse/intro.md",
                      "pmat/introduction.md",
                      "misc/conjugacy.md",
                      ],
          "Extra features" => ["features/mset.md",
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
#Documenter.print_signature(io::IO, signature)        = print(io, signature)

# To remove the "Method", "Type", "Module" use the following
#Documenter.doccat(b::Base.Docs.Binding, ::Type)  = ""
#Documenter.doccat(::Type)     = ""
#Documenter.doccat(::Module)   = ""

# Remove the module prefix
Base.print(io::IO, b::Base.Docs.Binding) = print(io, b.var)

# the .id in the anchor is derived from the signature, which sometimes contain "<:"
# it seems mkdocs does not handle "<:" that well inside an <a href="...">.
# function Base.getproperty(obj::Documenter.Anchors.Anchor, sym::Symbol)
#   if sym === :id
#     return replace(getfield(obj, sym), "<:" => "")
#   else
#     return getfield(obj, sym)
#   end
# end

status = sprint(io -> Pkg.status("Nemo"; io = io))
version = match(r"(v[0-9].[0-9]+.[0-9]+)", status)[1]
gh_moi = Documenter.Remotes.GitHub("nemocas", "Nemo.jl")
remotes = Dict(pkgdir(Nemo) => (gh_moi, version))

function make(Hecke::Module; strict = false,
                             local_build::Bool = false,
                             doctest = true,
                             format::Symbol = :vitepress,
                             warnonly = false)

  # Load the bibliography
  bib = CitationBibliography(joinpath(Hecke.pkgdir, "docs", "src", "Hecke.bib"))

  @info "Using bibliography: $(bib)"

  cd(joinpath(Hecke.pkgdir, "docs")) do
    DocMeta.setdocmeta!(Hecke, :DocTestSetup, :(using Hecke); recursive = true)
    DocMeta.setdocmeta!(Hecke.Nemo, :DocTestSetup, :(using Hecke.Nemo); recursive = true)

    if format == :html
      makedocs(
        modules = [Hecke, Hecke.Nemo],
        authors="Claus Fieker and Tommy Hofmann",
        repo="https://github.com/thofma/Hecke.jl",
        sitename="Hecke",
        checkdocs = :none,
        format = Documenter.HTML(prettyurls = !local_build, collapselevel = 1),
        warnonly = warnonly,
        plugins=[bib],
        doctest = doctest,
        remotes = remotes,
      )
    elseif format == :vitepress
    makedocs(
      modules = [Hecke, Hecke.Nemo],
      authors="Claus Fieker and Tommy Hofmann",
      repo="https://github.com/thofma/Hecke.jl",
      sitename="Hecke",
      checkdocs = :none,
      remotes = remotes,
      format=DocumenterVitepress.MarkdownVitepress(
          repo = "github.com/thofma/Hecke.jl",
          devurl = "dev",
          devbranch = "master",
          #deploy_url = "https://thofma.com/Hecke.jl",
          #build_vitepress = !local_build,
         ),
      warnonly = warnonly,
      plugins=[bib],
      doctest= doctest,
      )
    end
  end
end

end # module Build

using .Build
