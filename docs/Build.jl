#
# This file is included by docs/make.jl and by a helper function
# in src/Hecke.jl
#
module Build

using Pkg, Nemo, Documenter, DocumenterVitepress, DocumenterCitations

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
          deploy_url = "https://docs.hecke.thofma.com",
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
