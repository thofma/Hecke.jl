#
# This file is included by docs/make.jl and by a helper function
# in src/Hecke.jl
#
module Build

using Pkg, Nemo, Documenter, DocumenterVitepress, DocumenterCitations, Literate

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
    DocMeta.setdocmeta!(Hecke, :DocTestSetup, Hecke.doctestsetup(); recursive = true)
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

function editmeta(content)
  return content
  content = replace(content, "```@meta" => "```@meta\nCurrentModule = Hecke")
  return content
end

function edit_header(content)
  str = """
# This file is also available as a jupyter notebook and a julia file:
#
# [![download](https://img.shields.io/badge/download-notebook-blue)](https://@__REPO_ROOT_URL__.ipynb)
# [![nbviewer](https://raw.githubusercontent.com/jupyter/design/master/logos/Badges/nbviewer_badge.svg)](https://nbviewer.jupyter.org/url/@__REPO_ROOT_URL__.ipynb)
# [![download](https://img.shields.io/badge/download-script-blue)](https://@__REPO_ROOT_URL__.jl)
"""
  content = replace(content, "__HEADER__" => str)
  return content
end

function clear_header(content)
  content = replace(content, "__HEADER__" => "")
end

static_tutorial_list =
Dict("quaternion" => "Quaternion algebras",
    )

function remove_using_hecke(content)
  str = """
````@repl bla
using Hecke
````
"""
  str2 = """
````@setup bla
using Hecke
nothing
````
"""

  content = replace(content, str => str2)
  return content
end

function build_all_tutorials(Hecke::Module, local_build::Bool = false)
  # get the base_str
  relpath = local_build ? "" : "/"
  res = []
  repourl = "docs.hecke.thofma.com/"
  outdir = mkpath(joinpath(Hecke.pkgdir, "docs", "src", "public", "tutorials", "build"))
  cd(joinpath(Hecke.pkgdir, "docs", "src", "tutorials")) do
    for s in readdir(".")
      if isfile(s) && endswith(s, ".jl")
        if length(split(s, ".jl")) != 2
          error("don't put .jl in your tutorial name. what are you? some kind of monster?")
        end
        name, = split(s, ".jl")
        name = String(name)
        mdlink = repourl * "docs/src/tutorials/" * name
        ipylink = repourl * "docs/src/tutorials/" * name * ".ipynb"
        mdfile = basename(Literate.markdown(s; codefence = codefence = "````@repl bla" => "````", preprocess = edit_header, postprocess = remove_using_hecke, repo_root_url = repourl * "dev/tutorials/build/" * name * "", name =name, credit = false))
        @info mdfile
        notebookfile = basename(Literate.notebook(s, preprocess = clear_header, outdir, credit = false))
        scriptfile = basename(Literate.script(s, preprocess = clear_header, outdir, credit = false))
        push!(res, (name, mdfile, notebookfile, scriptfile))
      end
    end
  end

  cd(joinpath(Hecke.pkgdir, "docs", "src", "tutorials")) do
    open("index.md", "w") do io
      println(io, """
```@meta
CurrentModule = Hecke
DocTestSetup = Hecke.doctestsetup()
```
# Tutorials
"""
    )
      for (s, mdfile, notebookfile, scriptfile) in res
        println(io, "- [$(static_tutorial_list[s])]($mdfile)")
      end
    end
  end
end

end # module Build

using .Build
