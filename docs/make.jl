using Documenter, Hecke

function Markdown.plain(io::IO, ::Markdown.HorizontalRule)
           println(io, "-"^3)
end

makedocs(
    modules = Hecke,
    clean   = true,
    doctest = false,
)

deploydocs(
    deps = Deps.pip("pygments", "mkdocs", "mkdocs-material", "python-markdown-math", "mkdocs-bootswatch"),
    repo = "github.com/thofma/Hecke.jl.git",
    julia = "0.5",
)
