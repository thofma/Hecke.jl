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
    deps = Deps.pip("pygments",
                    "mkdocs",
                    "python-markdown-math",
                    "mkdocs-cinder"),
    repo = "github.com/thofma/Hecke.jl.git",
    julia = "0.5",
)
