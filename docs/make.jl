using Documenter, Hecke

makedocs(
    modules = Hecke,
    clean   = true,
)

deploydocs(
    deps = Deps.pip("pygments", "mkdocs", "mkdocs-material", "python-markdown-math"),
    repo = "github.com/thofma/Hecke.jl.git",
    julia = "0.4",
)
