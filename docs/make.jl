using Documenter, Hecke

function Markdown.plain(io::IO, ::Markdown.HorizontalRule)
           println(io, "-"^3)
end

makedocs(
    modules = Hecke,
    clean   = true,
    doctest = false,
)

# Hack around to get syntax highlighting working
cd(Pkg.dir("Hecke", "docs"))
mv("application-f78e5cb881.palette.css", "build/application-f78e5cb881.palette.css")
mv("application-e2807e330f.css", "build/application-e2807e330f.css")

deploydocs(
    deps = Deps.pip("pygments",
                    "mkdocs",
                    "python-markdown-math",
                    "mkdocs-cinder"),
    repo = "github.com/thofma/Hecke.jl.git",
    julia = "0.5",
)

