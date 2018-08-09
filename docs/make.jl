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
cp("application-f78e5cb881.palette.css", "build/application-f78e5cb881.palette.css", remove_destination = true)
cp("application-e2807e330f.css", "build/application-e2807e330f.css", remove_destination = true)

deploydocs(
    deps = Deps.pip("pygments",
                    "mkdocs==0.16.3",
                    "python-markdown-math",
                    "mkdocs-cinder"),
    repo = "github.com/thofma/Hecke.jl.git",
    osname = "osx",
    julia = "0.6",
)

