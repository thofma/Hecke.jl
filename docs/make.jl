using Documenter, Hecke, Markdown, Pkg

makedocs(
    modules = Hecke,
    clean   = true,
    doctest = false,
)

# Hack around to get syntax highlighting working
cd(Pkg.dir("Hecke", "docs"))
cp("application-f78e5cb881.palette.css", "build/application-f78e5cb881.palette.css", force = true)
cp("application-e2807e330f.css", "build/application-e2807e330f.css", force = true)

deploydocs(
    deps = Deps.pip("pygments",
                    "mkdocs==0.16.3",
                    "python-markdown-math",
                    "mkdocs-cinder"),
    repo = "github.com/thofma/Hecke.jl.git",
    osname = "linux",
    julia = "1.0",
)

