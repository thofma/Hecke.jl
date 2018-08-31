using Documenter, Hecke, Markdown, Pkg

function Markdown.plain(io::IO, ::Markdown.HorizontalRule)
           println(io, "-"^3)
end

makedocs(
    modules = Hecke,
    clean   = true,
    format = :html,
    sitename = "Hecke",
    doctest = !false,
)

# Hack around to get syntax highlighting working
cd(joinpath(dirname(pathof(Hecke)), "..", "docs"))

cp("application-f78e5cb881.palette.css", "build/application-f78e5cb881.palette.css", force = true)
cp("application-e2807e330f.css", "build/application-e2807e330f.css", force = true)

deploydocs(
     deps = nothing,
#    deps = Deps.pip()#="pygments",
#                    "mkdocs==0.16.3",
#                    "python-markdown-math",
#                    "mkdocs-cinder")=#,
    repo = "github.com/thofma/Hecke.jl.git",
    target = "build",
    make = nothing,
#    osname = "linux",
    julia = "1.0",
)

