using Documenter, Hecke, Pkg

include(normpath(joinpath(Hecke.pkgdir, "docs", "Build.jl")))

Build.make(Hecke; strict=false, local_build=false, doctest=true, format = :mkdocs)

## Overwrite printing to make the header not full of redundant nonsense
## Turns
##   Hecke.Order - Method
## into
##   Order - Method
#
## To remove the '-'
## Documenter.Utilities.print_signature(io::IO, signature)        = print(io, signature)
#
## To remove the "Method", "Type", "Module" use the following
## Documenter.Utilities.doccat(b::Base.Docs.Binding, ::Type)  = ""
## doccat(::Type)     = ""
## doccat(::Module)   = ""
#
## Remove the module prefix
#Base.print(io::IO, b::Base.Docs.Binding) = print(io, b.var)

# We use 'mike', a mkdocs extension to display a selector. 
# We create the versions.json for the selector Usually Documenter.jl creates a
# versions.js containing the information.
function Documenter.Writers.HTMLWriter.generate_version_file(versionfile::AbstractString, entries, symlinks = [])
    versionfile = joinpath(dirname(versionfile), "versions.json")
    open(versionfile, "w") do buf
        symlinks = Dict(symlinks)
        isempty(entries) && return
        println(buf, "[")
        for (j, folder) in enumerate(entries)
          print(buf, "{\"version\": \"$(folder)\", \"title\": \"$(folder)\", \"aliases\": ")
          print(buf, "[")
          for (i, al) in enumerate([e for e in symlinks if e.first == folder])
            print(buf, "\"", al.second, "\"")
            if i < length([e for e in symlinks if e.first == folder])
              print(buf, ", ")
            end
          end
          print(buf, "]}")
          if j < length(entries)
            print(buf, ",")
          end
          print(buf, "\n")
        end
        print(buf, "]")
    end
end

deps = Pkg.dependencies()
ver = Pkg.dependencies()[Base.UUID("3e1990a7-5d81-5526-99ce-9ba3ff248f21")]
s = string(ver.version)
if haskey(ENV, "RELEASE_VERSION")
  if ENV["RELEASE_VERSION"] == "master"
    s = "dev"
    cmd = `mike deploy $s`
  else
    s = ENV["RELEASE_VERSION"]
    cmd = `mike deploy $s`
  end
else
  s = `mkdocs deploy`
end

deploydocs(
  repo = "github.com/thofma/Hecke.jl.git",
  deps = Deps.pip("pymdown-extensions",
                  "pygments",
                  "mkdocs",
                  "python-markdown-math",
                  "mkdocs-material",
                  "mkdocs-cinder",
                  "mike"),
  target = "site",
  make = () -> run(cmd),
  forcepush = true
)
