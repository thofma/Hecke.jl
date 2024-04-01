using Documenter
using Hecke
using Pkg

include(normpath(joinpath(Hecke.pkgdir, "docs", "Build.jl")))

Build.make(Hecke; strict = Documenter.except(:missing_docs), local_build=false, doctest=true, format = :vitepress)

deploydocs(
  repo = "github.com/thofma/Hecke.jl.git",
  target = "build",
  push_preview = true,
  forcepush = true
)
