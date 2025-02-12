using Documenter
using Hecke
using Pkg

include(normpath(joinpath(Hecke.pkgdir, "docs", "Build.jl")))

Build.make(Hecke; strict = Documenter.except(:missing_docs), local_build=true, doctest=false, format = :vitepress, warnonly = false)

should_push_preview = true
if get(ENV, "GITHUB_ACTOR", "") == "dependabot[bot]"
  # skip preview for dependabot PRs as they fail due to lack of permissions
  should_push_preview = false
end

deploydocs(
  repo = "github.com/thofma/Hecke.jl.git",
  target = "build",
  push_preview = should_push_preview,
  forcepush = true
)
