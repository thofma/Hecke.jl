using Aqua

@testset "Aqua.jl" begin
  Aqua.test_all(
    Hecke;
    ambiguities=false,      # TODO: fix ambiguities
    unbound_args=true,
    undefined_exports=true,
    project_extras=true,
    stale_deps=true,
    deps_compat=true,
    project_toml_formatting=true,
    piracy=false            # TODO: fix piracy
  )
end
