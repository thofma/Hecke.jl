using Aqua

@testset "Aqua.jl" begin
  Aqua.test_all(
    Hecke;
    ambiguities=false,      # TODO: fix ambiguities
    unbound_args=true,
    undefined_exports=true,
    project_extras=true,
    stale_deps=(ignore=[:GAP, :Polymake],),
    deps_compat=(ignore=[:GAP, :Polymake],),
    project_toml_formatting=true,
    piracy=false            # TODO: fix piracy
  )
end
