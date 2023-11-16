using Aqua

@testset "Aqua.jl" begin
  Aqua.test_all(
    Hecke;
    ambiguities=false,      # TODO: fix ambiguities
    stale_deps=(ignore=[:GAP, :Polymake],),
    deps_compat=(ignore=[:GAP, :Polymake],),
    piracies=false          # TODO: fix piracy
  )
end
