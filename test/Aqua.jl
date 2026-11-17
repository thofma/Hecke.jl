using Aqua

@testset "Aqua.jl" begin
  Aqua.test_all(
    Hecke;
    # TODO: `rand(rng, R, v...)` clashes with RandomExtensions
    ambiguities=(exclude=[rand],),
    piracies=false          # TODO: fix piracy
  )
end
