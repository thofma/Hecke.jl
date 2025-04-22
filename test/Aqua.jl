using Aqua

@testset "Aqua.jl" begin
  Aqua.test_all(
    Hecke;
    ambiguities=false,      # TODO: fix ambiguities
    piracies=false          # TODO: fix piracy
  )
end
