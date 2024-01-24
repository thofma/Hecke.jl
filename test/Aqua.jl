using Aqua

@testset "Aqua.jl" begin
  Aqua.test_all(
    Hecke;
    persistent_tasks=false, # TODO: revert before merge
    ambiguities=false,      # TODO: fix ambiguities
    piracies=false          # TODO: fix piracy
  )
end
