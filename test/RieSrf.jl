# Tests of src/RieSrf. The test of src/RieSrf/<Folder>/<File>.jl is
# test/RieSrf/<Folder>/<File>.jl; TestHelpers.jl holds the shared helpers and
# test curves. The diagnostics in RieSrf/Diagnostics (precision suite,
# homomorphism stress tests) are not part of the test run.
@testset "RieSrf" begin
  include("RieSrf/TestHelpers.jl")
  include("RieSrf/Numerics/IntegrationParameters.jl")
  include("RieSrf/Paths/CPath.jl")
  include("RieSrf/Paths/AnalyticContinuation.jl")
  include("RieSrf/Surface/RiemannSurface.jl")
  include("RieSrf/Surface/Differentials.jl")
  include("RieSrf/Surface/Fiber.jl")
  include("RieSrf/Surface/SpaceCurves.jl")
  include("RieSrf/Periods/PeriodMatrix.jl")
  include("RieSrf/Periods/Superelliptic.jl")
  include("RieSrf/AbelJacobi/AbelJacobiMap.jl")
  include("RieSrf/Theta.jl")
  include("RieSrf/Endomorphisms/HeuristicEndomorphisms.jl")
  include("RieSrf/Endomorphisms/Algebraization.jl")
  include("RieSrf/Endomorphisms/EndomorphismStructure.jl")
end
