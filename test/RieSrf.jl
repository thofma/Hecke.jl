# Tests of src/RieSrf. The test of src/RieSrf/<Folder>/<File>.jl is
# test/RieSrf/<Folder>/<File>.jl; TestHelpers.jl holds the shared helpers and
# test curves. The diagnostics in RieSrf/Diagnostics (precision suite,
# homomorphism stress tests) are not part of the test run.
@testset "RieSrf" begin
  include("RieSrf/TestHelpers.jl")
  include("RieSrf/Numerics/Auxiliary.jl")
  include("RieSrf/Numerics/IntegrationParameters.jl")
  include("RieSrf/Numerics/NumericalKernel.jl")
  include("RieSrf/Paths/CPath.jl")
  include("RieSrf/Paths/Topology.jl")
  include("RieSrf/Paths/AnalyticContinuation.jl")
  include("RieSrf/Periods/Quadrature/GaussLegendre.jl")
  include("RieSrf/Periods/Quadrature/DoubleExponential.jl")
  include("RieSrf/Periods/Quadrature/Grouping.jl")
  include("RieSrf/Surface/RiemannSurface.jl")
  include("RieSrf/Surface/Differentials.jl")
  include("RieSrf/Surface/Fiber.jl")
  include("RieSrf/Surface/SpaceCurves.jl")
  include("RieSrf/Periods/ParallelIntegration.jl")
  include("RieSrf/Periods/PeriodMatrix.jl")
  include("RieSrf/Periods/Superelliptic.jl")
  include("RieSrf/AbelJacobi/AbelJacobiMap.jl")
  include("RieSrf/Theta.jl")
  include("RieSrf/Endomorphisms/HeuristicEndomorphisms.jl")
  include("RieSrf/Endomorphisms/Algebraization.jl")
  include("RieSrf/Endomorphisms/EndomorphismStructure.jl")
  include("RieSrf/Reconstruction/ReconstructCurvesG123.jl")
  include("RieSrf/Reconstruction/ReconstructG4.jl")
end
