# Tests of src/RieSrf. The test of src/RieSrf/<Folder>/<File>.jl is
# test/RieSrf/<Folder>/<File>.jl. The CI runs these files one by one (this
# wrapper only for Hecke.test_module("RieSrf")), so each includes what it needs
# from test/RieSrfHelpers: TestHelpers.jl (shared helpers and test curves) and
# ReconstructionHelpers.jl (comparisons and random curves of the
# reconstruction tests). test/RieSrfHelpers is not run by the CI, nor are the
# diagnostics in test/RieSrfHelpers/Diagnostics (precision suite, genus 4
# reconstruction).
@testset "RieSrf" begin
  include("RieSrfHelpers/TestHelpers.jl")
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
  include("RieSrf/AbelJacobi/RieSrfPoints.jl")
  include("RieSrf/AbelJacobi/Divisors.jl")
  include("RieSrf/AbelJacobi/AbelJacobiMap.jl")
  include("RieSrf/Theta.jl")
  include("RieSrf/Endomorphisms/HeuristicEndomorphisms.jl")
  include("RieSrf/Endomorphisms/Algebraization.jl")
  include("RieSrf/Endomorphisms/EndomorphismStructure.jl")
  include("RieSrfHelpers/ReconstructionHelpers.jl")
  include("RieSrf/Reconstruction/ReconstructCurvesG123.jl")
  include("RieSrf/Reconstruction/ReconstructG4.jl")
end
