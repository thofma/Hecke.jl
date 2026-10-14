# Tests of src/RieSrf. The test of src/RieSrf/<Folder>/<File>.jl is
# test/RieSrf/<Folder>/<File>.jl. Shared helpers and test curves are in
# test/RieSrf/setup_tests.jl, those of the reconstruction tests in
# test/RieSrf/Reconstruction/setup_tests.jl; the setup_tests.jl of a directory
# is included before every test file in it (docs/src/manual/developer/test.md).
# Hecke._include_test does that here as well. The diagnostics in
# test/RieSrfDiagnostics (precision suite, genus 4 reconstruction) are not
# part of the test run.
@testset "RieSrf" begin
  for file in [
    "Numerics/Auxiliary.jl",
    "Numerics/IntegrationParameters.jl",
    "Numerics/NumericalKernel.jl",
    "Paths/CPath.jl",
    "Paths/Topology.jl",
    "Paths/AnalyticContinuation.jl",
    "Periods/Quadrature/GaussLegendre.jl",
    "Periods/Quadrature/DoubleExponential.jl",
    "Periods/Quadrature/Grouping.jl",
    "Surface/RiemannSurface.jl",
    "Surface/Differentials.jl",
    "Surface/Fiber.jl",
    "Surface/SpaceCurves.jl",
    "Periods/ParallelIntegration.jl",
    "Periods/PeriodMatrix.jl",
    "Periods/Superelliptic.jl",
    "AbelJacobi/RieSrfPoints.jl",
    "AbelJacobi/Divisors.jl",
    "AbelJacobi/AbelJacobiMap.jl",
    "Theta.jl",
    "Endomorphisms/HeuristicEndomorphisms.jl",
    "Endomorphisms/Algebraization.jl",
    "Endomorphisms/EndomorphismStructure.jl",
    "Reconstruction/ReconstructCurvesG123.jl",
    "Reconstruction/ReconstructG4.jl",
  ]
    Hecke._include_test(joinpath(@__DIR__, "RieSrf", file))
  end
end
