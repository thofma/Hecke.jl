include("RieSrf/Theta.jl")
module RiemannSurfaces

using Hecke

# The user-facing functions. (Everything else is internal; the tests and
# diagnostics access it as Hecke.RiemannSurfaces.name.)
export riemann_surface, RiemannSurface, genus, precision, embedding,
       big_period_matrix, small_period_matrix, homology_basis,
       discriminant_points, ramification_points, singular_points, infinite_points,
       y_infinite_points, critical_points, fiber, complex_defining_polynomial,
       fundamental_group_of_punctured_P1, monodromy_representation, monodromy_group,
       abel_jacobi_map, divisor,
       tangent_representation, homology_representation,
       geometric_homomorphism_representation, geometric_homomorphism_representation_nf,
       geometric_endomorphism_representation, geometric_endomorphism_representation_nf,
       approximate_minimal_polynomial, algebraize_element, endomorphism_structure


import Hecke.AbstractAlgebra, Hecke.Nemo
import Hecke.AbstractAlgebra.is_terse
import Hecke.IntegerUnion
import Hecke:function_field, basis_of_differentials, genus, embedding, defining_polynomial,
evaluate, fillacb!, length, reverse, precision, round_scale!, shortest_vectors, radius, zeros_array, center,
degree, support, complex_field, acosh, asinh, atanh
import Base:show, isequal, *, ^, inv, ==, +, -, parent, position
using FLINT_jll: libflint

import Nemo: acb_struct, acb_vec, acb_vec_clear, array

include("RieSrf/Numerics/ArbHelpers.jl")
include("RieSrf/Numerics/Auxiliary.jl")
include("RieSrf/Numerics/IntegrationParameters.jl")
include("RieSrf/Numerics/NumericalKernel.jl")
include("RieSrf/Types.jl")
include("RieSrf/Paths/CPath.jl")
include("RieSrf/Periods/Quadrature/GaussLegendre.jl")
include("RieSrf/Periods/Quadrature/DoubleExponential.jl")
include("RieSrf/Periods/Quadrature/Grouping.jl")
include("RieSrf/Periods/Quadrature/Bounds.jl")
include("RieSrf/Surface/RiemannSurfaceModel.jl")
include("RieSrf/Surface/Differentials.jl")
include("RieSrf/Periods/Integrand.jl")
include("RieSrf/Surface/Discriminant.jl")
include("RieSrf/Surface/Fiber.jl")
include("RieSrf/Paths/AnalyticContinuation.jl")
include("RieSrf/Paths/Topology.jl")
include("RieSrf/Periods/ParallelIntegration.jl")
include("RieSrf/Periods/PeriodMatrix.jl")
include("RieSrf/AbelJacobi/SpecialPoints.jl")
include("RieSrf/AbelJacobi/RieSrfPoints.jl")
include("RieSrf/AbelJacobi/Divisors.jl")
include("RieSrf/AbelJacobi/AbelJacobiMap.jl")
include("RieSrf/Surface/RiemannSurface.jl")
include("RieSrf/Surface/SpaceCurves.jl")
include("RieSrf/Periods/Superelliptic.jl")
include("RieSrf/Endomorphisms/HeuristicEndomorphisms.jl")
include("RieSrf/Endomorphisms/Algebraization.jl")
include("RieSrf/Endomorphisms/EndomorphismStructure.jl")
include("RieSrf/Reconstruction/ThetaCharacteristics.jl")
include("RieSrf/Reconstruction/ReconstructNumerics.jl")
include("RieSrf/Reconstruction/ReconstructCurvesG123.jl")
include("RieSrf/Reconstruction/ReconstructG4Tables.jl")
include("RieSrf/Reconstruction/ReconstructG4.jl")
include("RieSrf/Reconstruction/ReconstructG4Tests.jl")
end