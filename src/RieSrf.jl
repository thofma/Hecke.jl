include("RieSrf/Theta.jl")
module RiemannSurfaces

using Hecke

export riemann_surface, discriminant_points, embedding, genus, precision,
fundamental_group_of_punctured_P1, monodromy_representation, monodromy_group,
homology_basis, ramification_points, singular_points, infinite_points, y_infinite_points,
abel_jacobi_map, fiber, complex_defining_polynomial, critical_points, CChain, RiemannSurface

export max_radius, radius_factor, find_paths_to_end, sheet_ordering, embed_poly,
embed_mpoly, analytic_continuation, minimal_spanning_tree, closest_point, recursive_continuation,
divisor, find_path_on_sheet, integrate_on_sheet, c_infinite_line, recursive_continuation_manual,
ajm_DE_special_point, internal_discriminant_points, compute_ellipse_bound_heuristic


export integral_left_kernel, tangent_representation, homology_representation,
geometric_homomorphism_representation, geometric_homomorphism_representation_nf, 
approximate_minimal_polynomial, algebraize_element, complex_structure, 
rational_homomorphism_equations, geometric_endomorphism_representation, 
geometric_endomorphism_representation

import Hecke.AbstractAlgebra, Hecke.Nemo
import Hecke.AbstractAlgebra.is_terse
import Hecke.IntegerUnion
import Hecke:function_field, basis_of_differentials, genus, embedding, defining_polynomial,
evaluate, fillacb!, length, reverse, precision, round_scale!, shortest_vectors, radius, zeros_array, center,
degree, support, complex_field
import Base:show, isequal, mod2pi, *, ^, inv, ==, +, -, parent
using FLINT_jll: libflint

import Nemo: acb_struct, acb_vec, acb_vec_clear, array

include("RieSrf/Auxiliary.jl")
include("RieSrf/CPath.jl")
include("RieSrf/NumIntegrate.jl")
include("RieSrf/RiemannSurface.jl")
include("RieSrf/PeriodMatrix.jl")
include("RieSrf/RieSrfPoints.jl")
include("RieSrf/Divisors.jl")
include("RieSrf/AbelJacobiMap.jl")
include("RieSrf/HeuristicEndomorphisms.jl")
include("RieSrf/Algebraization.jl")
include("RieSrf/EndomorphismStructure.jl")
end
