include("RieSrf/Theta.jl")
module RiemannSurfaces

using Hecke

export RiemannSurface, discriminant_points, embedding, genus, precision,
fundamental_group_of_punctured_P1, monodromy_representation, monodromy_group,
homology_basis

export max_radius, radius_factor, find_paths_to_end, sheet_ordering, embed_poly,
embed_mpoly, analytic_continuation, minimal_spanning_tree

export integral_left_kernel, tangent_representation, homology_representation,
geometric_homomorphism_representation, geometric_homomorphism_representation_nf, 
approximate_minimal_polynomial, algebraize_element, complex_structure, 
rational_homomorphism_equations, precision_adjuster, geometric_endomorphism_representation, 
geometric_endomorphism_representation

import Hecke.AbstractAlgebra, Hecke.Nemo
import Hecke.AbstractAlgebra.is_terse
import Hecke.IntegerUnion
import Hecke:function_field, basis_of_differentials, genus, embedding,
evaluate, fillacb!, length, reverse, precision, round_scale!, shortest_vectors, radius, zeros_array
import Base:show, isequal, mod2pi
using FLINT_jll: libflint

import Nemo: acb_struct, acb_vec, acb_vec_clear, array

include("RieSrf/Auxiliary.jl")
include("RieSrf/CPath.jl")
include("RieSrf/NumIntegrate.jl")
include("RieSrf/RiemannSurface.jl")
include("RieSrf/PeriodMatrix.jl")
include("RieSrf/HeuristicEndomorphisms.jl")
include("RieSrf/Algebraization.jl")
include("RieSrf/EndomorphismStructure.jl")
end
