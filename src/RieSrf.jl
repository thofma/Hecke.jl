include("RieSrf/Theta.jl")
module RiemannSurfaces

using Hecke

export RiemannSurface, discriminant_points, embedding, genus, precision,
fundamental_group_of_punctured_P1, monodromy_representation, monodromy_group,
homology_basis

export max_radius, radius_factor, find_paths_to_end, sheet_ordering,
embed_mpoly, analytic_continuation, minimal_spanning_tree

import Hecke.AbstractAlgebra, Hecke.Nemo
import Hecke.IntegerUnion
import Hecke:function_field, basis_of_differentials, genus, embedding, evaluate, fillacb!, length, reverse, precision, round_scale!, shortest_vectors, radius
import Base:show, isequal, mod2pi
using FLINT_jll: libflint

import Nemo: acb_struct, acb_vec, acb_vec_clear, array

include("RieSrf/Auxiliary.jl")
include("RieSrf/CPath.jl")
include("RieSrf/NumIntegrate.jl")
include("RieSrf/RiemannSurface.jl")
include("RieSrf/PeriodMatrix.jl")
end
