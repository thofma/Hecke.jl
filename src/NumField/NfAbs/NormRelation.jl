module NormRel

using Hecke

import Hecke: one, can_solve_with_solution_and_kernel, kernel, lcm!, simplify, NfFactorBase, morphism_type, nf

add_verbosity_scope(:NormRelation)
add_assertion_scope(:NormRelation)

include("NormRelation/Setup.jl")
include("NormRelation/SUnits.jl")
include("NormRelation/Clgp.jl")

end # module
