module NormRel

using Hecke

import Hecke: one, can_solve_with_kernel, lcm!, simplify, NfFactorBase

add_verbosity_scope(:NormRelation)
add_assertion_scope(:NormRelation)

include("NormRelation/Setup.jl")
include("NormRelation/SUnits.jl")
include("NormRelation/Clgp.jl")

end # module

export norm_relation
