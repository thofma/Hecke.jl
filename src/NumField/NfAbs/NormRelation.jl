module NormRel

using Hecke

import Hecke: one, can_solve_with_kernel, lcm!, simplify, NfFactorBase

Hecke.add_verbose_scope(:NormRelation)
Hecke.add_assert_scope(:NormRelation)

include("NormRelation/Setup.jl")
include("NormRelation/SUnits.jl")
include("NormRelation/Clgp.jl")

end # module

export norm_relation
