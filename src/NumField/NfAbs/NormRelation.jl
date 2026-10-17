module NormRel

using Hecke

import Hecke: one, can_solve_with_solution_and_kernel, kernel, lcm!, simplify, NfFactorBase, morphism_type, nf,
              find_small_group

include("NormRelation/Setup.jl")
include("NormRelation/SUnits.jl")
include("NormRelation/Clgp.jl")

end # module
