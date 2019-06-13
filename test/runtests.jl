using Hecke

using Test

using LinearAlgebra

for scope in Hecke.ASSERT_SCOPE
  set_assert_level(scope, 3)
end

#for scope in Hecke.VERBOSE_SCOPE
#  set_verbose_level(scope, 3)
#end

@time include("NumField.jl")
@time include("AlgAss.jl")
@time include("AlgAssAbsOrd.jl")
@time include("AlgAssRelOrd.jl")
@time include("EllCrv.jl")
@time include("GrpAb.jl")
@time include("Grp.jl")
@time include("LinearAlgebra.jl")
@time include("Map.jl")
@time include("Misc.jl")
@time include("NfAbs.jl")
@time include("NfOrd.jl")
@time include("NfRel.jl")
@time include("RCF.jl")
@time include("Examples.jl")
@time include("Sparse.jl")
