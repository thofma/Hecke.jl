using Hecke

using Test

using LinearAlgebra

for scope in Hecke.ASSERT_SCOPE
  set_assert_level(scope, 3)
end

#for scope in Hecke.VERBOSE_SCOPE
#  set_verbose_level(scope, 3)
#end

@time include("AlgAss.jl")
@time include("AlgAssOrd.jl")
@time include("EllCrv.jl")
@time include("GrpAb.jl")
@time include("LinearAlgebra.jl")
@time include("Map.jl")
@time include("Misc.jl")
@time include("NfAbs.jl")
@time include("NfOrd.jl")
@time include("NfRel.jl")
@time include("RCF.jl")
@time include("Examples.jl")
@time include("Sparse.jl")

# x^5 + 514944*x^2 + 123904 test prime decomposition with this (2 is index divisor and only one prime ideal over 2)
