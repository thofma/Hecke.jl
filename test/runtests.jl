using Hecke


using Base.Test

for scope in Hecke.ASSERT_SCOPE
  set_assert_level(scope, 3)
end

include("NfMaxOrd/Clgp.jl")
include("NfMaxOrd/LinearAlgebra.jl")
include("NfMaxOrd/ResidueRingMultGrp.jl")
include("NfMaxOrd/RayClassGroup.jl")

include("NfOrd/NfOrd.jl")
include("NfOrd/Elem.jl")
include("NfOrd/Ideal.jl")
include("NfOrd/FracIdl.jl")
include("NfOrd/ResidueRing.jl")

#include("NfMaxOrd.jl")
#include("NfOrd.jl")
include("EllCrv.jl")
include("LinearAlgebra.jl")
include("Misc.jl")
include("RCF.jl")
include("NfRel.jl")
include("GrpAb.jl")


# x^5 + 514944*x^2 + 123904 test prime decomposition with this (2 is index divisor and only one prime ideal over 2)
