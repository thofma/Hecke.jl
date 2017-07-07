using Hecke

if VERSION < v"0.5.0-dev+7720"
  """
  Allows the `@testset` syntax from Julia 0.5 in Julia 0.4,
  but without the additional features.
  """
  macro testset(args...)
    isempty(args) && error("No arguments to @testset")
    return esc(args[end])
  end
end

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

#include("NfMaxOrd.jl")
#include("NfOrd.jl")
include("EllCrv.jl")
include("LinearAlgebra.jl")
include("Misc.jl")


# x^5 + 514944*x^2 + 123904 test prime decomposition with this (2 is index divisor and only one prime ideal over 2)
