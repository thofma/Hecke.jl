import Nemo.sub!, Base.gcd

if Int == Int32
  global const p_start = next_prime(2^30)
else
  global const p_start = next_prime(2^60)
end

include("NfAbs/NfAbs.jl")
include("NfAbs/Conjugates.jl")
include("NfAbs/CompactRepresentation.jl")
include("NfAbs/Elem.jl")
include("NfAbs/NonSimple.jl")
include("NfAbs/Poly.jl")
include("NfAbs/Simplify.jl")
include("NfAbs/DiscriminantBounds.jl")
include("NfAbs/NormRelation.jl")
include("NfAbs/PolyFact.jl")
include("NfAbs/MPolyGcd.jl")
include("NfAbs/MPolyFactor.jl")
include("NfAbs/MPolyAbsFact.jl")
include("NfAbs/ConjugatesNS.jl")
include("NfAbs/Cyclotomic.jl")
