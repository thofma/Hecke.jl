import Nemo.sub!, Base.gcd 
export induce_rational_reconstruction, induce_crt, root, roots,
       ismonic, radical_extension, isradical_extension,
       iskummer_extension, cyclotomic_field, wildanger_field, 
       compositum

add_verbose_scope(:PolyFactor)       
add_assert_scope(:PolyFactor)       
add_verbose_scope(:CompactPresentation)       
add_assert_scope(:CompactPresentation)       

if Int==Int32
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
include("NfAbs/Hilbert.jl")
include("NfAbs/NormRelation.jl")
include("NfAbs/PolyFact.jl")
include("NfAbs/MPolyGcd.jl")
include("NfAbs/ConjugatesNS.jl")
