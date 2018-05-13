import Nemo.sub!, Base.gcd 
export induce_rational_reconstruction, induce_crt, root, roots,
       number_field, ismonic, pure_extension, ispure_extension,
       iskummer_extension, cyclotomic_field, wildanger_field, 
       compositum

add_verbose_scope(:PolyFactor)       
add_verbose_scope(:CompactPresentation)       
add_assert_scope(:CompactPresentation)       

if Int==Int32
  global const p_start = 2^30
else
  global const p_start = 2^60
end

#mutable struct nf_elem_deg_1_raw
#  num::Int  ## fmpz!
#  den::Int
#end
#
#mutable struct nf_elem_deg_2_raw
#  nu0::Int  ## fmpz - actually an fmpz[3]
#  nu1::Int
#  nu2::Int
#  den::Int
#end
#
#mutable struct nf_elem_deg_n_raw  #actually an fmpq_poly_raw
#  A::Ptr{Int} # fmpz
#  den::Int # fmpz
#  alloc::Int
#  len::Int
#end
#
#mutable struct nmod_t
#  n::Int
#  ni::Int
#  norm::Int
#end

include("NfAbs/NfAbs.jl")
include("NfAbs/Conjugates.jl")
include("NfAbs/CompactRepresentation.jl")
include("NfAbs/Elem.jl")
include("NfAbs/NonSimple.jl")
include("NfAbs/Poly.jl")
include("NfAbs/Simplify.jl")
