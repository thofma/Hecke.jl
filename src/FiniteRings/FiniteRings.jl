module FiniteRings

import ..Hecke

import ..Hecke:
  right_ideal,
  left_ideal,
  mul!,
  data,
  parent,
  one,
  inv,
  basis_matrix,
  get_attribute,
  prime_divisors,
  is_known,
  is_exact_type,
  zero,
  AbstractAssociativeAlgebra,
  AbstractAlgebra,
  set_attribute!,
  MatAlgebra,
  RingElement,
  NCRingElement,
  ConformanceTests,
  @attributes,
  @attr,
  one,
  inv,
  Ring,
  RingElem,
  elem_type,
  parent_type,
  zero,
  is_commutative,
  is_one,
  is_prime_power_with_data,
  @req,
  radical,
  is_unit,
  parent,
  base_ring,
  base_ring_type,
  order,
  ideal,
  preimage,
  IntegerUnion,
  quo,
  is_zero,
  iszero,
  unit_group,
  FinGenAbGroup,
  FinGenAbGroupElem,
  FinGenAbGroupHom,
  FinFieldElem,
  StructureConstantAlgebra,
  is_finite,
  absolute_degree,
  characteristic,
  dim,
  abelian_group,
  basis,
  hom,
  lift,
  ZZ,
  representation_matrix,
  sub,
  has_preimage_with_preimage,
  id_hom,
  free_abelian_group,
  ngens,
  snf,
  ItemQuantity,
  ncols,
  nrows,
  rels,
  NCRing,
  NCRingElem,
  coefficients,
  coordinates,
  gens,
  get_attribute!,
  is_prime,
  elementary_divisors,
  GF,
  Map,
  matrix_algebra,
  map_entries,
  matrix,
  ZZMatrix,
  is_trivial,
  isomorphism,
  decompose,
  degree,
  codomain,
  domain,
  direct_product,
  image,
  preimage,
  gen,
  rank,
  @vprint,
  @vprintln,
  sylow_subgroup,
  center,
  biproduct,
  kernel,
  zero_matrix,
  identity_matrix,
  is_invertible

function __init__()
  Hecke.add_verbosity_scope(:FiniteRings)
end


include("Types.jl")
#include("EffectivePresentation.jl")
#include("GL.jl")
include("Ring.jl")
include("Elem.jl")
include("OnePlusIdeal.jl")
#include("Units.jl")
include("Ideal.jl")
include("Map.jl")
#include("Ktheory.jl")

function isomorphism(::Type{FinGenAbGroup}, Q::StructureConstantAlgebra)
  F = base_ring(Q)
  @assert absolute_degree(F) == 1
  p = characteristic(F)
  A = abelian_group([p for i in 1:dim(Q)])
  f = x -> begin # A to Q (abelian group to Q)
    @assert parent(x) === A
    return Q(F.([x.coeff[i] for i in 1:dim(Q)]))
  end
  g = y -> begin # Q to A (Q to abelian group)
    @assert parent(y) === Q
    return A(lift.(Ref(ZZ), coefficients(y)))
  end
  return A, f, g
end

Hecke.base_ring(I::Hecke.AbsAlgAssIdl) = Hecke.algebra(I)

export finite_ring
export maximal_p_quotient_ring
export decompose_into_p_rings
export decompose_into_indecomposable_rings

end

using .FiniteRings

export finite_ring
export maximal_p_quotient_ring
export decompose_into_p_rings
export decompose_into_indecomposable_rings
