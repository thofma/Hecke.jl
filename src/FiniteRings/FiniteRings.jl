module FiniteRings

import ..Hecke

import ..Hecke:
  @attr,
  @attributes,
  @req,
  @vprint,
  @vprintln,
  AbsOrdQuoRing,
  AbstractAlgebra,
  AbstractAssociativeAlgebra,
  AbstractAssociativeAlgebra,
  ConformanceTests,
  FinFieldElem,
  FinGenAbGroup,
  FinGenAbGroupElem,
  FinGenAbGroupHom,
  FpFieldElem,
  FqFieldElem,
  GF,
  HeckeMap,
  IntegerUnion,
  ItemQuantity,
  Map,
  MapFromFunc,
  MatAlgebra,
  NCRing,
  NCRingElem,
  NCRingElement,
  Nemo,
  Ring,
  RingElem,
  RingElement,
  StructureConstantAlgebra,
  ZZ,
  ZZMatrix,
  _eltseq,
  _subalgebra,
  abelian_group,
  absolute_degree,
  base_ring,
  base_ring_type,
  basis,
  basis_matrix,
  biproduct,
  center,
  central_primitive_idempotents,
  characteristic,
  codomain,
  coefficients,
  coefficients,
  coordinates,
  data,
  decompose,
  degree,
  dim,
  direct_product,
  domain,
  elem_type,
  elementary_divisors,
  fits,
  fpFieldElem,
  free_abelian_group,
  gen,
  gens,
  get_attribute!,
  get_attribute,
  has_attribute,
  has_complement,
  has_preimage_with_preimage,
  hom,
  id_hom,
  ideal,
  identity_matrix,
  image,
  inv,
  inv,
  is_commutative,
  is_exact_type,
  is_finite,
  is_invertible,
  is_known,
  is_one,
  is_prime,
  is_prime_power_with_data,
  is_trivial,
  is_unit,
  is_zero,
  isomorphism,
  iszero,
  kernel,
  left_ideal,
  left_ideal,
  lift,
  map_entries,
  matrix,
  matrix_algebra,
  mul!,
  ncols,
  ngens,
  nrows,
  one,
  one,
  order,
  parent,
  parent,
  parent_type,
  preimage,
  preimage,
  prime_divisors,
  promote_rule,
  quo,
  radical,
  rank,
  rels,
  representation_matrix,
  right_ideal,
  right_ideal,
  set_attribute!,
  show_snf_structure,
  snf,
  sub,
  sylow_subgroup,
  twosided_ideal,
  unit_group,
  zero,
  zero,
  zero_matrix

function __init__()
  Hecke.add_verbosity_scope(:FiniteRings)
end


include("Types.jl")
include("Ring.jl")
include("Elem.jl")
include("OnePlusIdeal.jl")
include("Ideal.jl")
include("Map.jl")
include("Conversions.jl")

export FiniteRing
export FiniteRingElem
export FiniteRingHom
export FiniteRingMap
export additive_generators
export decompose_into_indecomposable_rings
export decompose_into_p_rings
export finite_ring
export is_indecomposable
export maximal_p_quotient_ring
export number_of_additive_generators

end

using .FiniteRings
