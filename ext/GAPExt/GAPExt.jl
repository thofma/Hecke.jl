module GAPExt

using Hecke, GAP

const Nemo = Hecke.Nemo
const AbstractAlgebra = Hecke.AbstractAlgebra

import Hecke:
  cartesian_product_iterator,
  check_obstruction,
  compose_mod,
  field_context,
  find_gens,
  fixed_field,
  fixed_field1,
  has_quotient,
  image_generators,
  image_primitive_element,
  induce_action_on_subgroup,
  intersect_prime,
  is_automorphisms_known,
  is_fixed_point_free,
  IdGroup,
  number_field,
  AbsSimpleNumFieldEmbedding,
  permutation_group1,
  primitive_frobenius_extensions,
  ramified_primes,
  set_automorphisms,
  simplified_simple_extension,
  _isequal,
  _find_complex_conjugation,
  _order,
  _relative_to_absolute,
  _relative_to_absoluteQQ,
  __convert_map_data

import Base: iszero

function __init__()
  add_verbosity_scope(:Fields)
  add_assertion_scope(:Fields)
  add_verbosity_scope(:FieldsNonFancy)
  add_verbosity_scope(:BrauerObst)
end

include("meataxe.jl")
include("fields.jl")
include("FrobeniusExtensions.jl")
include("merge.jl")
include("abelian_layer.jl")
include("brauer.jl")
include("chain.jl")
include("conductors.jl")
include("non_normal.jl")
include("maximal_abelian_subextension.jl")

end
