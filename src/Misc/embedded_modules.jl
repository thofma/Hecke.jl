module EmbeddedModules

import ..Hecke

import Base: +, ==, intersect, issubset, parent
import LinearAlgebra: rank

import ..Hecke:
  @req,
  AbsNumFieldOrder,
  FieldElement,
  FractionFieldMap,
  HeckeMap,
  KInftyRing,
  Map,
  MatElem,
  MatrixElem,
  PMat,
  PolyRing,
  Ring,
  RingElem,
  ZZRing,
  _has_preimage,
  _hnf,
  _hnf_modular_eldiv,
  _preimage,
  basis,
  base_ring,
  can_solve_with_solution,
  change_base_ring,
  codomain,
  coordinates,
  decompose,
  dense_matrix_type,
  det,
  diagonal,
  divexact,
  domain,
  elem_type,
  fraction_field_map,
  free_module,
  hom,
  image,
  invariant_factors,
  is_compatible,
  is_divisible_by,
  is_bijective,
  is_injective,
  is_known,
  is_prime,
  is_surjective,
  is_zero_row,
  kernel,
  matrix,
  mul!,
  ncols,
  nrows,
  preimage,
  quo,
  residue_field,
  ring,
  snf,
  sub,
  zero,
  zero_matrix,
  zeros_array

include("embedded_modules/Types.jl")
include("embedded_modules/Elements.jl")
include("embedded_modules/Basics.jl")
include("embedded_modules/Arithmetic.jl")
include("embedded_modules/Containment.jl")
include("embedded_modules/Quotients.jl")
include("embedded_modules/Map.jl")

export EmbeddedModule
export EmbeddedModuleElem
export EmbeddedModuleMap
export PseudoElement
export _DD
export _Field
export _PID
export _RingType
export _ring_type
export _check_compatible
export _element_from_ambient_coordinates
export _element_from_coordinates
export _element_from_coordinates_and_ambient_coordinates
export _embedded_module_type
export _in
export _map
export _pseudo_element
export _tmp_mat_overring
export ambient_coordinates
export ambient_rank
export basis
export basis_matrix
export basis_matrix_components
export basis_matrix_inverse
export basis_matrix_numerator
export embedded_module
export element
export fraction_map
export fractional_ideal
export generator_matrix
export has_full_rank
export index_multiple
export index
export overring
export overstructure
export quotient_vector_space
export ring
export set_basis_matrix
export set_basis_matrix_components
export set_basis_matrix_inverse
export zero_embedded_module

end # module EmbeddedModules

import .EmbeddedModules:
  EmbeddedModule,
  EmbeddedModuleElem,
  EmbeddedModuleMap,
  PseudoElement,
  _DD,
  _Field,
  _PID,
  _RingType,
  _check_compatible,
  _element_from_ambient_coordinates,
  _element_from_coordinates,
  _element_from_coordinates_and_ambient_coordinates,
  _embedded_module_type,
  _in,
  _map,
  _pseudo_element,
  _ring_type,
  _tmp_mat_overring,
  ambient_coordinates,
  ambient_rank,
  basis_matrix,
  basis_matrix_components,
  basis_matrix_inverse,
  basis_matrix_numerator,
  embedded_module,
  element,
  fraction_map,
  fractional_ideal,
  generator_matrix,
  has_full_rank,
  index,
  index_multiple,
  overring,
  overstructure,
  quotient_embedded_module,
  quotient_vector_space,
  ring,
  set_basis_matrix,
  set_basis_matrix_components,
  set_basis_matrix_inverse,
  zero_embedded_module
