abstract type _RingType end
abstract type _PID <: _RingType end
abstract type _DD <: _RingType end
abstract type _Field <: _RingType end

_ring_type(::Type{ZZRing}) = _PID
_ring_type(::Type{<:PolyRing{<:T}}) where {T <: FieldElement} = _PID
_ring_type(::Type{<:KInftyRing{T}}) where {T <: FieldElement} = _PID
_ring_type(::Type{<:AbsNumFieldOrder}) = _DD
_ring_type(R::Ring) = _ring_type(typeof(R))

struct PseudoElement{S, T}
  elem::S
  ideal::T

  PseudoElement(elem, ideal) = new{typeof(elem), typeof(ideal)}(elem, ideal)
end

# Structure to represent R-modules inside S^n, where R <= S are commutative rings.
mutable struct EmbeddedModule{RingTypeType, RingType, OverringType}
  overstructure::Any # only used to check whether modules are compatible
  generator_matrix
  ring::RingType
  overring::OverringType
  fractionmap::FractionFieldMap{RingType, OverringType}
  fullrank::Int # 0 (unknown) 1 (yes) 2 (no)
  rank::Int
  index_multiple
  basis_matrix       # might also be a pseudo-matrix? unique?
  basis_matrix_inverse
  basis_matrix_numerator
  denominator
  solve_context
  basis
  canonical_basis_matrix
  tmp_vec_ring
  tmp_vec_overring
  tmp_mat_overring

  function EmbeddedModule(overstructure,
                          generator_matrix,
                          ring::RingType,
                          overring::OverringType
      ) where {RingType, OverringType}
    z = new{_ring_type(ring), RingType, OverringType}(overstructure, generator_matrix, ring, overring, fraction_field_map(ring, overring), 0, -1)
  end
end

mutable struct EmbeddedModuleElem{ModuleType, RingType, OverringType}
  mod::ModuleType
  coords#::Vector{elem_type(RingType)}
  ambientcoords#::Vector{elem_type(OverringType)}
  pseudocoords#::Vector{elem_type(OverringType)} # Dedekind module case

  function EmbeddedModuleElem(M::EmbeddedModule{S, RingType, OverringType}) where {S, RingType, OverringType}
    return new{typeof(M), RingType, OverringType}(M)
  end
end
