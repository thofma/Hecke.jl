################################################################################
#
#  Embedded modules
#
#  Motivation
#  ----------
# Many objects in number theory are Z-submodules of Q-vector spaces V with
# additonal structure:
#   - orders of (absolute) number fields,
#   - orders of Q-algebras,
#   - integer lattices in quadratic spaces over Q,
#   - lattices of modules over Q-algebras
#
# More generally, objects are R-submodules of K-vector spaces V with additonal
# structure, where R is a Dedekind domain.
#
# In each case, we represent the object by storing a Z-basis specified by a
# Q-matrix with respect to the fixed basis of V. Then we have containment,
# inclusion, sums, intersections, etc. We also have to always optimize this
# again, in case one has full rank etc. It will also sneak some non-generic
# techniques in (using, for example, that one is working over Z), which makes
# it hard to generalize to other base rings later on.
#
# These operations are always they same, but we implement it for each type again.
#
# To deal with this once and for all, we introduce EmbeddedModule's, which
# gives a generic way to handle this.
#
#  Design
#  ------
# Given a pair of rings R <= S, an EmbeddedModule represents a finitely generated
# R-submodule of S^n.
#
# Such modules can be intersected, one can test for containment (of an element
# of S^n) etc.


# Type which decideds how EmbeddedModules are represened internally for the
# given ring R.
abstract type _RingType end
abstract type _PID <: _RingType end
abstract type _DD <: _RingType end
abstract type _Field <: _RingType end

_ring_type(::Type{ZZRing}) = _PID
_ring_type(::Type{<:PolyRing{<:T}}) where {T <: FieldElement} = _PID
_ring_type(::Type{<:KInftyRing{T}}) where {T <: FieldElement} = _PID
_ring_type(::Type{<:AbsNumFieldOrder}) = _DD
_ring_type(R::Ring) = _ring_type(typeof(R))

# When working over a Dedekind domain, work with PseudoElements
struct PseudoElement{S, T}
  elem::S
  ideal::T

  PseudoElement(elem, ideal) = new{typeof(elem), typeof(ideal)}(elem, ideal)
end

# Structure to represent R-modules inside S^n, where R <= S are commutative rings.
mutable struct EmbeddedModule{RingTypeType, RingType, OverringType}
  overstructure::Any          # only used to check whether modules are compatible
  generator_matrix            # matrix (or pseudo-matrix) whose rows generate the module
  ring::RingType              # R
  overring::OverringType      # S
  fractionmap::FractionFieldMap{RingType, OverringType}
                              # a map object for the map R -> S

  # Additional fluff
  fullrank::Int          # 0 (unknown) 1 (yes) 2 (no)
  rank::Int              # rank(?) of M \otimes S
  index_multiple
  basis_matrix           # might also be a pseudo-matrix? unique?
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
  mod::ModuleType                                   # the embedded module
  coords#=::Vector{elem_type(RingType)}=#           # unique coordinates with
                                                    # respect to basis matrix of mod
  ambientcoords#::Vector{elem_type(OverringType)}
  pseudocoords#::Vector{elem_type(OverringType)} # Dedekind module case
  # TODO: we should fold the pseudocoords into coords, since the OverringType knows what to do

  function EmbeddedModuleElem(M::EmbeddedModule{S, RingType, OverringType}) where {S, RingType, OverringType}
    return new{typeof(M), RingType, OverringType}(M)
  end
end
