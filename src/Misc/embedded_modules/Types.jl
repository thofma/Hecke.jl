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

################################################################################
#
#  Map types
#
################################################################################

# User-facing methods for a map M -> X (M an R-module)
#
#   hom(M, X, image_of_basis)
#   hom(M, X, [m_i => n_i)), where m_i is is an R-generating set
#
#   and
#
#   hom(M, X, f, image_of_basis)
#   hom(M, X, f, [m_i => n_i)), where m_i is is an R-generating set
#
# Here f is a ring morphism R -> S in case X is an S-module
# (Not sure we will need this)

# When working with maps on modules, we have to distinguish between PIDs and
# Dedekind domains.
#
# 1) PID
#   - In the generic-codomain case, we store images of *the* basis
#   - If we know that the image is an EmbeddedModule itself, we store
#     the matrix representing the map
#
# 2) Dedekind domain
#   - Have to think about this what to store

# Note that the EmbeddedModuleMapXXData types are the actual maps
# but we package everything up in EmbeddedModuleMap to only have one
# surface level type.
struct EmbeddedModuleMap{DomainT, CodomainT} <: Map{DomainT,
                                                   CodomainT,
                                                   HeckeMap,
                                                   EmbeddedModuleMap}

  domain::DomainT
  codomain::CodomainT
  data                       # realizes the actual map
                             # depends on many things
                             # this is not typed on purpose

  function EmbeddedModuleMap(domain::DomainT, codomain::CodomainT, data) where {DomainT, CodomainT}
    return new{DomainT, CodomainT}(domain, codomain, data)
  end
end

struct EmbeddedModuleDataEmbedding{DomainT, CodomainT} <:
         Map{DomainT, CodomainT, HeckeMap, EmbeddedModuleDataEmbedding}
  domain::DomainT
  codomain::CodomainT

  function EmbeddedModuleDataEmbedding(N::EmbeddedModule, M::EmbeddedModule)
    @req issubset(N, M) "The domain must be contained in the codomain"
    return new{typeof(N), typeof(M)}(N, M)
  end
end

# PID

struct EmbeddedModuleDataPIDQuotient{DomainT, CodomainT, QuotientMapT} <:
         Map{DomainT, CodomainT, HeckeMap, EmbeddedModuleDataPIDQuotient}
  domain::DomainT
  codomain::CodomainT
  kernel::DomainT
  quotient_map::QuotientMapT
end

struct EmbeddedModuleDataPIDReduction{DomainT, CodomainT, RingMapT, MatrixT} <:
         Map{DomainT, CodomainT, HeckeMap, EmbeddedModuleDataPIDReduction}
  domain::DomainT
  codomain::CodomainT
  kernel::DomainT
  ring_map::RingMapT
  projection_matrix::MatrixT  # nothing for the coordinatewise reduction M -> M/pM
  section_matrix::MatrixT
end

struct EmbeddedModuleMapPIDData{DomainT, CodomainT, RingMapT, ImageElemT} <:
         Map{DomainT, CodomainT, HeckeMap, EmbeddedModuleMapPIDData}
  # Core
  domain::DomainT
  codomain::CodomainT
  ring_map::RingMapT         #
  image_basis::ImageElemT    #

  # Additional
  data

  function EmbeddedModuleMapPIDData(domain::DomainT,
                                    codomain::CodomainT,
                                    ring_map::RingMapT,
                                    image_basis::ImageElemT) where {DomainT, CodomainT, RingMapT, ImageElemT}

    return new{DomainT, CodomainT, RingMapT, ImageElemT}(
                 domain,
                 codomain,
                 ring_map,
                 image_basis,
                 EmbeddedModuleMapPIDDataMoreData(CodomainT)
           )
  end
end

mutable struct EmbeddedModuleMapPIDDataMoreData{CodomainT}
  matrix                       # matrix representing the map
  solve_context                # left solve context

  function EmbeddedModuleMapPIDDataMoreData(::Type{T}) where {T}
    return new{T}()
  end
end

# Dedekind domains

struct EmbeddedModuleMapDDData{DomainT, CodomainT, RingMapT}
  # Core
  domain::DomainT
  codomain::CodomainT
  ring_map::RingMapT
  # ???
end
