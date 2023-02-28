export ZLat

@attributes mutable struct ZLat <: AbstractLat{QQField}
  space::QuadSpace{QQField, QQMatrix}
  rational_span::QuadSpace{QQField, QQMatrix}
  basis_matrix::QQMatrix
  gram_matrix::QQMatrix
  aut_grp_gen::QQMatrix
  aut_grp_ord::ZZRingElem
  automorphism_group_generators::Vector{ZZMatrix} # With respect to the
                                                  # basis of the lattice
  automorphism_group_order::ZZRingElem
  minimum::QQFieldElem

  scale::QQFieldElem
  norm::QQFieldElem

  function ZLat(V::QuadSpace{QQField, QQMatrix}, B::QQMatrix)
    z = new()
    z.space = V
    z.basis_matrix = B
    return z
  end
end

@attributes mutable struct QuadLat{S, T, U} <: AbstractLat{S}
  space::QuadSpace{S, T}
  pmat::U
  gram::T                        # gram matrix of the matrix part of pmat
  rational_span::QuadSpace{S, T}
  base_algebra::S
  automorphism_group_generators::Vector{T}
  automorphism_group_order::ZZRingElem
  generators
  minimal_generators
  norm
  scale

  function QuadLat{S, T, U}() where {S, T, U}
    return new{S, T, U}()
  end

  function QuadLat(K::S, G::T, P::U) where {S, T, U}
    space = quadratic_space(K, G)
    z = new{S, T, U}(space, P)
    z.base_algebra = K
    return z
  end

  function QuadLat(K::S, G::T) where {S, T}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(K, n))
    return QuadLat(K, G, M)
  end
end

