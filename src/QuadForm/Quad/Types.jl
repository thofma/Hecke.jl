mutable struct QuadLat{S, T, U} <: AbsLat{S}
  space::QuadSpace{S, T}
  pmat::U
  gram::T                        # gram matrix of the matrix part of pmat
  rational_span::QuadSpace{S, T}
  base_algebra::S
  automorphism_group_generators::Vector{T}
  automorphism_group_order::fmpz
  generators
  minimal_generators
  @declare_other

  function QuadLat{S, T, U}() where {S, T, U}
    return new{S, T, U}()
  end

  function QuadLat(K::S, G::T, P::U) where {S, T, U}
    space = QuadSpace(K, G)
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


