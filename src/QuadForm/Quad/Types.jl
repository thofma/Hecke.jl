export ZLat

@attributes mutable struct ZLat <: AbsLat{FlintRationalField}
  space::QuadSpace{FlintRationalField, fmpq_mat}
  rational_span::QuadSpace{FlintRationalField, fmpq_mat}
  basis_matrix::fmpq_mat
  gram_matrix::fmpq_mat
  aut_grp_gen::fmpq_mat
  aut_grp_ord::fmpz
  automorphism_group_generators::Vector{fmpz_mat} # With respect to the
                                                  # basis of the lattice
  automorphism_group_order::fmpz
  minimum::fmpq

  scale::fmpq
  norm::fmpq

  function ZLat(V::QuadSpace{FlintRationalField, fmpq_mat}, B::fmpq_mat)
    z = new()
    z.space = V
    z.basis_matrix = B
    return z
  end
end

@attributes mutable struct QuadLat{S, T, U} <: AbsLat{S}
  space::QuadSpace{S, T}
  pmat::U
  gram::T                        # gram matrix of the matrix part of pmat
  rational_span::QuadSpace{S, T}
  base_algebra::S
  automorphism_group_generators::Vector{T}
  automorphism_group_order::fmpz
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


