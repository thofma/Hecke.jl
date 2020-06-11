# Hermitian lattices
mutable struct HermLat{S, T, U, V, W} <: AbsLat{S}
  space::HermSpace{S, T, U, W}
  pmat::V
  gram::U
  rational_span::HermSpace{S, T, U, W}
  base_algebra::S
  involution::W
  automorphism_group_generators::Vector{U}
  automorphism_group_order::fmpz
  generators
  minimal_generators
  @declare_other

  function HermLat{S, T, U, V, W}() where {S, T, U, V, W}
    z = new{S, T, U, V, W}()
    return z
  end

  function HermLat(E::S, G::U, P::V) where {S, U, V}
    @assert degree(E) == 2
    A = automorphisms(E)
    a = gen(E)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    K = base_field(E)

    space = HermSpace(E, G)

    z = new{S, typeof(K), U, V, typeof(involution)}(space, P)
    z.base_algebra = E
    z.involution = involution
    return z
  end

  function HermLat(E::S, G::U) where {S, U}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(E, n))
    return HermLat(E, G, M)
  end
end


