function quo(M::EmbeddedModule{_PID}, N::EmbeddedModule{_PID})
  _check_compatible(M, N)
  fl, T = _in(basis_matrix(N), M, Val(true))
  @req fl "Not a submodule"
  F = free_module(ring(M), rank(M))
  S, _ = sub(F, [F(T[i, :]) for i in 1:nrows(T)])
  E = elem_type(ring(M))
  Q, FtoQ = quo(F, S)::Tuple{Hecke.AbstractAlgebra.Generic.QuotientModule{E},
                            Hecke.AbstractAlgebra.Generic.ModuleHomomorphism{E}}
  d = EmbeddedModuleDataPIDQuotient(M, Q, N, FtoQ)
  return Q, EmbeddedModuleMap(M, Q, d)
end

@doc raw"""
    quotient_embedded_module(M::EmbeddedModule, N::EmbeddedModule)

For PID coefficients, return `(Q, f)` representing the torsion-free quotient
$M/N$ as an embedded $R^d$ in `overring(M)^d`, together with its projection map.
Require compatible modules with $N \subseteq M$. Throw an error if the quotient
has torsion.
"""
function quotient_embedded_module(M::EmbeddedModule{_PID}, N::EmbeddedModule{_PID})
  Q, MtoQ = quo(M, N)
  S, StoQ = snf(Q)
  invfac = invariant_factors(S)
  @req all(iszero, invfac) "Quotient is not torsion-free"
  d = length(invfac)
  E = embedded_module(ring(M), overring(M), Hecke.identity_matrix(overring(M), d);
                      is_basis_matrix = true)
  images = Vector{elem_type(E)}(undef, rank(M))
  for (i, b) in enumerate(basis(M; copy = false))
    c = coordinates(preimage(StoQ, MtoQ(b)))
    images[i] = _element_from_coordinates(E, c; check = false)
  end
  return E, hom(M, E, images)
end

@doc raw"""
    quotient_vector_space(M::EmbeddedModule{_PID}, p::RingElem)
    quotient_vector_space(M::EmbeddedModule{_PID}, N::EmbeddedModule{_PID}, p::RingElem)

Return `(V, f, RtoF)` for the quotient $M/pM$ or $M/N$ over the residue
field $F = R/(p)$, where $R$ is the coefficient PID and `p` is prime in `R`.
The second form requires $pM \subseteq N \subseteq M$.
"""
function quotient_vector_space(M::EmbeddedModule{_PID}, p::RingElem)
  R = ring(M)
  @req parent(p) === R "Prime must belong to the coefficient ring"
  @req (R isa ZZRing ? is_prime(p) : Hecke.is_irreducible(p)) "Element must be prime"
  F, RtoF = residue_field(R, p)
  V = free_module(F, rank(M); cached = false)
  s = image(fraction_map(M), p)
  N = embedded_module(R, overring(M), s * basis_matrix(M);
                      overstructure = overstructure(M), is_basis_matrix = true)
  d = EmbeddedModuleDataPIDReduction(M, V, N, RtoF, nothing, nothing)
  return V, EmbeddedModuleMap(M, V, d), RtoF
end

function quotient_vector_space(M::EmbeddedModule{_PID}, N::EmbeddedModule{_PID},
                               p::RingElem)
  R = ring(M)
  @req parent(p) === R "Prime must belong to the coefficient ring"
  @req (R isa ZZRing ? is_prime(p) : Hecke.is_irreducible(p)) "Element must be prime"
  @req issubset(N, M) "Not a submodule"
  F, RtoF = residue_field(R, p)
  Q, MtoQ = quo(M, N)
  S, StoQ = snf(Q)
  invfac = invariant_factors(S)
  @req all(x -> is_divisible_by(p, x) && is_divisible_by(x, p),
           invfac) "Quotient must be annihilated by the prime"
  r = rank(M)
  d = length(invfac)
  V = free_module(F, d; cached = false)
  A = zero_matrix(F, r, d)
  if iszero(d)
    B = zero_matrix(F, 0, r)
  else
    for (i, b) in enumerate(basis(M; copy = false))
      c = coordinates(preimage(StoQ, MtoQ(b)))
      A[i, :] = elem_type(F)[image(RtoF, a) for a in c]
    end
    fl, B = can_solve_with_solution(A, Hecke.identity_matrix(F, d); side = :left)
    @assert fl
  end
  data = EmbeddedModuleDataPIDReduction(M, V, N, RtoF, A, B)
  return V, EmbeddedModuleMap(M, V, data), RtoF
end
