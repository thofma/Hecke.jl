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

function quo(M::EmbeddedModule{_DD}, N::EmbeddedModule{_DD})
  _check_compatible(M, N)
  @req issubset(N, M) "Not a submodule"
  A = basis_matrix(M)
  B = basis_matrix(N)
  if iszero(nrows(B))
    C = zero_matrix(overring(M), 0, nrows(A))
  else
    fl, C = can_solve_with_solution(matrix(A), matrix(B); side = :left)
    @assert fl
  end
  Q = Hecke.FPModuleDedekind(ring(M), Hecke.coefficient_ideals(A), C,
                            Hecke.coefficient_ideals(B))
  d = EmbeddedModuleDataDDQuotient(M, Q, N)
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
  return V, EmbeddedModuleMap(M, V, d)
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
  return V, EmbeddedModuleMap(M, V, data)
end

function _dd_reduction_data(M::EmbeddedModule{_DD}, p)
  R = ring(M)
  @req Hecke.order(p) === R "Prime ideal must belong to the coefficient ring"
  @req !iszero(p) && is_prime(p) "Ideal must be nonzero and prime"
  F, RtoF = residue_field(R, p)
  KtoF = Hecke.extend(RtoF, overring(M))
  u = image(fraction_map(M), Hecke.uniformizer(p))
  iu = inv(u)
  ideals = Hecke.coefficient_ideals(basis_matrix(M))
  s = Vector{elem_type(overring(M))}(undef, length(ideals))
  lifts = similar(s)
  for i in eachindex(s)
    v = Hecke.valuation(ideals[i], p)
    s[i] = v < 0 ? iu^(-v) : u^v
    c = Hecke.coprime_to(inv(s[i]) * ideals[i], p)
    lifts[i] = s[i] * c * preimage(KtoF, inv(image(KtoF, c)))
  end
  return F, RtoF, KtoF, u, s, lifts
end

function quotient_vector_space(M::EmbeddedModule{_DD}, p)
  F, RtoF, KtoF, _, s, lifts = _dd_reduction_data(M, p)
  V = free_module(F, rank(M); cached = false)
  N = p * M
  data = EmbeddedModuleDataDDReduction(M, V, N, RtoF, KtoF, s, lifts, nothing, nothing)
  return V, EmbeddedModuleMap(M, V, data)
end

function quotient_vector_space(M::EmbeddedModule{_DD}, N::EmbeddedModule{_DD}, p)
  _check_compatible(M, N)
  F, RtoF, KtoF, u, s, lifts = _dd_reduction_data(M, p)
  @req issubset(N, M) "Not a submodule"
  pM = p * M
  @req issubset(pM, N) "Quotient must be annihilated by the prime ideal"

  # Reduce a local basis of N in the local coordinates of M. Its row span
  # is N/pM, so a right kernel gives the projection onto M/N.
  BN = basis_matrix(N)
  fl, C = can_solve_with_solution(matrix(basis_matrix(M)), matrix(BN); side = :left)
  @assert fl
  A = zero_matrix(F, nrows(C), ncols(C))
  iu = inv(u)
  for i in 1:nrows(C)
    v = Hecke.valuation(Hecke.coefficient_ideals(BN)[i], p)
    t = v < 0 ? iu^(-v) : u^v
    for j in 1:ncols(C)
      A[i, j] = image(KtoF, t * C[i, j]/s[j])
    end
  end
  P = kernel(A; side = :right)
  d = ncols(P)
  V = free_module(F, d; cached = false)
  if iszero(d)
    S = zero_matrix(F, 0, rank(M))
  else
    fl, S = can_solve_with_solution(P, Hecke.identity_matrix(F, d); side = :left)
    @assert fl
  end
  data = EmbeddedModuleDataDDReduction(M, V, N, RtoF, KtoF, s, lifts, P, S)
  return V, EmbeddedModuleMap(M, V, data)
end
