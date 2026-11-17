@attr IdDict{EmbeddedModule, Any} function _mod_cache(N::EmbeddedModule)
  return IdDict{EmbeddedModule, Any}()
end

_mod_matrix_type(::EmbeddedModule{_PID, R, K}) where {R, K} =
  dense_matrix_type(R)
_mod_matrix_type(::EmbeddedModule{_DD, R, K}) where {R, K} =
  Hecke.pseudo_matrix_type(R, K)

function _mod_pivots(H::MatElem)
  return Int[something(findlast(j -> !iszero(H[i, j]), 1:ncols(H)), 0)
             for i in 1:nrows(H)]
end

_mod_pivots(H::PMat) = _mod_pivots(matrix(H))

function _mod_matrix(M::EmbeddedModule{_PID}, N::EmbeddedModule{_PID})
  fl, T = _in(basis_matrix(N), M, Val(true))
  @req fl "Not a submodule"
  iszero(nrows(T)) && return T
  return _hnf(T; shape = :lowerleft, trim = true)
end

function _mod_matrix(M::EmbeddedModule{_DD}, N::EmbeddedModule{_DD})
  @req Hecke.is_maximal(ring(M)) "The coefficient ring must be a maximal order"
  @req issubset(N, M) "Not a submodule"
  A, B = basis_matrix(M), basis_matrix(N)
  if iszero(nrows(B))
    T = zero_matrix(overring(M), 0, nrows(A))
  else
    fl, T = can_solve_with_solution(matrix(A), matrix(B); side = :left)
    @assert fl
  end
  P = Hecke.pseudo_matrix(ring(M), T, Hecke.coefficient_ideals(B))
  iszero(nrows(P)) && return P
  return Hecke.pseudo_hnf(P, :lowerleft)
end

function _mod_data(M::EmbeddedModule, N::EmbeddedModule)
  _check_compatible(M, N)
  # Parent identity matters: the normal form uses the chosen basis of M.
  data = get!(_mod_cache(N), M) do
    H = _mod_matrix(M, N)
    return H, _mod_pivots(H)
  end
  return data::Tuple{_mod_matrix_type(M), Vector{Int}}
end

function _reduce_mod!(c::Vector, H::MatElem, pivots::Vector{Int})
  for i in nrows(H):-1:1
    p = pivots[i]
    iszero(p) && continue
    r = mod(c[p], H[i, p])
    q = divexact(c[p] - r, H[i, p])
    for j in 1:p
      c[j] = c[j] - q*H[i, j]
    end
  end
  return c
end

function _reduce_mod!(c::Vector, H::PMat, pivots::Vector{Int})
  # Use the coefficient-ideal pivot sweep from Hecke._fp_module_reduce!.
  A = matrix(H)
  ideals = Hecke.coefficient_ideals(H)
  for i in nrows(A):-1:1
    p = pivots[i]
    iszero(p) && continue
    a = divexact(c[p], A[i, p])
    d = a - mod(a, ideals[i])
    for j in 1:p
      c[j] = c[j] - d*A[i, j]
    end
  end
  return c
end

@doc raw"""
    mod(x::EmbeddedModuleElem, N::EmbeddedModule)

Return a representative of `x + N` in `parent(x)`. Require compatible modules
with `N` contained in `parent(x)`. Reduce the coordinates by lower-left HNF
over a PID, or pseudo-HNF over a supported maximal order, using the scalar
`mod` conventions at each pivot. The normal form is relative to the chosen
basis or pseudo-basis of `parent(x)`; it also supports smaller-rank submodules.
Neither `x` nor the module representations are modified.
"""
function mod(x::EmbeddedModuleElem, N::EmbeddedModule)
  M = parent(x)
  H, pivots = _mod_data(M, N)
  c = _reduce_mod!(coordinates(x), H, pivots)
  return _element_from_coordinates(M, c; check = false)
end

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
  # Normalize at p and choose global lifts of the local basis.
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
  data = EmbeddedModuleDataDDReduction(M, V, N, RtoF, KtoF, s, lifts,
                                       nothing, Int[], collect(1:rank(M)))
  return V, EmbeddedModuleMap(M, V, data)
end

function quotient_vector_space(M::EmbeddedModule{_DD}, N::EmbeddedModule{_DD}, p)
  _check_compatible(M, N)
  F, RtoF, KtoF, u, s, lifts = _dd_reduction_data(M, p)
  @req issubset(N, M) "Not a submodule"
  pM = p * M
  @req issubset(pM, N) "Quotient must be annihilated by the prime ideal"

  # Write a local basis of N in the local coordinates of M.
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
  r = Hecke.rref!(A)
  A = sub(A, 1:r, 1:ncols(A))
  pivots = Hecke.find_pivots(A)
  # The nonpivot columns give a basis of M/N.
  basis_elts = setdiff(1:rank(M), pivots)
  V = free_module(F, length(basis_elts); cached = false)
  data = EmbeddedModuleDataDDReduction(M, V, N, RtoF, KtoF, s, lifts,
                                       A, pivots, basis_elts)
  return V, EmbeddedModuleMap(M, V, data)
end
