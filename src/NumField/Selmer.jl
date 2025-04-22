module SelmerModule
using Hecke

"""
Adds an element to the group. For this to work, C needs to be a subgroup of the parent of a.
Should move to GrpAb
"""
function Base.push!(C::FinGenAbGroup, a::FinGenAbGroupElem)
  g = gens(C)
  push!(g, a)
  #TODO: find common overgroup? Assuming for now that parent(a) is it.
  return sub(parent(a), g)
end

#TODO: should be exported, but at this point, index is not yet a symbol, so it can't be extended.
#Should move to GrpAb
function index(G::FinGenAbGroup, U::FinGenAbGroup; check::Bool = true)
  return divexact(order(G), order(U))
end

@doc raw"""
    pselmer_group_fac_elem(p::Int, S::Vector{<:AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}; check::Bool = true, algo::Symbol = :raw)

Let $K$ be the number field of the prime ideals in $S$. Then the $p$-Selmer group is a subgroup of
$K^*$ modulo $p$-th powers of elements such that all valuations outside $S$ are divisible by $p$.

This parametrises the maximal radical $p$-extension unramified outside $S$.

In this version, the eelements are returned in factored form. The `algo` parameter can be set
to `:raw` or `:compRep`, in the latter case, the representatives will be reduced modulo $p$-th powers.
The support of the principl ideal can be random though.

`check` controls if the pre-image map tests if the elements are actually in the codomain.

See also `pselmer_group`

# Example
```jldoctest
julia> k, a = wildanger_field(3, 13);

julia> zk = maximal_order(k);

julia> S = collect(keys(factor(6*zk)));

julia> Sel, map = pselmer_group_fac_elem(2, S);

julia> g = evaluate(map(Sel[3]));

julia> K, _ = radical_extension(2, g);

julia> ZK = maximal_order(K);

julia> issubset(Set(keys(factor(discriminant(ZK)))) , S)
true

```
"""
function pselmer_group_fac_elem(p::Int, S::Vector{<:AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}; check::Bool = true, algo::Symbol = :raw)
  @assert all(x->order(x) == order(S[1]), S)
  @assert is_prime(p) #maybe not necessary

  #TODO: need primes above p as well?
  ZK = order(S[1])
  K = number_field(ZK)

  C, mC = class_group(ZK)
  s, ms = sub(C, map(pseudo_inv(mC), S))
  P = PrimesSet(100, -1)
  pr, pos = iterate(P)
  D = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  while gcd(index(C, s), p) != 1
    lp = prime_decomposition(ZK, pr)
    for (pi, ei) = lp
      (norm(pi) < 1000 || degree(pi) == 1) || continue
      c = preimage(mC, pi)
      c in s && continue
      s, ms = push!(s, c)
      push!(D, pi)
    end
    p, pos = iterate(P, pos)
  end

  if length(D) + length(S) == 0
    U, mU = Hecke.unit_group_fac_elem(ZK)
  else
    U, mU = Hecke.sunit_group_fac_elem(vcat(S, D))
  end

  if length(D) == 0
    k = U
    mk = hom(U, U, gens(U))
  else
    A = abelian_group([p for i = D])
    h = hom(U, A, [A([valuation(mU(g), pi) for pi = D]) for g = gens(U)])
    k, mk = kernel(h)
  end
  #so k should be the SelmerGroup...
  #sorry: k mod p*k is it.
  Sel, mSel = quo(k, p .* gens(k))
  Sel, m = snf(Sel)
  mSel = mSel * pseudo_inv(m)

  #the forward map has a couple of possibilities:
  # - take any lift to k, map to U map to K
  # -                            U and when mapping to K, reduce exponents
  # -                                                     use comp. rep.
  #
  # the backward map is more tricky, but the indirect route via
  # class field theory (Frobenius) works for Magma - it should work here.

  function toK(x::FinGenAbGroupElem; algo::Symbol = algo)
    @assert parent(x) == Sel
    @assert algo in [:compRep, :raw]
    x = preimage(mSel, x)
    x = mk(x)
    y = mU(x)

    if algo == :raw
      return y
    else
      y = Hecke.reduce_mod_powers(y, p, vcat(S, D))
      return y
    end
  end

  disc_log_data = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Tuple{Map, Vector{Int}}}()
  function toSel(x::AbsSimpleNumFieldElem; check::Bool = check)
    return toSel(FacElem([x], [1], check = check))
  end
  function toSel(x::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}; check::Bool = check)
    if check
      A = ideal(ZK, x)
      for P = S
        A = A*FacElem([P//1], [-valuation(A, P)])
      end
      I = evaluate(A)
      n, d = integral_split(I)
      fl, _ = is_power(n, p)
      fl || error("not in the image")
      fl, _ = is_power(d, p)
      fl || error("not in the image")
    end

    Fp = GF(p)
    dl = matrix(Fp, 0, ngens(Sel), [])
    dx = matrix(Fp, 0, 1, [])
    for (P, T) = disc_log_data
      v = try T[1](x)[1]
          catch e
            isa(e, Hecke.BadPrime) || rethrow(e)
            -1
          end
      if v == -1
        continue
      end
      dx = vcat(dx, matrix(Fp, 1, 1, [v]))
      dl = vcat(dl, matrix(Fp, 1, ngens(Sel), T[2]))
    end
    if length(keys(disc_log_data)) == 0
      sp = PrimesSet(100, -1, p, 1)
    else
      sp = PrimesSet(Int(maximum(minimum(P) for P = keys(disc_log_data))), -1, p, 1)
    end
    pr, pos = iterate(sp)
    while rank(dl) < ngens(Sel)
      lp = prime_decomposition(ZK, pr)
      for (pi, ei) = lp
        ei > 1 && continue
        F, mF = Hecke.ResidueFieldSmall(ZK, pi)
        u, mu = unit_group(F, n_quo = p)
        mF = Hecke.extend_easy(mF, K)
        va = try [preimage(mu, mF(toK(g)))[1] for g = gens(Sel)]
             catch e
               isa(e, BadPrime) || rethrow(e)
               nothing
             end
        va === nothing && continue
        disc_log_data[pi] = (mF*pseudo_inv(mu), va)
        v = try preimage(mu, mF(x))[1]
            catch e
              isa(e, Hecke.BadPrime) || rethrow(e)
              -1
            end
        v == -1 && continue
        dx = vcat(dx, matrix(Fp, 1, 1, [v]))
        dl = vcat(dl, matrix(Fp, 1, ngens(Sel), va))
      end
      pr, pos = iterate(sp, pos)
    end
    fl, sol = can_solve_with_solution(dl, dx; side = :right)
    @assert fl
    return Sel(map(lift, vec(collect(sol))))
  end

  return Sel, MapFromFunc(Sel, codomain(mU), toK, toSel)
end

@doc raw"""
    pselmer_group(p::Int, S::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}; check::Bool = true, algo::Symbol = :raw)

Similar to the `pselmer_group_fac_elem`, the difference is that the elements here are evaluated,
ie. returned explicitly wrt the basis of the number field.
"""
function pselmer_group(p::Int, S::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}; check::Bool = true, algo::Symbol = :raw)
  G, mp = pselmer_group_fac_elem(p, S, check = check, algo = algo)
  return G, MapFromFunc(G, number_field(order(S[1])), x->evaluate(mp(x)), y->preimage(mp, FacElem([y], ZZRingElem[1])))
end

@doc raw"""
    pselmer_group_fac_elem(p::Int, S::Vector{<:Integer}; algo::Symbol = :raw, check::Bool = true)

The Selmer group of Q - with the elements in factored form. For $p=2$, $-1$ can be included into $S$.

# Example
```jldoctest
julia> k, a = wildanger_field(3, 13);

julia> zk = maximal_order(k);

julia> S = collect(keys(factor(6*zk)));

julia> Sel, map = pselmer_group_fac_elem(2, S);

julia> sel, mmap = pselmer_group_fac_elem(2, [-1, 2, 3]);

julia> h = hom(Sel, sel, [preimage(mmap, Hecke.factored_norm(map(g), parent = codomain(mmap))) for g = gens(Sel)]);

julia> k, mk = kernel(h);

```
"""
function pselmer_group_fac_elem(p::Int, S::Vector{ZZRingElem}; algo::Symbol = :raw, check::Bool = true)
  R = FacElemMon(QQ)
  @assert all(x->(x == -1) || is_prime(x), S)
  if -1 in S
    @assert p == 2
  end
  G = abelian_group([p for i = S])
  function toQ(a::FinGenAbGroupElem)
    @assert parent(a) == G
    return FacElem(QQ, map(QQFieldElem, S), [a[i] for i = 1:ngens(G)], parent = R)
  end
  function toG(a::FacElem{QQFieldElem, QQField}; check::Bool = check)
    v = ZZRingElem[x == -1 ? sign(a)<0 : valuation(a, x) for x = S]
    if check
      b = a*FacElem(QQ, QQFieldElem[x for x = S], [-x for x = v], parent = R)
      is_power(b, p)[1] || error("not in the codomain")
    end
    return G(v)
  end
  function toG(a::QQFieldElem)
    return toF(FacElem(QQ, [a], ZZRingElem[1]), parent = R)
  end
  function toG(a::ZZRingElem)
    return toF(FacElem(QQ, QQFieldElem[a], ZZRingElem[1]), parent = R)
  end
  function toG(a::Integer)
    return toF(FacElem(QQ, QQFieldElem[a], ZZRingElem[1]), parent = R)
  end
  return G, MapFromFunc(G, R, toQ, toG)
end

function pselmer_group_fac_elem(p::Int, S::Vector{<:Integer}; algo::Symbol = :raw, check::Bool = true)
  return pselmer_group_fac_elem(p, map(ZZRingElem, S), algo = algo, check = check)
end

#trivia... but was missing. Maybe move?
Hecke.valuation(a::FacElem{QQFieldElem, QQField}, p::ZZRingElem) = reduce(+, [v*valuation(k,p) for (k,v) = a], init = ZZRingElem(0))
Hecke.valuation(a::FacElem{QQFieldElem, QQField}, p::Integer) = reduce(+, [v*valuation(k,p) for (k,v) = a], init = ZZRingElem(0))

function Hecke.is_power(a::FacElem{QQFieldElem, QQField}, p::Int)
  b = simplify(a)
  K = QQFieldElem[]
  V = ZZRingElem[]
  for (k,v) = b
    if v % p == 0
      push!(K, k)
      push!(V, divexact(v, p))
    else
      fl, r = is_power(k, p)
      fl || return false, a
      push!(K, r)
      push!(V, v)
    end
  end
  return true, FacElem(QQ, K, V, parent = parent(a))
end

function pselmer_group(p::Int, S::Vector{ZZRingElem}; check::Bool = true, algo::Symbol = :raw)
  G, mp = pselmer_group_fac_elem(p, S, check = check, algo = algo)
  return G, MapFromFunc(G, QQ, x->evaluate(mp(x)), y->preimage(mp, FacElem(QQ, QQFieldElem[y], ZZRingElem[1], parent = codomain(mp))))
end
function pselmer_group(p::Int, S::Vector{<:Integer}; check::Bool = true, algo::Symbol = :raw)
  return pselmer_group(p, map(ZZRingElem, S), check = check, algo = algo)
end

export pselmer_group, pselmer_group_fac_elem

end # SelmerModule

using .SelmerModule
