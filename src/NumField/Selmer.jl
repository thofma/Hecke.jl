module SelmerModule
using Hecke

function Base.push!(C::GrpAbFinGen, a::GrpAbFinGenElem)
  g = gens(C)
  push!(g, a)
  #TODO: find common overgroup? Assuming for now that parent(a) is it.
  return sub(parent(a), g)
end

function index(G::GrpAbFinGen, U::GrpAbFinGen; check::Bool = true)
  return divexact(order(G), order(U))
end

function pselmer_group_fac_elem(p::Int, S::Vector{<:NfOrdIdl})
  @assert all(x->order(x) == order(S[1]), S)
  @assert isprime(p) #maybe not neccessary

  #TODO: need primes above p as well?
  ZK = order(S[1])
  K = number_field(ZK)

  C, mC = class_group(ZK)
  s, ms = sub(C, map(pseudo_inv(mC), S))
  P = PrimesSet(100, -1)
  pr, pos = iterate(P)
  D = NfOrdIdl[]
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
  @show mSel
  @show m
  mSel = mSel * pseudo_inv(m)

  #the forward map has a couple of possibilities:
  # - take any lift to k, map to U map to K
  # -                            U and when mapping to K, reduce exponents
  # -                                                     use comp. rep. 
  #
  # the backward map is more tricky, but the indirect route via 
  # class field theory (Frobenius) works for Magma - it should work here.

  function toK(x::GrpAbFinGenElem; algo::Symbol = :raw)
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

  disc_log_data = Dict{NfOrdIdl, Tuple{Map, Vector{Int}}}()
  function toSel(x::nf_elem; check::Bool = true)
    return toSel(FacElem([x], [1], check = check))
  end
  function toSel(x::FacElem{nf_elem, AnticNumberField}; check::Bool = true)
    if check
      A = ideal(ZK, x)
      for P = S
        A = A*FacElem([P//1], [-valuation(A, P)])
      end
      I = evaluate(A)
      I = simplify(I)
      fl, _ = is_power(numerator(I), p)
      fl || error("not in the image")
      fl, _ = is_power(denominator(I), p)
      fl || error("not in the image")
    end

    Fp = GF(p)
    dl = matrix(Fp, 0, ngens(Sel), [])
    dx = matrix(Fp, 0, 1, [])
    for (P, T) = disc_log_data
      v = T[1](x)[1]
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
        lp = prime_decomposition(ZK, pr)
        for (pi, ei) = lp
          F, mF = Hecke.ResidueFieldSmall(ZK, pi)
          u, mu = unit_group(F, n_quo = p)
          mF = Hecke.extend_easy(mF, K)
          va = [preimage(mu, mF(toK(g)))[1] for g = gens(Sel)]
          disc_log_data[pi] = (mF*pseudo_inv(mu), va)
          v = preimage(mu, mF(x))[1]
          dx = vcat(dx, matrix(Fp, 1, 1, [v]))
          dl = vcat(dl, matrix(Fp, 1, ngens(Sel), va))
        end
      end
      pr, pos = iterate(sp, pos)
    end
    fl, sol = Hecke.can_solve_with_solution(dl, dx)
    @assert fl
    return Sel(map(lift, vec(collect(sol))))
  end

  return Sel, MapFromFunc(toK, toSel, Sel, codomain(mU)) 
end

end # SelmerModule
