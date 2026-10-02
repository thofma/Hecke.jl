# Gold, Kim, "Bases for cyclotomic units"

module KimGoldBases

using ..Hecke

struct KimGoldStruct
  n::Int
  ps::Vector{Int}
  es::Vector{Int}
  sigmaitilde::Vector{Int}
end

function KimGoldStruct(n::Union{ZZRingElem, Integer})
  f = factor(n)
  ps = collect(p for (p,_) in f)
  sort!(ps)
  es = [valuation(n, p) for p in ps]
  sigmaitilde = [ (@__MODULE__).sigmaitilde(n, ps[i], es[i]) for i in 1:length(ps)]
  return KimGoldStruct(n, ps, es, sigmaitilde)
end

ppower(K::KimGoldStruct, i) = K.ps[i]^K.es[i]

r(K::KimGoldStruct) = length(K.ps)

sigmaitilde(K::KimGoldStruct, i) = K.sigmaitilde[i]

function sigmaitilde(n, p, e)
  ppow = p^e
  if p != 2
    R, = residue_ring(ZZ, ppow)
    U, mU = unit_group(R)
    @assert ngens(U) == 1
    l = lift(mU(U[1])) % n
    i = 0
    while true
      if mod(l* ppow - ppow, n) == 0
        return l
      end
      l += ppow
    end
  else
    tau = -1 % ppow
    R, = residue_ring(ZZ, ppow)
    U, mU = unit_group(R)
    a = rand(U)
    # U = Z/2^(e - 2) x Z/2Z
    # we want a to be an element of order 2^(e - 2)
    # which should be distinct from 1,-1 if e >= 3
    while order(a) != 2^(e - 2) || (e >= 3 && (lift(mU(a)) in [1, ppow - 1])) # not -1
      a = rand(U)
    end
    l = (lift(mU(a)) + n) % n
    while true
      if mod(l* ppow - ppow, n) == 0
        return l
      end
      l += ppow
    end
    return l
  end
end

function sigma_i_k(KG, i, k = 1)
  n = KG.n
  ppow = KG.ps[i]^KG.es[i]
  e = KG.es[i]
  sigmaitilde = (@__MODULE__).sigmaitilde(KG, i)
  if KG.ps[i] != 2
    return powermod(sigmaitilde, k, n)
  else
    tau = -1 % ppow
    R, = residue_ring(ZZ, ppow)
    U, mU = unit_group(R)
    if k < 2^(e - 2)
      l = powermod(sigmaitilde, k, n)
    else
      l = (powermod(sigmaitilde, k, n) * tau) % n
    end
    while true
      if mod(l* ppow - ppow, n) == 0
        break
      end
      l += ppow
    end
    @assert mod(l* ppow - ppow, n) == 0
    return l
  end
end

function In(K)
  c = [0:euler_phi(ppower(K, i)) - 1 for i in 1:r(K)-1]
  push!(c, 0:divexact(euler_phi(ppower(K, r(K))), 2) - 1)
  cc = collect(Hecke.cartesian_product_iterator(c; inplace = false))
end

function Inp(K)
  res = Vector{Int}[]
  for x in In(K)
    if is_good(x, K)
      push!(res, x)
    end
  end
  @assert length(res) == divexact(prod(euler_phi(ppower(K, i)) - 1 for i in 1:r(K)) + 1, 2)
  return res
end

function is_good(x, K)
  r = (@__MODULE__).r(K)
  if x[r] != 0 && all(i -> x[i] != 0, 1:r-1)
    return true
  end

  for i in 0:r-2
    if all(j -> x[j] == 0, r:-1:r-i) && 1 <= x[r - i - 1] <= divexact(euler_phi(ppower(K, r - i - 1)), 2) - 1 && all(j -> x[j] != 0, 1:r-i-2)
      return true
    end
  end
  if all(iszero, x)
    return true
  end
  return false
end

function Inpp(K)
  I = Inp(K)
  if is_even(r(K))
    return I
  else
    i = findfirst(isequal(fill(0, r(K))), I)
    deleteat!(I, 1)
    return I
  end
end

function Tntilde(n)
  return [(n, Inpp(KimGoldStruct(n)))]
end

function Tntildep(n)
  res = []
  for d in Divisors(n)
    if d == 1 || d == n
      continue
    end
    if gcd(d, divexact(n, d)) != 1
      continue
    end
    append!(res, Tntilde(d))
  end
  res
end

function gtilde(K, norig, n, a)
  if Hecke.is_prime_power(n)
    return g(K, norig, n, a)/g(K, norig, n, 1)
  else
    return g(K, norig, n, a)
  end
end

function g(K, norig, n, a)
  znorig = gen(K)
  zn = znorig^divexact(norig, n)
  # aa is n-th root of unity
  return 1 - zn^a
end

function _cyclotomic_units(K, n)
  res = elem_type(K)[]
  for (d, v) in vcat(Tntilde(n), Tntildep(n))
    KG = KimGoldStruct(d)
    for is in v
      push!(res, gtilde(K, n, d, prod(sigma_i_k(KG, i, is[i]) for i in 1:r(KG))))
    end
  end
  res
end

function _sinnott_g(n)
  g = length(factor(n))
  return g
end

function _sinnott_factor(n)
  g = length(factor(n))
  if g == 1
    return 2^0
  else
    return 2^(2^(g - 2) + 1 - g)
  end
end

#

function _cyclotomic_units_totally_real_generic_with_conductor(k, n)
  @assert 2*degree(k) == euler_phi(n)
  K, = cyclotomic_field(n)
  i = hom(k, K, gen(K) + inv(gen(K)))
  cyc = _cyclotomic_units(K, n)
  _cyc = copy(cyc)
  rcyc = p -> ldexp(regulator(_cyc, p), -Hecke.unit_group_rank(K))
  pushfirst!(cyc, -gen(K)) # See Gold-Kim
  #A = free_abelian_group(length(cyc))
  B, f = torsion_unit_group(K)
  A = abelian_group(reverse!(push!([0 for i in 1:length(cyc) - 1], Hecke.torsion_unit_order(-gen(K), 2*n))))
  #h = hom(A, B, [preimage(f, cyc[i]/conj(cyc[i])) for i in 1:length(cyc)])
  h = hom(A, B, [preimage(f, cyc[i]/conj(cyc[i])) for i in 1:length(cyc)])
  C, CtoA = kernel(h)
  #CC, CCtoA = kernel(hh)
  @assert elementary_divisors(C) == append!([2], [0 for i in 1:degree(k)-1])
  lllm = lll(reduce(vcat, ((x -> x.coeff).(CtoA.(gens(C))))))
  res = elem_type(k)[]
  @assert length(cyc) == ncols(lllm)
  for j in 1:nrows(lllm)
    fl, x = has_preimage_with_preimage(i, prod(cyc[i]^lllm[j, i] for i in 1:ncols(lllm)))
    @assert fl
    push!(res, x)
  end
  return res, rcyc
end

export _cyclotomic_units_totally_real_generic_with_conductor

end

import .KimGoldBases:
  _cyclotomic_units_totally_real_generic_with_conductor
