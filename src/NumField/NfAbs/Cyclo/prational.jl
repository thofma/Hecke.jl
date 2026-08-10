module pRationalCyclotomic

using ..Hecke

import ..Hecke.pRational:
  _schirokauer_map_data_generic,
  _schirokauer_map_data_minkowski_unit,
  _create_eta_map,
  _pick_automorphisms,
  _random_cyclic_subgroup

import ..Hecke.KimGoldBases:
  _sinnott_g

mutable struct pRationalityTestCtx
  k::AbsSimpleNumField
  ok::AbsSimpleNumFieldOrder
  n::Int # conductor
  mink
  strongminkowski::Bool
  aut
  cyc::Vector{AbsSimpleNumFieldElem}
  cycmC::MapFromFunc{FinGenAbGroup, FacElemMon{AbsSimpleNumField}} # unit group map
  subfields::Vector{AbsSimpleNumField}
  subfield_class_number::IdDict{AbsSimpleNumField, ZZRingElem}

  pRationalityTestCtx() = new()
end

degree(k) = Hecke.degree(k)

function degree(T::pRationalityTestCtx)
  return Hecke.degree(T.k)
end

function pRationalityTestCtx(n::Int)
  T = pRationalityTestCtx()
  T.n = n
  k, = cyclotomic_real_subfield(n)
  T.k = k
  T.ok = lll(maximal_order(k))
  @vprint :pRationality 1 "conductor: $n: computing cyclotomic units\n"
  cyc = cyclotomic_units_totally_real(k; conductor = n)
  T.cyc = cyc
  # triger automorphism group computation
  autfull = automorphism_list(k; is_abelian = true)
  aut = _pick_automorphisms(k; is_abelian = true)
  T.aut = aut
  @vprint :pRationality 1 "conductor: $n: computing (weak) Minkowski unit\n"
  if Hecke.is_prime_power(n) && is_odd(n)
    u = _cyclotomic_units_totally_real_prime_power_conductor(k, n)
    T.strongminkowski = true
    T.mink = u
  else
    @vprint :pRationality 1 "conductor: $n: computing (weak) Minkowski unit\n"
    u = _random_cyclic_subgroup(k, aut, cyc)
    T.strongminkowski = false
    T.mink = u
  end

  T.subfield_class_number = IdDict{AbsSimpleNumField, ZZRingElem}()
  return T
end

function _p_rationality_of_real_cyclotomic_quick_check_at_2(T)
  n = T.n
  nps = prime_divisors(n)
  if n == 2^valuation(n, 2) || n == 2^valuation(n, 2) * 3 || n == 2^valuation(n, 2) * 5
    return true
  end
  if any(l -> mod(l, 8) == 1, nps)
    return false
  end
  if any(l -> mod(l, 8) == 7 && mod(n, 4l) == 0, nps)
    return false
  end
  if !allunique([mod(l, 4) for l in nps if l > 2])
    return false
  end
  if _sinnott_g(n) >= 3
    return false
  end
  if length(prime_ideals_over(maximal_order(T.k), 2)) > 1
    return false
  end
  return nothing
end

# per prime version
function _p_rationality_of_real_cyclotomic_check_per_prime(T, p)
  n = T.n

  if p == 2
    @vprint :pRationality 1 "conductor: $n: prime $p: quick check for n = $(factor(n))\n"
    fl = _p_rationality_of_real_cyclotomic_quick_check_at_2(T)
    @vprint :pRationality 1 "conductor: $n: prime $p: quick check at 2: $fl\n"
    if fl isa Bool
      return fl
    end
  end

  @vprint :pRationality 1 "conductor: $n: prime $p: check Schirokauer map on cyclotomic units\n"
  if !is_divisible_by(2*n, p)
    fl, = _schirokauer_map_data_minkowski_unit(T.k, T.mink, p, T.aut; is_abelian = true, new = true)
    if fl
      @vprint :pRationality 1 "conductor: $n: prime $p: Schirokauer map injective; p-rationality established\n"
      return true
    end
    @vprint :pRationality 1 "conductor: $n: prime $p: p does not divide (2*n)\n"
    if T.strongminkowski
      return false
    end
    fl, = _schirokauer_map_data_generic(T.k, T.cyc, p)
    return fl
  end

  return _is_prational_cyclotomic_via_eta_map(T, p)
end

function _is_prational_cyclotomic_via_eta_map(T, p)
  k = T.k
  n = T.n
  @vprint :pRationality 1 "conductor: $n: prime $p\n"
  ok = lll(maximal_order(k))
  # we need to check the condition on the p-th roots of unity
  if mod(2*n, p) == 0
    # p divides 2 * d_K
    if p == 2
      g = length(prime_ideals_over(ok, 2))
      @vprint :pRationality 1 "conductor: $n: prime $p: number of primes above 2: $g\n"
      if g > 1
        @vprint :pRationality 1 "conductor: $n: prime $p: returning false\n"
        return false
      end
    else
      @vprint :pRationality 1 "conductor: $n: prime $p: check splitting of p in Q(z_n)|Q(z_n)^+\n"
      # need to look at K(zeta_p)|K = Q(zeta_n)|Q(zeta_n)^+, a quadratic extension
      K, = cyclotomic_field(n; cached = false)
      g = length(prime_decomposition_type(ok, p)) # g primes over p in Q(zeta_n)^+
      gg = length(prime_decomposition_type(maximal_order(K), p)) # gg primes over p in Q(zeta_n)
      @vprint :pRationality 1 "conductor: $n: prime $p: number of primes above of p in Q(z_n)^+: $g\n"
      @vprint :pRationality 1 "conductor: $n: prime $p: number of primes above of p in Q(z_n): $gg\n"
      if gg > g
        @assert gg == 2 * g
        @vprint :pRationality 1 "conductor: $n: prime $p: returning false\n"
        # the primes are totally split
        return false
      end
    end
  end
  # p does not divide 2*n, so condition (b) is satisfied
  # we just check if the eta map on C/C^p is injective
  @vprint :pRationality 1 "conductor: $n: prime $p: creating eta map\n"
  U, f = _create_eta_map(k, p)
  prankcyclo = p == 2 ? degree(k) - 1 + 1 : degree(k) - 1
  u = FacElem.(T.cyc)
  @vprint :pRationality 1 "conductor: $n: prime $p: computing image of cyclotomic units\n"
  V, = sub(U, f.(u))
  r = rank(V, p)
  @vprint :pRationality 1 "conductor: $n: prime $p: p-rank is $r (cyclotomic units have p-rank $prankcyclo)\n"
  @vprint :pRationality 1 "conductor: $n: prime $p: returning $(r == prankcyclo)\n"
  return r == prankcyclo
end

@doc raw"""
    is_real_cyclotomic_field_p_rational(n::Int, p; GRH::Bool = false)

Return whether the maximal real subfield of the cyclotomic field of conductor
$n$ is $p$-rational at $p$.

See also [`is_quasi_p_rational`](@ref) and [`is_p_rational`](@ref) for versions
that work for any number field.

# Examples

```jldoctest
julia> is_real_cyclotomic_field_p_rational(15, 13)
false
```
"""
function is_real_cyclotomic_field_p_rational(n, p)
  T = pRationalityTestCtx(n)
  return _p_rationality_of_real_cyclotomic_check_per_prime(T, p)
end

function _cyclotomic_units_totally_real_prime_power_conductor(K, q)
  Zx = Hecke.Globals.Zx
  x = gen(Zx)
  @assert is_zero(cos_minpoly(q, gen(Zx))(gen(K)))
  xi = gen(K)

  # Schoof, "Class numbers of real cyclotomic fields of prime conductor", Section 2
  # gives the following formula:
  # eta = zeta^(g) - zeta^(-g)/zeta - zeta^-1 = sin(2pi g/n)/sin(2p/n) = U_{g - 1}(cos(2pi/n))
  # then Cyc is generated by the G-orbit of eta,
  # where G = Gal(K/Q).
  # This is slightly different from Washington, who takes sin(pi g/n)(sin(2pi/n)
  # but they differ only by a choice of primitive root of unity. If you take z' with z'^2 = z
  # in Washington, you get Schoofs unit.

  @assert Hecke.is_prime_power(q)

  U, mU = unit_group(residue_ring(ZZ, q, cached = false)[1])
  @assert ngens(U) == 1
  g = Int(lift(mU(U[1])))


  p1 = numerator(chebyshev_u(g - 1, x)(x//2))
  eta = p1(xi)
  return eta
end

# p-rationality check for fixed field

function _check_prationality_of_cyclotomic_units_up_to(n, bound, callback = nothing)
  T = pRationalityTestCtx(n)
  res = Int[]
  for (i, ell) in enumerate(PrimesSet(2, bound))
    if !(callback isa Nothing)
      callback(i, ell, res)
    end
    fl = _p_rationality_of_real_cyclotomic_check_per_prime(T, ell)
    if fl
      continue
    end
    push!(res, ell)
  end
  return res
end

end

import .pRationalCyclotomic:
  is_real_cyclotomic_field_p_rational,
  _check_prationality_of_cyclotomic_units_up_to
