
###############################################################################
#### AbstractAlgebra overrides ################################################

function _doit(a::Generic.MPoly{<:NumFieldElem}, fxn::Function)
  k = base_ring(a)
  ks, ms = absolute_simple_field(k)
  lf = fxn(map_coefficients(pseudo_inv(ms), a, cached = false))
  return Fac(map_coefficients(ms, unit(lf), parent = parent(a)), Dict(map_coefficients(ms, k, parent = parent(a)) => v for (k,v) = lf.fac))
end

function AbstractAlgebra.factor(a::Generic.MPoly{<:NumFieldElem})
  return _doit(a, factor)
end

function AbstractAlgebra.factor(a::Generic.MPoly{AbsSimpleNumFieldElem})
  return AbstractAlgebra.MPolyFactor.mfactor_char_zero(a)
end

function AbstractAlgebra.factor_squarefree(a::Generic.MPoly{AbsSimpleNumFieldElem})
  return AbstractAlgebra.MPolyFactor.mfactor_squarefree_char_zero(a)
end

function AbstractAlgebra.factor_squarefree(a::Generic.MPoly{<:NumFieldElem})
  return _doit(a, factor_squarefree)
end

function AbstractAlgebra.MPolyFactor.mfactor_choose_eval_points!(
  alphas::Vector,
  A::E,
  mainvar::Int,
  minorvars::Vector{Int},
  size::Int) where E <: Generic.MPoly{AbsSimpleNumFieldElem}

  n = length(minorvars)
  R = parent(A)
  K = base_ring(R)
  d = degree(K)

  size = clamp(size, 2, 100)

  for i in 1:n
    # choose integers for now
    zero!(alphas[i])
    Hecke.set_den!(alphas[i], one(ZZ))
    for j in 0:0
      Hecke.set_num_coeff!(alphas[i], j, rand_bits(ZZ, 2 + rand(0:size)))
    end
  end
end

function AbstractAlgebra.MPolyFactor.hlift_have_lcs(
  A::E,
  Auf::Vector{E},       # univariate factorization in mainvar
  lcs::Vector{E},       # lead coeffs of factors
  mainvar::Int,
  minorvars::Vector{Int},   # length n
  alphas::Vector
) where E <: Generic.MPoly{AbsSimpleNumFieldElem}

  return hlift_have_lcs_generic(A, Auf, lcs, mainvar, minorvars, alphas)
#  return hlift_have_lcs_crt(A, Auf, lcs, mainvar, minorvars, alphas)
end

###############################################################################
#### implementation ###########################################################

#### the original generic method using AbsSimpleNumFieldElem arithmetic #####################

function hlift_have_lcs_generic(
  A::E,                 # lead coeff should equal prod(lcs)
  Auf::Vector{E},       # univariate factorization in mainvar
  lcs::Vector{E},       # lead coeffs of factors
  mainvar::Int,
  minorvars::Vector{Int},   # length n
  alphas::Vector
) where E <: Generic.MPoly{AbsSimpleNumFieldElem}

  R = parent(A)
  K = base_ring(R)
  n = length(minorvars)
  r = length(Auf)
  @assert n > 0
  @assert r > 1

  lc_evals = zeros(R, n + 1, r)
  for j in 1:r
    lc_evals[n + 1, j] = lcs[j]
    for i in n:-1:1
      lc_evals[i, j] = AbstractAlgebra.MPolyFactor.eval_one(lc_evals[i + 1, j],
                                                       minorvars[i], alphas[i])
    end
  end

  A_evals = zeros(R, n + 1)
  A_evals[n + 1] = A
  for i in n:-1:1
    A_evals[i] = AbstractAlgebra.MPolyFactor.eval_one(A_evals[i + 1],
                                                       minorvars[i], alphas[i])
  end

  fac = zeros(R, r)
  for j in 1:r
    @assert is_constant(lc_evals[1, j])
    fac[j] = Auf[j]*divexact(lc_evals[1, j],
                           AbstractAlgebra.MPolyFactor.get_lc(Auf[j], mainvar))
  end

  tdegs = degrees(A_evals[n + 1])
  liftdegs = [tdegs[minorvars[i]] for i in 1:n]

  for i in 2:n+1
    tfac = [AbstractAlgebra.MPolyFactor.set_lc(fac[j],
                                         mainvar, lc_evals[i, j]) for j in 1:r]

    ok, fac = AbstractAlgebra.MPolyFactor.hliftstep(tfac, mainvar,
                          minorvars[1:i-1], liftdegs, alphas, A_evals[i], true)
    if !ok
      return false, fac
    end
  end

  return true, fac
end

#### modular approach #########################################################

function nf_elem_split(a::AbsSimpleNumFieldElem)
  den = denominator(a)
  num = Hecke.Globals.Zx(parent(defining_polynomial(parent(a)))(a)*den)
  return num, den
end

#=
  Theorem 6.2 in Martin Lee's thesis
  return (lcc::ZZRingElem, bits::Int) such that for any monic divisor g of A:
    lcc*g is in Z[alpha][x1,x2,...]
    height(lcc*g) <= 2^bits
=#
function mfactor_martin_bounds(A::Generic.MPoly{AbsSimpleNumFieldElem})
  R = parent(A)
  K = base_ring(R)
  Alen = length(A)
  @assert Alen > 0

  # mu in Z[alpha] is the defining polynomial
  mu = defining_polynomial(K)
  mu = Hecke.Globals.Zx(denominator(mu) * mu)

  # define f to be scale*A so that f in Z[alpha][X,x1,...,xn]
  # f will not be computed explicitly - we only need height(f) and leading_coefficient(f)
  leadf, scale1 = nf_elem_split(coeff(A, 1))
  heightf = height(leadf)
  scale = scale1
  for i in 2:Alen
    num, den = nf_elem_split(coeff(A, i))
    g = gcd(scale, den)
    den = divexact(den, g)
    heightf = max(heightf*den, height(num)*divexact(scale, g))
    scale *= den
  end
  leadf *= divexact(scale, scale1)

  # factors will be reconstructed with leading coeff df*D
  df = resultant(mu, leadf)
  D = resultant(mu, derivative(mu))

  degs = degrees(A)
  prod_degs = prod(ZZRingElem(i) + 1 for i in degs)
  sum_degs = sum(ZZRingElem(i) for i in degs)
  s = sum(i > 0 ? 1 : 0 for i in degs)  # count of present variables
  k = ZZRingElem(degree(mu))
  bits = sum_degs + k + nbits(prod_degs)
  bits += cdiv(k*nbits(cdiv((k + 1)^7*heightf^2*height(mu)^8, leading_coefficient(mu)^2)) - s, 2)

  return (df*D, Int(bits))
end

function is_pairwise_coprime(v::Vector{E}) where E
  n = length(v)
  for i in 1:n-1, j in i+1:n
    if !isone(gcd(v[i],v[j]))
      return false
    end
  end
  return true
end

function hlift_have_lcs_crt(
  A::E,
  Auf::Vector{E},       # univariate factorization in mainvar
  lcs::Vector{E},       # lead coeffs of factors
  mainvar::Int,
  minorvars::Vector{Int},   # length n
  alphas::Vector
) where E <: Generic.MPoly{AbsSimpleNumFieldElem}

  R = parent(A)
  K = base_ring(R)
  n = length(minorvars)
  r = length(Auf)
  @assert n > 0
  @assert r > 1

  nf_lcc, bits = mfactor_martin_bounds(A)

  m = ZZRingElem(1)
  Af = zeros(R, r)

  for p in PrimesSet(Hecke.p_start, -1)

    local pA, pAuf, plcs, palphas

    if is_divisible_by(nf_lcc, p)
        continue
    end

    me = Hecke.modular_init(K, p)
    s = length(me.fld)

    try
      pA = modular_proj(fqPolyRepFieldElem, A, me)

      # make sure no leading coeff vanishes
      plcs = [modular_proj(fqPolyRepFieldElem, lc, me) for lc in lcs]
      plcs = [[plcs[j][i] for j in 1:r] for i in 1:s]
      ok = true
      for i in 1:s, j in 1:r
        ok = ok && !iszero(plcs[i][j])
      end
      if !ok
        continue
      end

      # make sure univariate factorizations remain pairwise prime
      pAuf = [modular_proj(fqPolyRepFieldElem, f, me) for f in Auf]
      pAuf = [[pAuf[j][i] for j in 1:r] for i in 1:s]
      ok = true
      for i in 1:s
        ok = ok && is_pairwise_coprime(pAuf[i])
      end
      if !ok
        continue
      end

      palphas = [deepcopy(Hecke.modular_proj(alphas[j], me)) for j in 1:n]
      palphas = [[palphas[j][i] for j in 1:n] for i in 1:s]

    catch ee
      if ee <: Hecke.BadPrime
        continue
      end
      rethrow(ee)
    end

    pAf = [eltype(pA)[] for j in 1:r]
    for i in 1:s
      ok, t = AbstractAlgebra.MPolyFactor.hlift_have_lcs(
                       pA[i], pAuf[i], plcs[i], mainvar, minorvars, palphas[i])
      if !ok
        return false
      end

      for j in 1:r
        push!(pAf[j], (nf_lcc*inv(leading_coefficient(t[j]))*t[j]))
      end
    end

    for j in 1:r
      t = modular_lift(pAf[j], me)
      Af[j] = Hecke.induce_crt(Af[j], m, t, ZZRingElem(p), true)[1]
    end
    m *= p

    if nbits(m) > bits + 1
      break
    end
  end

  # scale the Af[j] to match the given lcs if possible
  for j in 1:r
    ok, c = divides(lcs[j], AbstractAlgebra.MPolyFactor.get_lc(Af[j], mainvar))
    if !ok || !is_constant(c)
      return false
    end
    Af[j] *= c
  end

  ok = (A == prod(f for f in Af))
  return ok, Af
end

