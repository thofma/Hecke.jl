function _gauss(m, k, q)
  z = _gauss0(m, q)
  z = divexact(z, _gauss0(k, q))
  z = divexact(z, _gauss0(m - k, q))
  return z
end

function _gauss0(m, q)
  return fmpq(prod(fmpz[1 - q^i for i in 1:m]))
end

function local_factor_even(L::HermLat, p)
  S = base_ring(L)
  E = nf(S)
  K = base_field(nf(S))
  P = prime_decomposition(S, p)[1][1]
  valscale = valuation(scale(L), P)
  @assert valscale >= 0
  val = div(valscale, 2)
  if !iszero(val )
    s = elem_in_nf(uniformizer(p))
    L = rescale(L, s^(-val))
  end

  G = _genus_symbol_kirschmer(L, p)::Vector{Tuple{Int, Int, Bool, Int, elem_type(K)}}
  # I should check if I can get this from the standard genus symbol

  if !(issubset([g[2] for g in G], [0, 1]))
    return zero(fmpq)
  end

  m0 = G[1][2] == 0 ? G[1][1] : 0
  m1 = G[end][2] == 1 ? G[end][1] : 0

  q = norm(p)
  m = m0 + m1
  @assert iseven(m1)
  @assert m >= 0
  @assert m0 >= 0
  @assert m1 >= 0
  k = div(m, 2)
  k0 = div(m0, 2)
  k1 = div(m1, 2)

  if isodd(m)
    return fmpq(1, 2) * _gauss(k, k1, q^2)
  end

  e = valuation(discriminant(S), p)
  f2 = div(e, 2)
  d = (-1)^((m - 1) * k) * det(rational_span(L))
  # b <=> L \isom M \perp H0^* \perp H1^* where M is unimodular.
  b = m1 == 0 || (m0 != 0 && G[1][1] != G[2][4])
  lf = fmpq(1, 2) * _gauss(k, k0, q^2)
  l = div((b ? G[1][4] : G[end][4]), 2)

  if islocal_norm(E, d, p)
    h0 = m0 == 0 || G[1][4] == 2 * f2
    h1 = m1 == 0 || G[end][4] == 2 * div(e + 1, 2)
    # L_p = H(0)^k0 \perp H(1)^k1
    if h0 && h1
      t = iseven(e) ? k1 : k0
      return (q^t + 1) * lf
    end
    
    if !b
      if iseven(e)
        return q^(m * (f2 - l) - k1) * (q^m1 - 1) * lf
      else
        return q^(m * (f2 - l) - k0) * (q^m1 - 1) * lf
      end
    else
      if iseven(e)
        return q^(m * (f2 - 1 - l) + k1) * (q^m0 - 1) * lf
      else
        return q^(m * (f2 - 1 ) - k0)    * (q^m0 - 1) * lf
      end
    end
  else # non-hyperbolic case
    if isodd(e)
      if b && l == div(e - 1, 2)
        return (q^k0 - 1) * lf
      elseif b
        return q^(m * (f2 - l) - k0) * (q^m0 - 1) * lf
      else
        return q^(m * (f2 - l) + k0) * (q^m1 - 1) * lf
      end
    end

    if b
      return q^(m * (f2 - 1 - l) + k1) * (q^m0 - 1) * lf
    elseif l == div(e, 2) # e is even
      return q^(k1 - 1) * lf
    else
      return q^(m * (f2 - l) - k1) * (q^m1 - 1) * lf
    end
  end
  throw(error("Impossible"))
end

function local_factor_maximal(L::HermLat, p)
  S = base_ring(L)
  m = rank(L)
  lp = prime_decomposition(S, p)
  ram = length(lp) == 1 && lp[1][2] == 2
  if isodd(m) && ram
    return fmpq(1, 2)
  end
  G = gram_matrix_of_basis(L)
  disc = _discriminant(G)
  if !islocal_norm(S, disc, p)
    q = norm(p)
    if ram
      return fmpq(q^m - 1, 2*q + 2)
    else
      return fmpq(q^m - (-1)^m, q + 1)
    end
  end
  return fmpq(1)
end

function local_factor_generic(L::HermLat, p)
  K = fixed_field(L)
  a = _isdefinite(rational_span(L))
  def = !iszero(a)
  S = base_ring(L)
  lp = prime_decomposition(S, p)
  P = lp[1][1]
  val = valuation(norm(L) * S, P)
  if length(lp) == 1 && lp[1][2] == 2
    @assert val >= 0
    val = div(val, 2)
  end

  ss = uniformizer(p)^(-val)

  if def
    R = base_ring(base_ring(L))
    rlp = real_places(K)
    A::GrpAbFinGen, _exp, _log = infinite_primes_map(R, rlp, p)
    sa = ss * a
    t = (1 + _exp(A(Int[ sign(sa, rlp[j]) == 1 ? 0 : 1 for j in 1:length(rlp)]))::elem_type(R))
    @assert t - 1 in p
    @assert all(Bool[sign(t, rlp[i]) == sign(sa, rlp[i]) for i in 1:length(rlp)])
    ss = ss * t
  end
  L = rescale(L, ss)

  chain = typeof(L)[L]
  ok, LL = ismaximal_integral(L, p)
  @time while !ok
    push!(chain, LL)
    ok, LL = ismaximal_integral(LL, p)
  end
  f = local_factor_maximal(L, p)
  @time for i in 1:(length(chain) - 1)
    M, E = maximal_sublattices(chain[i + 1], P, use_auto = false)# should be use_auto = def)
    f = f * sum(Int[E[j] for j in 1:length(M) if islocally_isometric(chain[i], M[j], p)])
    M, E = minimal_superlattices(chain[i], P, use_auto = false)# should be use_auto = def)
    f = divexact(f, sum(Int[E[j] for j in 1:length(M) if islocally_isometric(chain[i + 1], M[j], p)]))
  end
  return f
end

function local_mass_factor(L::HermLat, p)
  S = base_ring(L)
  E = nf(S)
  K = base_field(E)
  q = norm(p)
  lp = prime_decomposition(S, p)
  ram = length(lp) == 1 && lp[1][2] == 2
  @show ram
  if ram && isdyadic(p)
    lf = local_factor_even(L, p)
    # TODO: Use Cho's recipe if p unramified over Z.
    if iszero(lf)
      lf = local_factor_generic(L, p)
      return lf
    end
    return lf
  end
  lp = prime_decomposition(S, p)
  split = length(lp) > 1 && !ram
  _, G, s = jordan_decomposition(L, p)
  if length(s) == 1 && !ram
    return fmpq(1)
  end
  
  m = rank(L)
  local f::fmpq
  if ram
    @show "Sp", 2 * div(m, 2), q
    f = fmpq(group_order("Sp", 2 * div(m ,2), q))
  else
    f = fmpq(group_order(split ? "GL" : "U", m, q))
  end

  @show f

  d = ram ? 1 : 2
  N = zero(fmpq)

  @show length(s), ram

  for i in 1:length(s)
    mi = ncols(G[i])
    ri = sum(Int[ncols(G[j]) for j in (i + 1):length(s)])
    @show i, mi, ri
    if ram
      N = N - div(s[i], 2) * mi^2
      if isodd(s[i])
        N = N - (mi + 1) * div(mi, 2)
        f = divexact(f, group_order("Sp", mi, q))
      else
        det = K(_discriminant(G[i]))
        isnorm = islocal_norm(E, det, p)
        f = divexact(f, group_order(isnorm ? "O+" : "O-", mi, q))
      end
    else
      N = N - s[i] * mi^2
      f = divexact(f, group_order(split ? "GL" : "U", mi, q))
    end
    N = N - d * s[i] * mi * ri
    @show i, N
    @assert mod(d * s[i] * mi * m, 2) == 0
    N = N + divexact(d * s[i] * mi * m, 2)
    @show i, N
  end

  # Fix the difference coming from the discriminant
  if ram && iseven(m)
    N = N + div(m ,2)
  end

  @show N, f

  return q^(Int(FlintZZ(N))) * f
end

function _standard_mass(L::HermLat, prec::Int = 10)
  S = base_ring(L)
  E = nf(S)
  K = base_field(E)
  n = absolute_degree(K)
  m = rank(L)
  stdmass = fmpq(2)^(1 - n * m)
  # K is totally real, so I can get the exact value "cheaply"
  for i in 2:2:m
    stdmass = stdmass * dedekind_zeta_exact(K, 1 - i)
  end

  wprec = 2 * prec

  RR = ArbField(wprec, cached = false)
  _stdmass = RR(stdmass)
  
  local relzeta::arb

  while true
    relzeta = prod(arb[_L_function(E, 1 - i, wprec) for i in 1:2:m])
    if radiuslttwopower(relzeta * _stdmass, -prec)
      break
    end
    wprec = wprec + 1
  end
  return _stdmass * relzeta
end

function mass(L::HermLat)
  @req isdefinite(L) "Lattice must be definite"
  m = rank(L)
  if m == 0
    return one(fmpq)
  end

  lm = local_mass(L)

  prec = 10
  mu = _minkowski_multiple(absolute_field(nf(base_ring(L)))[1], rank(L))

  d = mu * numerator(lm)

  while true
    z = d * _standard_mass(L, prec)
    fl, b = unique_integer(z)
    if fl
      return abs(b)//d * lm
    end
    prec += 2
  end
end

function local_mass(L::HermLat)
  lf = fmpq(1)

  for p in bad_primes(L, discriminant = true)
    #@show minimum(p), local_mass_factor(L, p)
    lf *= local_mass_factor(L, p)
  end

  return lf
end

