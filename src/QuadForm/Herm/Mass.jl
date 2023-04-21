export local_factor, local_mass

################################################################################
#
#  Local factor for dyadic primes
#
################################################################################

# Returns the local mass factor for dyadic primes
# The local scales must be 0 or 1
# Otherwise the function returns 0

function _local_factor_dyadic(L::HermLat, p)
  @assert is_dyadic(p)
  S = base_ring(L)
  E = nf(S)
  K = base_field(E)
  P = prime_decomposition(S, p)[1][1]
  valscale = valuation(scale(L), P)
  @assert valscale >= 0
  val = div(valscale, 2)
  if !iszero(val)
    s = elem_in_nf(uniformizer(p))
    L = rescale(L, s^(-val))
  end

  G = _genus_symbol_kirschmer(L, p)::Vector{Tuple{Int, Int, Bool, Int, elem_type(K)}}
  # I should check if I can get this from the standard genus symbol

  if !(issubset([g[2] for g in G], [0, 1]))
    return zero(QQFieldElem)
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
    return QQFieldElem(1, 2) * _gauss(k, k1, q^2)
  end

  e = valuation(discriminant(S), p)
  f2 = div(e, 2)
  d = (-1)^((m - 1) * k) * det(rational_span(L))
  # b <=> L \isom M \perp H0^* \perp H1^* where M is unimodular.
  b = (m1 == 0) || (m0 != 0 && G[1][4] != G[2][4])
  lf = QQFieldElem(1, 2) * _gauss(k, k0, q^2)
  l = div((b ? G[1][4] : G[end][4]), 2)

  if is_local_norm(E, d, p)
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
        return q^(m * (f2 - l) + k0) * (q^m1 - 1) * lf
      end
    else
      if iseven(e)
        return q^(m * (f2 - 1 - l) + k1) * (q^m0 - 1) * lf
      else
        return q^(m * (f2 - l ) - k0)    * (q^m0 - 1) * lf
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
      return (q^k1 - 1) * lf
    else
      return q^(m * (f2 - l) - k1) * (q^m1 - 1) * lf
    end
  end
  error("Impossible")
end

################################################################################
#
#  Local mass factor for maximal lattices
#
################################################################################

function _local_factor_maximal(L::HermLat, p)
  S = base_ring(L)
  E = nf(S)
  K = base_field(E)
  m = rank(L)
  lp = prime_decomposition(S, p)
  ram = length(lp) == 1 && lp[1][2] == 2
  if isodd(m) && ram
    return QQFieldElem(1, 2)
  end
  G = gram_matrix_of_rational_span(L)
  disc = _discriminant(G)
  if !is_local_norm(E, K(disc), p)
    q = norm(p)
    if ram
      return QQFieldElem(q^m - 1, 2*q + 2)
    else
      return QQFieldElem(q^m - (-1)^m, q + 1)
    end
  end
  return QQFieldElem(1)
end

################################################################################
#
#  Generic local mass factor
#
################################################################################

function _local_factor_generic(L::HermLat, p)
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

  ss = elem_in_nf(uniformizer(p))^(-val)

  if def
    R = base_ring(base_ring(L))
    rlp = real_embeddings(K)
    A::GrpAbFinGen, _exp, _log = sign_map(R, rlp, p)
    sa = ss * a
    t = (1 + _exp(A(Int[ sign(sa, rlp[j]) == 1 ? 0 : 1 for j in 1:length(rlp)]))::elem_type(R))
    @assert t - 1 in p
    @assert all(Bool[sign(t, rlp[i]) == sign(sa, rlp[i]) for i in 1:length(rlp)])
    ss = ss * t
  end
  L = rescale(L, ss)

  chain = typeof(L)[L]
  ok, LL = is_maximal_integral(L, p)
  while !ok
    push!(chain, LL)
    ok, LL = is_maximal_integral(LL, p)
  end
  f = _local_factor_maximal(L, p)
  for i in 1:(length(chain) - 1)
    M, E = maximal_sublattices(chain[i + 1], P, use_auto = def)
    lM = length(M)
    _f = 0
    for j in 1:lM
      if is_locally_isometric(chain[i], M[j], p)
        _f += E[j]
      end
    end

    f = f * _f
    M, E = minimal_superlattices(chain[i], P, use_auto = def)
    lM = length(M)
    _f = 0
    for j in 1:lM
      if is_locally_isometric(chain[i + 1], M[j], p)
        _f += E[j]
      end
    end
    f = divexact(f, _f)
  end
  return f
end

################################################################################
#
#  Local mass factor
#
################################################################################

@doc raw"""
    local_factor(L::HermLat, p::NfOrdIdl) -> QQFieldElem

Given a definite hermitian lattice `L` and a bad prime ideal `p` of `L`,
return the local density of `L` at `p`.
"""
function local_factor(L::HermLat, p)
  @req is_definite(L) "Lattice must be definite"
  S = base_ring(L)
  E = nf(S)
  K = base_field(E)
  q = norm(p)
  lp = prime_decomposition(S, p)
  ram = length(lp) == 1 && lp[1][2] == 2
  if ram && iseven(q) # p is dyadic and ramified
    if is_maximal(L,p)[1]
      return _local_factor_maximal(L, p)
    end
    lf = _local_factor_dyadic(L, p)
    # TODO: Use Cho's recipe if p unramified over Z.
    if iszero(lf)
      lf = _local_factor_generic(L, p)
      return lf
    end
    return lf
  end
  split = length(lp) > 1 && !ram
  _, G, s = jordan_decomposition(L, p)
  if length(s) == 1 && !ram
    return QQFieldElem(1)
  end

  m = rank(L)
  local f::QQFieldElem
  if ram
    f = QQFieldElem(group_order("Sp", 2 * div(m ,2), q))
  else
    f = QQFieldElem(group_order(split ? "GL" : "U", m, q))
  end

  d = ram ? 1 : 2
  N = zero(QQFieldElem)

  for i in 1:length(s)
    mi = ncols(G[i])
    ri = sum(Int[ncols(G[j]) for j in (i + 1):length(s)])
    if ram
      N = N - div(s[i], 2) * mi^2
      if isodd(s[i])
        N = N - (mi + 1) * div(mi, 2)
        f = divexact(f, group_order("Sp", mi, q))
      else
        det = K(_discriminant(G[i]))
        is_norm = is_local_norm(E, det, p)
        f = divexact(f, group_order(is_norm ? "O+" : "O-", mi, q))
      end
    else
      N = N - s[i] * mi^2
      f = divexact(f, group_order(split ? "GL" : "U", mi, q))
    end
    N = N - d * s[i] * mi * ri
    @assert mod(d * s[i] * mi * m, 2) == 0
    N = N + divexact(d * s[i] * mi * m, 2)
  end

  # Fix the difference coming from the discriminant
  if ram && iseven(m)
    N = N + div(m ,2)
  end

  return QQFieldElem(q)^(Int(FlintZZ(N))) * f
end

function _standard_mass(L::HermLat, prec::Int = 10)
  S = base_ring(L)
  E = nf(S)
  K = base_field(E)
  n = absolute_degree(K)
  m = rank(L)
  stdmass = QQFieldElem(2)^(1 - n * m)
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

################################################################################
#
#  Mass of hermitian lattices
#
################################################################################

@doc raw"""
    mass(L::HermLat) -> QQFieldElem

Given a definite hermitian lattice `L`, return the mass of its genus.
"""
function mass(L::HermLat)
  @req is_definite(L) "Lattice must be definite"
  m = rank(L)
  if m == 0
    return one(QQFieldElem)
  end

  lm = local_mass(L)

  prec = 10
  mu = _minkowski_multiple(absolute_simple_field(nf(base_ring(L)))[1], rank(L))

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

@doc raw"""
    local_mass(L::HermLat) -> QQFieldElem

Given a definite hermitian lattice `L`, return the product of its local
densities at the bad primes of `L`.
"""
function local_mass(L::HermLat)
  @req is_definite(L) "Lattice must be definite"
  lf = QQFieldElem(1)

  for p in bad_primes(L, discriminant = true)
    lf *= local_factor(L, p)
  end

  return lf
end


################################################################################
#
#  Misc
#
################################################################################

function _gauss(m, k, q)
  z = _gauss0(m, q)
  z = divexact(z, _gauss0(k, q))
  z = divexact(z, _gauss0(m - k, q))
  return z
end

function _gauss0(m, q)
  return QQFieldElem(prod(ZZRingElem[1 - q^i for i in 1:m]))
end

