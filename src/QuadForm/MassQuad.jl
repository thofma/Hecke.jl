export mass

################################################################################
#
#  Local factor of a maximal lattice in K*L following Shimura and Gan-Hanke-Yu.
#
################################################################################

function _local_factor_maximal(L, p)
  m = rank(L)
  r = div(m, 2)
  if m == 1
    return QQFieldElem(1)
  end

  w = witt_invariant(L, p)
  d = discriminant(ambient_space(L))
  q = norm(p)

  if isodd(m)
    if isodd(valuation(d, p))
      return QQFieldElem(q^r + w, 2)
    elseif w == -1 && iseven(valuation(d, p))
      return divexact(QQFieldElem(q^(m-1) -1, q + 1), 2)
    end
  else
    if isodd(valuation(d, p))
      # ram
      return QQFieldElem(1,2)
    elseif is_local_square(d, p)
      # split
      if w == -1
        return divexact(QQFieldElem((q^(r -1) - 1) * (q^r - 1), q + 1), 2)
      end
    elseif isodd(quadratic_defect(d, p))
      # ram
      return QQFieldElem(1, 2)
    else
      if w == -1
        return divexact(QQFieldElem((q^(r -1) + 1) * (q^r + 1), q + 1), 2)
      end
    end
  end
  return QQFieldElem(1)
end

_get_eps(::PosInf) = 1

_get_eps(::Any) = -1

################################################################################
#
#  Local factor of a unimodular lattice
#
################################################################################

function _local_factor_unimodular(L::QuadLat, p)
  local s::Vector{Int}
  local G::Vector{dense_matrix_type(nf(base_ring(L)))}
  d, s, w, a, _, G = data(_genus_symbol_kirschmer(L, p))
  @assert s == Int[0] && is_dyadic(p)
  d = d[1]::Int
  b = w[1]::Int
  a = valuation(a[1], p)::Int
  q = norm(p)
  e = ramification_index(p)

  if iseven(d)
    @assert b == e || isodd(a + b)
    r = div(d, 2)
    disc = (-1)^r * det(G[1])
    c = quadratic_defect(disc, p)
    if d == 2
      if a < b && b == 2 && c == 2 * e
        @assert e - a - 1 >= 0
        lf = QQFieldElem(q^div(e - a - 1, 2) * (q - _get_eps(c)))
      elseif b == e && a + e + 1 <= c && c < 2 * e
        @assert c - e - a >= 0
        lf = QQFieldElem(2 * q^div(c - e - a, 2))
      else
        lf = QQFieldElem(1)
      end
    elseif iseven(a + b)
      if e == a
        lf = QQFieldElem(1)
      elseif c >= 2 * e
        lf = QQFieldElem(q^(Int((e - a)*(r - 1//2) - r)) * (q^r - _get_eps(c)))
      elseif a + e + 1 <= c
        lf = QQFieldElem(2 * q^(Int((c - e - a - 1) * (r - 1//2))))
      else
        lf = QQFieldElem(q^((c - e - a -1) * (r -1)))
      end
    else # a + b odd
      if c == a + b
        lf = QQFieldElem(1)
      elseif c >= 2 * e
        # We first compute the Hilbert symbol hs of (alpha, 1+gamma).
        hs = (c isa PosInf || iseven(a)) ? 1 : -1
        # Compute c'
        if witt_invariant(L, p) == hs
          cc = c
        else
          cc = c isa PosInf ? 2 *e : inf
        end

        if e == b && cc isa PosInf
          ee = _get_eps(c)
          lf = QQFieldElem(q^(Int((e - a - 1) * (r - 1//2))) * (q^r - ee) * (q^(r - 1) + ee), 2)
        elseif e == b
          lf = QQFieldElem(q^(Int((e - a - 1) * (r - 1//2))) * (q + 1))
        elseif cc isa PosInf && c == cc
          ee = _get_eps(c)
          lf = QQFieldElem(q^(Int((2 * e - b - a - 3) * (r - 1//2) + r)) * (q^r - ee) * (q^(2*r - 2) - ee), 2)
        elseif cc isa PosInf
          lf = QQFieldElem(q^(Int((2 * e - b - a - 3 * (r - 1//2) + r)) * (q + 1)))
        elseif c == cc
          ee = _get_eps(c)
          lf = QQFieldElem(q^(Int((2 * e - b - a - 3) * (r - 1//2) + r)) * (q^(r - 1) + 1) * (q^r - ee) * (q^(r - 1) + ee), 2)
        else
          lf = QQFieldElem(q^(Int((2 * e - b - a - 3) * (r - 1//2) + r)) * (q^(r - 1) + 1) * (q + 1))
        end
      elseif b == e
        lf = QQFieldElem(2 * q^(Int((c - e - a) * (r - 1//2))))
      else
        lf = QQFieldElem(q^(2 *r - 2) - 1) * q^(Int((c - a - b - 2) * (r - 1//2) + 1))
      end
    end
  else # odd dimension
    @assert a == 0
    r = div(d - 3, 2)
    w = witt_invariant(L, p)
    if e == b
      lf = QQFieldElem(1)
    elseif isodd(e)
      lf = QQFieldElem((q^(r + 1) - w) * q^((r + 1) * (e - b - 1)))
    else
      lf = (w == 1 ? QQFieldElem(q^(2 * r +2) - 1, 2) : QQFieldElem(q + 1)) * QQFieldElem(q^((r + 1) * (e - b - 1)))
    end
  end
  return _local_factor_maximal(rescale(L, 2), p) * lf
end

################################################################################
#
#  Local factor of lattices at dyadic unramified primes, apres S. Cho.
#
################################################################################

function _local_factor_cho(L, p)
  @assert is_dyadic(p) && ramification_index(p) == 1
  m = rank(L)
  R = base_ring(L)
  K = nf(R)
  _, G, S = jordan_decomposition(L, p)
  k, h = residue_field(R, p)
  hext = extend(h, K)
  V = []

  for s in S
    AG = diagonal_matrix([2^(S[j] < s ? 2*(s - S[j]) : 0) * G[j] for j in 1:length(G)])
    _,B = left_kernel(matrix(k, nrows(AG), 1, [hext(d//K(2)^s) for d in diagonal(AG)]))
    @assert all(is_square(x)[1] for x in B)
    B = map_entries(x -> sqrt(x), B)
    BK = map_entries(x -> hext\x, B)
    Q = 1//K(2)^(s + 1) * BK * AG * transpose(BK)
    for i in 1:ncols(Q)
      for j in 1:ncols(Q)
        if i > j
          Q[i, j] = 0
        elseif i < j
          Q[i, j] *= 2
        end
      end
    end

    Q = map_entries(hext, Q)

    BB = []
    for i in 1:nrows(B)
      b = zero_matrix(k, 1, nrows(B))
      b[1, i] = 1
      push!(BB, b)
    end

    @assert matrix(k, length(BB), length(BB), [ (b * Q * transpose(c))[1, 1] + (c * Q * transpose(b))[1, 1] for b in BB, c in BB]) == Q + transpose(Q)

    _, N = left_kernel(Q + transpose(Q))
    ok = is_diagonal(N * Q * transpose(N))
    @assert ok
    D = diagonal(N * Q * transpose(N))

    @assert ok
    _, rad = left_kernel(matrix(k, length(D), 1, D))

    rad = rad * N

    VV = vector_space(k, nrows(B))

    SS, mSS = sub(VV, [ VV([rad[i, j] for j in 1:ncols(rad) ]) for i in 1:nrows(rad)])
    W, g = quo(VV, SS)

    @assert length(rels(W)) == 0

    if ngens(W) == 0
      push!(V, (s, zero_matrix(k, 0, 0)))
    else
      BBelts = elem_type(k)[]
      for w in gens(W)
        _w = preimage(g, w)
        for j in 1:rank(VV)
          push!(BBelts, _w[j])
        end
      end
      BB = matrix(k, ngens(W), ncols(Q), BBelts)
      push!(V, (s, BB * Q * transpose(BB)))
    end
  end

  M = Int[ ncols(g) for g in G]

  PT = Bool[ valuation(norm(quadratic_lattice(K, identity_matrix(K, nrows(G[i])), gram = G[i])), p) == S[i] for i in 1:length(S) ] # parity type I
  # could try with get_norm_valuation_from_gram_matrix(G[i], p)

  alpha = Int[]

  for i in 1:length(G)
    j = findfirst(v -> v[1] == S[i], V)
    @assert j !== nothing
    v = V[j]
    if ncols(v[2]) != 0 && (!((S[i] - 1) in S) || !(PT[i-1])) && (!((S[i] + 1) in S) || !PT[i + 1])
      push!(alpha, i)
    end
  end

  beta = Int[]
  for i in 1:length(G)
    if !PT[i]
      continue
    end

    idx = findfirst(isequal(S[i] + 2), S)
    if idx === nothing || !PT[idx]
      push!(beta, i)
    end
  end

  rk = - sum(divexact(ncols(Q[2]) * (ncols(Q[2]) - 1), 2) for Q in V) + divexact(m * (m - 1), 2)
  @assert rk >= 0 # rk of maximal redundant quotient

  q = norm(p)
  res = 2^(length(alpha) + length(beta))
  N = count(PT) - length([i for i in 1:(length(S)-1) if PT[i] && PT[i + 1] && (S[i + 1] == S[i] + 1)]) + sum(Int[M[i] for i in 1:length(S) if !PT[i]])

  for i in 1:length(S)
    N += S[i] * divexact(M[i] * (M[i] + 1), 2)
    N += S[i] * M[i] * sum(Int[M[j] for j in (i + 1):length(S)])
  end

  for v in V
    mi = ncols(v[2])
    local QFT
    if mi  == 0
      continue
    elseif isodd(mi)
      QFT = "O"
    elseif mi > 0
      QFT = quadratic_form_type(v[2]) == 1 ? "O+" : "O-"
    end
    res *= QQFieldElem(group_order(QFT, mi, q))//2
  end

  beta = QQFieldElem(1, 2) * QQFieldElem(q)^N * res

  exp = QQFieldElem(m + 1, 2) * sum(S[i] * M[i] for i in 1:length(S)) # from det

  if isodd(m)
    exp += QQFieldElem(m + 1, 2)
    H = group_order("O", m, q)
  else
    exp += m
    d = discriminant(ambient_space(L))
    if is_local_square(d, p)
      H = group_order("O+", m, q)
    else
      Kt, t = polynomial_ring(K, "t", cached = false)
      E, = number_field(t^2 - denominator(d)^2 * d) # broken for non-integral polynomials
      v = valuation(discriminant(maximal_order(E)), p)
      if v == 0
        H = group_order("O-", m, q)
      else
        H = group_order("O", m - 1, q)
        exp += v * QQFieldElem(1 - m, 2)
      end
    end
  end

  @assert is_integral(exp)

  return QQFieldElem(q)^Int(FlintZZ(exp)) * H//2 * QQFieldElem(1)//beta
end

################################################################################
#
#  Local factor
#
################################################################################

# General local factor driver
function local_factor(L::QuadLat, p)
  # The local factor of L at the prime p in the Minkowski-Siegel mass formula
  @req order(p) == base_ring(L) "Ideal not an ideal of the base ring of the lattice"

  if rank(L) == 1
    return QQFieldElem(1)
  end

  R = base_ring(L)
  K = nf(R)

  if is_dyadic(p)
    if ramification_index(p) == 1
      return _local_factor_cho(L, p)
    elseif is_maximal(L, p)[1]
      ss = elem_in_nf(uniformizer(p))^(-valuation(norm(L), p))
      return _local_factor_maximal(rescale(L, ss), p)
    elseif is_modular(L, p)[1]
      ss = elem_in_nf(uniformizer(p))^(-valuation(scale(L), p))
      return _local_factor_unimodular(rescale(L, ss), p)
    else
      a = _isdefinite(rational_span(L))
      def = !iszero(a)
      ss = elem_in_nf(uniformizer(p))^(-valuation(norm(L), p))
      if def
        R = base_ring(L)
        rlp = real_places(K)
        A::GrpAbFinGen, _exp, _log = sign_map(R, _embedding.(rlp), p)
        sa = ss * a
        t = (1 + _exp(A(Int[ sign(sa, _embedding(rlp[j])) == 1 ? 0 : 1 for j in 1:length(rlp)]))::elem_type(R))
        @assert t - 1 in p
        @assert all(Bool[sign(t, _embedding(rlp[i])) == sign(sa, _embedding(rlp[i])) for i in 1:length(rlp)])
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
        M, E = maximal_sublattices(chain[i + 1], p, use_auto = false)# should be use_auto = def)
        _f = 0
        for j in 1:length(M)
          if is_locally_isometric(chain[i], M[j], p)
            _f += E[j]
          end
        end
        f = f * _f
        #f = f * sum(Int[E[j] for j in 1:length(M) if is_locally_isometric(chain[i], M[j], p)])
        M, E = minimal_superlattices(chain[i], p, use_auto = false)# should be use_auto = def)
        _f = 0
        for j in 1:length(M)
          if is_locally_isometric(chain[i + 1], M[j], p)
            _f += E[j]
          end
        end
        f = divexact(f, _f)
        #f = divexact(f, sum(Int[E[j] for j in 1:length(M) if is_locally_isometric(chain[i + 1], M[j], p)]))
      end
      return f
    end
  end

  # The odd primes
  _, G, s = jordan_decomposition(L, p)
  if length(s) == 1
    return QQFieldElem(1)
  end

  local f::QQFieldElem

  m = rank(L)
  q = norm(p)
  if isodd(m)
    f = QQFieldElem(group_order("O+", m, q))
  else
    d = discriminant(ambient_space(L))
    if isodd(valuation(d, p))
      f = QQFieldElem(group_order("O+", m - 1, q))
    elseif is_local_square(d, p)
      f = QQFieldElem(group_order("O+", m, q))
    else
      f = QQFieldElem(group_order("O-", m, q))
    end
  end

  N = QQFieldElem(0)

  for i in 1:length(s)
    mi = ncols(G[i])
    ri = sum(Int[ncols(G[j]) for j in (i + 1):length(s)])
    det = _discriminant(G[i])
    sq = is_local_square(det, p)[1]
    f = divexact(f, group_order(sq ? "O+" : "O-", mi, q))
    N = N - s[i] * divexact(mi*(mi+1), 2) - s[i] * mi * ri
    N = N + s[i] * mi * (m + 1)* 1//2 # volume?
  end

  if iseven(m) && isodd(valuation(d, p))
    N = N + QQFieldElem(1 - m, 2)
  end

  @assert is_integral(N)

  return q^Int(FlintZZ(N)) * f
end

################################################################################
#
#  Mass of a quadratic lattice
#
################################################################################

function mass(L::QuadLat)
  fl, m = _exact_standard_mass(L)

  if fl
    return abs(m) * local_mass(L)
  end

  lm = local_mass(L)

  prec = 10
  mu = _minkowski_multiple(nf(base_ring(L)), rank(L))

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

function _exact_standard_mass(L::QuadLat)
  m = rank(L)
  if m == 0
    return true, QQFieldElem(1)
  elseif m == 1
    return true, QQFieldElem(1, 2)
  end

  R = base_ring(L)
  K = nf(R)
  r = div(m, 2)

  fl = true

  standard_mass = FlintQQ(2)^(-absolute_degree(K) * r)
  if isodd(m)
    #standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-2))
    if _exact_dedekind_zeta_cheap(K)
      standard_mass *= prod(QQFieldElem[dedekind_zeta_exact(K, -i) for i in 1:2:(m-2)])
    else
      return false, QQFieldElem(0)
    end
  else
    #standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-3))

    if _exact_dedekind_zeta_cheap(K)
      standard_mass *= prod(QQFieldElem[dedekind_zeta_exact(K, -i) for i in 1:2:(m-3)])
    else
      return false, QQFieldElem(0)
    end

    dis = discriminant(rational_span(L))
    if is_square(dis)[1]
      if _exact_dedekind_zeta_cheap(K)
        standard_mass *= dedekind_zeta_exact(K, 1 - r)
      else
        return false, QQFieldElem(0)
      end
    else
      Kt, t = polynomial_ring(K, "t", cached = false)
      E, = number_field(t^2 - denominator(dis)^2 * dis, "b", cached = false)
      if _exact_L_function_cheap(E)
        standard_mass *= _exact_L_function(E, 1 - r)
      else
        return false, QQFieldElem(0)
      end
    end
  end

  return true, abs(standard_mass)
end

function local_mass(L::QuadLat)
  lf = QQFieldElem(1)

  for p in bad_primes(L, even = true)
    lf *= local_factor(L, p)
  end

  return lf
end

# The logic is not quite correct, because the precision is only ever increased in the quadratic case ...
function _standard_mass(L::QuadLat, prec::Int = 10)
  m = rank(L)
  RR = ArbField(64)
  if m == 0
    return RR(QQFieldElem(1))
  elseif m == 1
    return RR(QQFieldElem(1, 2))
  end

  R = base_ring(L)
  K = nf(R)
  r = div(m, 2)

  __standard_mass = FlintQQ(2)^(-absolute_degree(K) * r)
  if isodd(m)
    standard_mass = __standard_mass * prod(dedekind_zeta(K, -i, prec) for i in 1:2:(m-2))
  else
    standard_mass = __standard_mass * reduce(*, (dedekind_zeta(K, -i, prec) for i in 1:2:(m-3)), init = one(QQFieldElem))

    dis = discriminant(rational_span(L))
    if is_square(dis)[1]
      #standard_mass *= dedekind_zeta_exact(K, 2 - r)
      standard_mass *= dedekind_zeta(K, 1 - r, prec)
    else
      Kt, t = polynomial_ring(K, "t", cached = false)
      E, = number_field(t^2 - denominator(dis)^2 * dis, "b", cached = false)
      wprec = prec
      local relzeta
      while true
        relzeta = _L_function(E, 1 - r, wprec)
        if radiuslttwopower(relzeta, -prec)
          break
        end
        wprec = wprec + 1
      end
      standard_mass *= relzeta
      #standard_mass *= dedekind_zeta_exact(Eabs, 1 - r, prec, true)
    end
  end

  mass = abs(standard_mass)
end

function _mass(L::QuadLat, standard_mass = 0, prec::Int = 10)
  m = rank(L)
  if m == 0
    return QQFieldElem(1)
  elseif m == 1
    return QQFieldElem(1, 2)
  end

  R = base_ring(L)
  K = nf(R)
  r = div(m, 2)

  if standard_mass == 0
    standard_mass = FlintQQ(2)^(-absolute_degree(K) * r)
    if isodd(m)
      standard_mass *= prod(dedekind_zeta(K, -i, prec) for i in 1:2:(m-2))
    else
      standard_mass *= prod(dedekind_zeta(K, -i, prec) for i in 1:2:(m-3))

      dis = discriminant(rational_span(L))
      if is_square(dis)[1]
        #standard_mass *= dedekind_zeta_exact(K, 2 - r)
        standard_mass *= dedekind_zeta(K, 1 - r, prec)
      else
        Kt, t = polynomial_ring(K, "t", cached = false)
        E, = number_field(t^2 - denominator(dis)^2 * dis, "b", cached = false)
        #standard_mass *= dedekind_zeta_exact(E, 1 - r, true)
        wprec = prec
        local relzeta
        while true
          relzeta = _L_function(E, 1 - r, wprec)
          if radiuslttwopower(relzeta, -prec)
            break
          end
          wprec = wprec + 1
        end
        standard_mass *= relzeta
        #standard_mass *= dedekind_zeta_exact(Eabs, 1 - r, prec, true)
      end
    end
  end

  mass = abs(standard_mass)

  lf = QQFieldElem(1)

  for p in bad_primes(L, even = true)
    lf *= local_factor(L, p)
  end

  return mass, lf
end

function mass(L::QuadLat, prec)
  m, lf = _mass(L, 0, prec)
  return m * lf
end

################################################################################
#
#  Exact values of Dedekind zeta values
#
################################################################################

# To probe if we can compute the L-function of the relative extension E cheaply.
function _exact_L_function_cheap(E)
  K = base_field(E)

  if !is_totally_real(K)
    return false
  end

  if !is_totally_real(E)
    return false
  end

  return true
end

# L-function of a relative quadratic extension E at the negative integer s
function _L_function(E, s, prec)
  if s <= 0
    return _L_function_negative(E, s, prec)
  else
    return _L_function_positive(E, s, prec)
  end
end

function _L_function_negative(E, s, prec)
  K = base_field(E)
  Eabs = absolute_simple_field(E)[1]
  @assert is_totally_complex(Eabs)

  # I want to reflect to 1 - s
  sp = 1 - s
  d = abs(divexact(discriminant(maximal_order(Eabs)), discriminant(maximal_order(K))))
  @assert isodd(sp)

  n = degree(K)

  wprec = 8 * prec
  R = ArbField(wprec, cached = false)

  local pref::arb

  while true
    R = ArbField(wprec, cached = false)
    pref = inv((2 * const_pi(R)))^sp * (-1)^div(sp - 1, 2) * 2  * factorial(ZZRingElem(sp - 1))
    pref = pref^n
    pref = pref * R(d)^(sp - 1//2)
    if radiuslttwopower(pref, -64)
      break
    end
    wprec = 2 * wprec
  end

  i = 0

  while true
    i += 1
    z = _L_function_positive(E, sp, prec + i)
    res = z * pref
    if radiuslttwopower(res, -prec)
      return res
    end
  end
end

function _L_function_positive(E, s, prec)
  K = base_field(E)
  if s == 1
    return _L_function_at_1(E, prec)
  end
  Eabs = absolute_simple_field(E)[1]
  Eabs, = simplify(Eabs)
  @assert is_totally_complex(E)
  @assert s > 1

  R = ArbField(4 * prec, cached = false)

  i = 0
  while true
    i += 1

    z = dedekind_zeta(Eabs, s, prec + i)//dedekind_zeta(K, s, prec + (i + 2))
    if radiuslttwopower(z, -prec)
      return z
    end
  end
end

function _L_function_at_1(E, prec)
  K = base_field(E)
  Eabs, EabsToE = absolute_simple_field(E)
  @assert is_totally_complex(E)
  Eabs, simp = simplify(Eabs, cached = false)
  d = divexact(discriminant(maximal_order(Eabs)),
               discriminant(maximal_order(K)))

  d = abs(d)

  n = degree(K)
  CLE, = class_group(maximal_order(Eabs))
  hE = order(CLE)
  CLK, = class_group(K)
  hK = order(CLK)
  UE, mUE = unit_group(maximal_order(Eabs))
  UK, mUK = unit_group(maximal_order(K))

  TE, mTE = torsion_unit_group(Eabs)

  mu = order(TE)

  gens_for_subgroup = elem_type(UE)[]
  for i in 1:ngens(UK)
    u = mUK(UK[i])
    uu = E(elem_in_nf(u))
    uuu = simp\(EabsToE\uu)
    push!(gens_for_subgroup, mUE\uuu)
  end
  push!(gens_for_subgroup, mUE\mTE(TE[1]))
  S, mS = quo(UE, gens_for_subgroup)
  @assert order(S) <= 2
  Q = order(S)

  wprec = 2 * prec
  while true
    RR = ArbField(wprec, cached = false)
    val = hE//hK * (2 * const_pi(RR))^n // (Q * order(TE) * sqrt(RR(d)))
    if radiuslttwopower(val, prec)
      return val
    end
    wprec = 2 * wprec
  end
end

# This is an exact version, but I don't think.
function _exact_L_function(E, s)
  if absolute_degree(E) == 2
    k = 1 - s
    Eabs = absolute_simple_field(E)[1]
    if is_totally_real(Eabs)
      d = discriminant(maximal_order(Eabs))
      return _bernoulli_kronecker(k, d)//-k
    end
  end

  Eabs = absolute_simple_field(E)[1]
  K = base_field(E)
  return dedekind_zeta_exact(Eabs, s)//dedekind_zeta_exact(K, s)
end

# Probe if the exact computation of the Dedekind zeta function is cheap
function _exact_dedekind_zeta_cheap(K)
  return is_totally_real(K)
end

################################################################################
#
#  Dedekind zeta function evaluation a la Attwell-Duval
#
################################################################################

# This works :)
#
# But it is really slow for s = -1 (s = 2), since the Euler product
# converges only "linear", that is doubling the number of primes only doubles
# the precision.

function _truncated_euler_product(K::AnticNumberField, T::Int, s, RR::ArbField)
  z = one(RR)
  OK = maximal_order(K)
  p = 2
  #@show s, T
  while p <= T
    dectyp = prime_decomposition_type(OK, p)
    for (f, e) in dectyp
      z = z * inv(1 - RR(ZZRingElem(p)^f)^(-s))
    end
    p = next_prime(p)
  end

  return z
end

function _local_correction(K, p, RR)
  lp = prime_decomposition_type(maximal_order(K), p)
  z = one(RR)
  for (f, e) in lp
    z = z * inv((RR(1) - inv(RR(p)^(2 * f))))
  end

  z = z * (RR(1) - inv(RR(p)^2))^degree(K)
  return z
end

function _dedekind_zeta_attwell_duval_positive(K::AnticNumberField, s, prec::Int)
  RR = ArbField(512)
  d = degree(K)
  #@show prec

  local_cor = prod(arb[_local_correction(K, p, RR) for p in primes_up_to(100)])
  #@show local_cor

  _b = RR(s - 1) * (root(RR(2)^(-prec + 1)//(local_cor * zeta(RR(s))^d) + 1, d) - 1)

  #@show _b

  #@show inv(_b)

  _T = upper_bound(ZZRingElem, root(inv(_b), s - 1))

  _Tint = Int(_T)

  b = local_cor * zeta(RR(s))^d * (RR(d) + 1)//(RR(s - 1))//(RR(2))^(-(prec + 1))
  bb = root(b, s - 1)
  T = upper_bound(ZZRingElem, bb)
  # z_K(s) - truncated at T < 1/2^(prec + 1)
  @assert fits(Int, T)
  Tint = Int(T)

  @assert local_cor * zeta(RR(s))^d * ((1 +1//((s - 1) * RR(Tint)^(s - 1)))^d - 1) < (RR(2))^(-(prec + 1))

#  otherbound = local_cor * zeta(RR(s))^d * ((1 +1//((s - 1) * RR(div(Tint, 2))^(s - 1)))^d - 1)
#
#  while otherbound < RR(2)^(-prec - 1)
#    Tint = div(Tint, 2)
#    otherbound = local_cor * zeta(RR(s))^d * ((1 + 1//((s - 1) * RR(div(Tint, 2))^(s - 1)))^d - 1)
#  end
#
#  otherbound = zeta(RR(s))^d * ((1 + 1//((s - 1) * RR(Tint)^(s - 1)))^d - 1)
#  @assert radiuslttwopower(otherbound, -prec - 1)
#

  wprec = 3 * prec

  error_arf = arf_struct(0, 0, 0, 0)
  ccall((:arf_set_si_2exp_si, libarb), Nothing,
        (Ref{arf_struct}, Int, Int), error_arf, Int(1), Int(-(prec + 1)))

  local valaddederror

  while true
    RR = ArbField(wprec)
    z = _truncated_euler_product(K, Tint, s, RR)

    wprec = 2 * wprec

    valaddederror = deepcopy(z)
    ccall((:arb_add_error_arf, libarb), Nothing,
                (Ref{arb}, Ref{arf_struct}), valaddederror, error_arf)

    if radiuslttwopower(valaddederror, -prec)
      break
    end
  end

  ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), error_arf)

  return valaddederror
end

function _dedekind_zeta_attwell_duval_negative(K::AnticNumberField, s, target_prec::Int)
  @assert s < 0
  if iseven(s)
    return zero(ArbField(target_prec))
  end
  sp = 1 - s
  z = _dedekind_zeta_attwell_duval_positive(K, sp, target_prec + 1)
  zprec = precision(parent(z))
  wprec = zprec * 2
  RR = ArbField(wprec)
  dK = abs(discriminant(maximal_order(K)))
  d = degree(K)

  local res

  i = 1

  local prefac

  _wprec = 64
  while true
    RR = ArbField(_wprec)
    CK = RR(dK)//(const_pi(RR)^d * 2^d)
    prefac = (-1)^(div(d * sp, 2)) * CK^sp * (2 * RR(factorial(ZZRingElem(sp) - 1)))^d//sqrt(RR(dK))
    if radiuslttwopower(prefac, -4 * target_prec)
      break
    end
    _wprec = 2 * _wprec
  end

  _target_prec = target_prec

  while true
    res = prefac * z

    res_old = res
    if radiuslttwopower(res, -target_prec)
      break
    end
    _target_prec = Int(ceil(1.1 * _target_prec))
    z = _dedekind_zeta_attwell_duval_positive(K, sp, _target_prec)
    #@show radiuslttwopower(z, -_target_prec)
  end
  return res
end

function dedekind_zeta(K::AnticNumberField, s::Int, prec::Int)
  @req s != 0 && s != 1 "Point $s is a pole"
  r1, r2 = signature(K)
  if r2 == 0
    if s > 0
      return _dedekind_zeta_attwell_duval_positive(K, s, prec)
    else
      return _dedekind_zeta_attwell_duval_negative(K, s, prec)
    end
  else
    if s < 0
      return zero(ArbField(prec))
    else
      return _dedekind_zeta_attwell_duval_positive(K, s, prec)
    end
  end
end

################################################################################
#
#  Group orders of classical linear groups groups
#
################################################################################

# Some group orders for classical linear groups G_m(q), where
# G is "O+", "O-", "G", "U", or "Sp"
function group_order(G::String, m::Int, q::ZZRingElem)
  if G[1] != 'O'
    if G[1] == 'G' # GL_m
      o = prod(QQFieldElem[ 1 - QQFieldElem(q)^(-j) for j in 1:m ])
    elseif G[1] == 'U' # U_m
      o = prod(QQFieldElem[ 1 - QQFieldElem(-q)^(-j) for j in 1:m ])
    else # Default Sp_m
      o = prod(QQFieldElem[ 1 - QQFieldElem(q)^(-j) for j in 2:2:m ])
    end
  else # orthogonal case
    if iseven(m)
      k = div(m, 2)
      e = G[2] == '+' ? 1 : -1
      o = 2 * (1 - e * QQFieldElem(q)^(-k)) * prod(QQFieldElem[ 1 - QQFieldElem(q)^(-j) for j in 2:2:(m-2)])
    else
      o = 2 * prod(QQFieldElem[1 - QQFieldElem(q)^(-j) for j in 2:2:m])
    end
  end
  return o
end

# Determines type of an orthgonal group over a finite field of even
# characteristic.
function quadratic_form_type(v)
  return _orthogonal_signum_even(v + transpose(v), v)
end

# Bring symmetric form into standard form
function _orthogonal_signum_even(form, quad)
	basis = form^0
	skip = Int[]
	for i in 1:(nrows(form)-1)
    # find first non-zero entry in i-th row
    d = 1
    while d in skip || iszero(form[i, d])
      d = d + 1
    end
    push!(skip, d)
    # clear entries in row and column
    for j in (d + 1):nrows(form)
      c = divexact(form[i, j], form[i, d])
      if !iszero(c)
        for k in 1:nrows(form)
          form[k, j] = form[k, j] - c * form[k, d]
        end

        for k in 1:ncols(form)
          form[j, k] = form[j, k] - c * form[d, k]
        end

        for k in 1:ncols(form)
          basis[j, k] = basis[j, k] - c * basis[d, k]
        end
      end
    end
  end
  # reshuffle basis
  c = typeof(basis)[]
  j = Int[]
  for i in 1:nrows(form)
    if !(i in j)
      k = form[i, skip[i]]
      push!(c, inv(k) * sub(basis, i:i, 1:ncols(basis)))
      push!(c, sub(basis, skip[i]:skip[i], 1:ncols(basis)))
      push!(j, skip[i])
    end
  end

  basis = c
  Rt, t = polynomial_ring(base_ring(form), "t", cached = false)
  sgn = 1
  for i in 1:2:(nrows(form) - 1)
    c = (basis[i] * quad * transpose(basis[i]))[1, 1]
    if iszero(c)
      continue
    else
      j = (basis[i + 1] * quad * transpose(basis[i + 1]))[1, 1]
      if iszero(j)
        continue
      else
        pol = t^2 + inv(j) * t + inv(j) * c
        if !is_irreducible(pol)
          continue
        else
          sgn = -sgn
        end
      end
    end
  end
  return sgn
end

# A multiple of orders is given by Serre in:
# Bounds for the orders of the finite subgroups of G(k)
# It is also in Feit:
# Finite linear groups and .. Minkowski ... Schur
#
# See also http://oeis.org/A053657

# https://mathoverflow.net/questions/15127/the-maximum-order-of-finite-subgroups-in-gln-q?noredirect=1&lq=1
#
# https://mathoverflow.net/questions/168292/maximal-order-of-finite-subgroups-of-gln-z?noredirect=1&lq=1
#In fact, I have a copy of a preprint by Feit of this paper. I have not checked the results, but here is what Feit says: the group of signed permutation matrices is of maximal order as a finite subgroup of GL(𝑛,ℚ), except in the following cases (Feit's Theorem A).
#
#𝑛=2,𝑊(𝐺2) of order 12.
#
#𝑛=4,𝑊(𝐹4), order 1152.
#
#𝑛=6,𝑊(𝐸6)×𝐶2, order 103680.
#𝑛=7,𝑊(𝐸7), order 2903040.
#𝑛=8,𝑊(𝐸8), order 696729600.
#
#𝑛=9,𝑊(𝐸8)×𝑊(𝐴1), order 1393459200 (reducible).
#
#𝑛=10,𝑊(𝐸8)×𝑊(𝐺2), order 8360755200 (reducible).


function _minkowski_multiple(n)
  if n == 1
    return ZZRingElem(2)
  elseif n == 2
    return ZZRingElem(24)
  elseif n == 3
    return ZZRingElem(48)
  else
    bernoulli_cache(n)
    if isodd(n)
      return 2 * _minkowski_multiple(n - 1)
    else
      return denominator(divexact(bernoulli(n), n)) * _minkowski_multiple(n - 1)
    end
  end
end

################################################################################
#
#  Minkowski/Schur constants for number fields
#
################################################################################

# Computes an integer B, such that for any finite subgroup G of GL_n(K) the order
# of G divides B.
#
# Reference:
# Robret M. Guralnick and Martin Lorenz, "Orders of Finite Groups of Matrices"
#
# The idea is that the p' part of divides the p' part of GL_n(O/P), where P is
# any prime above p. Use primes until the bound does not change.
#
# This is in general not sharp, since it uses a heuristic. There is actually
# a "closed" formula for this number (see loc. cit.), but it requires a lot of
# expensive computations.
function _minkowski_multiple(K, n)
  OK = maximal_order(K)
  p = 2
  dec = prime_decomposition_type(OK, p)
  f2 = minimum(Int[f for (f, e) in dec])
  p = 3
  dec = prime_decomposition_type(OK, p)
  f3 = minimum(Int[f for (f, e) in dec])
  q2 = ZZRingElem(2)^f2
  q3 = ZZRingElem(3)^f3
  glf2 = prod(ZZRingElem[q2^i - 1 for i in 1:n])
  glf3 = prod(ZZRingElem[q3^i - 1 for i in 1:n])
  twopart, = ppio(glf3, ZZRingElem(2))
  cand = glf2 * twopart
  stab = 0
  while true
    dec = prime_decomposition_type(OK, p)
    ppart, = ppio(cand, ZZRingElem(p))
    f = minimum(Int[f for (f, e) in dec])
    q = ZZRingElem(p)^f
    glf = prod(ZZRingElem[q^i - 1 for i in 1:n])
    old_can = cand
    cand = gcd(cand, glf * ppart)
    if old_can == cand
      stab += 1
    end
    if stab > 20
      return cand
    end
    p = next_prime(p)
  end
  return cand
end

# Also allow QQ, to allow for more uniform code calling _minkowski_multiple
_minkowski_multiple(K::QQField, n) = _minkowski_multiple(n)


################################################################################
#
#  Denominator bounds for Dedekind zeta function values
#
################################################################################

# See Andreatta, Goren: "Hilbert Modular Forms: mod p and p-Adic Aspects"
# K must be totally real
function _denominator_valuation_bound(K, ss, p)
  s = 1 - ss
  @assert s > 0 && iseven(s)

  l(n) = n <= 2 ? n - 1 : n - 2
  if p == 2
    t = prime_decomposition_type(maximal_order(K), Int(p))
    rm = Tuple{Int, ZZRingElem}[ remove(e, p) for (f, e) in t ]
    ew = minimum(Int[p^e for (e, _) in rm ])
    et = minimum(Int[m for (_, m) in rm ])
    n = 0
    ewval = valuation(ew, p)
    sval = valuation(s, 2)
    while sval + ewval >= l(n)
      n += 1
    end
    return max(0, n - 1 - degree(K))
  elseif is_ramified(maximal_order(K), p)
    _lp = prime_decomposition(maximal_order(K), Int(p))
    t = prime_decomposition_type(maximal_order(K), Int(p))
    rm = Tuple{Int, ZZRingElem}[ remove(e, p) for (f, e) in t ]
    ew = minimum(Int[p^e for (e, _) in rm ])
    et = minimum(Int[m for (_, m) in rm ])
    return valuation(s, p) + 1 + valuation(ew, p)
  elseif mod(s, p - 1) == 0
    ss = divexact(s, p - 1)
    return valuation(ss, p) + 1
  else
    return 0
  end
end

function _denominator_bound(K, ss)
  s = 1 - ss
  @assert s > 0 && iseven(s)

  d = one(ZZRingElem)

  OK = maximal_order(K)

  d = d * ZZRingElem(2)^_denominator_valuation_bound(K, ss, 2)

  for p in ramified_primes(maximal_order(K))
    d = d * ZZRingElem(p)^_denominator_valuation_bound(K, ss, p)
  end

  for p in primes_up_to(s + 1)
    if is_ramified(OK, p) || p == 2
      continue
    end
    if mod(s, p - 1) == 0
      d = d * ZZRingElem(p)^_denominator_valuation_bound(K, ss, p)
    end
  end
  return d
end

################################################################################
#
#  Functionality for the totally real quadratic case
#
################################################################################

function _modulus_of_kronecker_as_dirichlet(D)
  return abs(fundamental_discriminant(D))
end

function _bernoulli_kronecker(z::IntegerUnion, D)
  return _bernoulli_kronecker(Int(z), D)
end

function _bernoulli_kronecker(z::Int, D)
  @assert z >= 0
  D1 = fundamental_discriminant(D)
  f = abs(D1)
  K = FlintQQ
  Rt, t = power_series_ring(K, z + 3, "t", cached = false, model = :capped_absolute)
  denom = exp(f*t) - 1
  #@show [_kronecker_as_dirichlet(a, N) for a in 1:Int(f)]
  num = sum(elem_type(Rt)[_kronecker_symbol(D1, a) * t * exp(a * t) for a in 1:Int(f)])
  F = divexact(num, denom)
  p = precision(F)
  @assert p >= z + 1
  return coeff(F, z) * factorial(ZZRingElem(z))
end

function _kronecker_as_dirichlet(n, D)
  if gcd(n, D) == 1
    return _kronecker_symbol(_modulus_of_kronecker_as_dirichlet(D), n)
  end
  return 0
end

function _kronecker_symbol(n, m)
  res = 1
  # deal with zero denominator
  if m == 0
    if abs(n) == 1
      return 1
    else
      return 0
    end
  end
  # deal with negative denom
  if m < 0
    if n < 0
      res*= -1
    end
    m = -m
  end
  # deal with even denominator
  e, m = remove(m, 2)
  if e > 0 && iseven(n)
    return 0
  end
  if isodd(e)
    nmod8 = mod(n, 8)
    if nmod8 == 3 || nmod8 == 5
      res *= -1
    end
  end
  if m == 1
    return res
  end
  res *= _jacobi_symbol(n, m)
  return res
end

# don't use this, this is slow
function _jacobi_symbol(n, m)
  @req m >= 3 "Second argument $(m) must be >= 3"
  @assert isodd(m)
  if !isone(gcd(n, m))
    return 0
  end

  res = 1
  for (p, e) in factor(m)
    if isodd(e)
      res *= jacobi_symbol(n, p)
    end
  end
  return res
end


################################################################################
#
#  Dedekind zeta exact for totally real
#
################################################################################

function dedekind_zeta_exact(K::AnticNumberField, s::Int)
  @assert is_totally_real(K)
  @assert s < 0

  if iseven(s)
    return zero(QQFieldElem)
  end

  if isodd(s)
    k = 1 - s
    if absolute_degree(K) == 1
      return bernoulli(k)//-k
    elseif absolute_degree(K) == 2
      Kabs = absolute_simple_field(K)[1]
      if is_totally_real(K)
        d = discriminant(maximal_order(Kabs))
        return bernoulli(k) * _bernoulli_kronecker(k, d)//k^2
      end
    end
  end

  d = _denominator_bound(K, s)
  n = Int(nbits(d)) - 1

  while true
    ded = dedekind_zeta(K, s, n)
    z  = d * ded
    fl, b = unique_integer(z)
    if fl
      return b//d
    end
    n += 1
  end
end

################################################################################
#
#  Dedekind zeta function evaluation a la Tollis
#
################################################################################

# This does not work at the moment.

function _compute_decs(Z::ZetaFunction, n::Int)
  K = Z.K
  OK = maximal_order(K)
  p = 2
  decs = []
  while p <= n
    for (f, e) in prime_decomposition_type(OK, p)
      push!(decs, (p, f))
    end
    p = next_prime(p)
  end
  Z.dec_types = decs
end

function _compute_an(Z::ZetaFunction, n::Int, h::Int)
  if n == 1 && h == 0
    return ZZRingElem(1)
  elseif n > 1 && h == 0
    return ZZRingElem(0)
  end

  p, f =  Z.dec_types[h]
  P = p^f
  v, = remove(n, P)
  z = zero(FlintZZ)
  for k in 0:v
    z = z + _compute_an(Z, divexact(n, P^k), h - 1)
  end
  return z
end

function _compute_an(Z::ZetaFunction, n::Int)
  _compute_decs(Z, n)
  m = length(Z.dec_types)
  return _compute_an(Z, n, m)
end

function _Hqk(q, k)
  if q == 0
    return 0
  end
  return sum(QQFieldElem(1, ZZRingElem(j)^k) for j in 1:Int(q))
end

function _compute_g_function_coefficients_even(i, n, r1, r2, CC::AcbField)
  @assert i % 2 == 0
  q = div(i, 2)
  res = Vector{acb}(undef, n + 1)
  res[1] = zero(CC)
  RR = ArbField(precision(CC))
  for k in 1:n
    z = (-1)^k * (k == 1 ? CC(const_euler(RR)) : zeta(CC(k))) * (CC(r1)//CC(2)^k + CC(r2))
    z = z + CC(r1)//CC(2)^k * _Hqk(q, k) + r2 * _Hqk(2 * q, k)
    res[k + 1] = z//CC(k)
  end
  return res
end

function _compute_premultiplier_even(i, r1, r2, CC::AcbField)
  q = div(i, 2)
  z = (-1)^(mod(q, 2)* mod(r1, 2)) * CC(2)^r1
  z = z//(CC(factorial(ZZRingElem(q)))^r1 * (CC(factorial(2*ZZRingElem(q))))^r2)
  return z
end

function _compute_Aij_even(i, r1, r2, CC::AcbField)
  CCx, x = laurent_series_ring(CC, r1 + r2 + 2, "x", cached = false)
  coef = _compute_g_function_coefficients_even(i, r1 + r2 + 1, r1, r2, CC)
  g = sum(coef[i + 1] * x^i for i in 1:(length(coef) - 1))
  expg = exp(g)
  pr = _compute_premultiplier_even(i, r1, r2, CC)
  res = Vector{acb}(undef, r1 + r2 + 1)
  for j in 0:(r1 + r2)
    # this is A_{i,j}
    res[j + 1] = coeff(expg, r1 + r2 - j) * pr
  end
  return res
end

# julia> exp(evaluate(CCy(Hecke._compute_g_function_coefficients_even(6, 20, 1, 1, CC)), CC(0.5))) * Hecke._compute_premultiplier_even(6, 1, 1, CC)//CC(0.5)^(1 + 1)
# [-0.01096173941170919558 +/- 9.45e-21] + i*0
#
# julia> gamma(CC(-5.5)//2) * gamma(CC(-5.5))
# [-0.01096173972011708044 +/- 8.22e-21] + i*0

function _compute_g_function_coefficients_odd(i, n, r1, r2, CC::AcbField)
  @assert i % 2 == 1
  q = div(i - 1, 2)
  res = Vector{acb}(undef, n + 1)
  res[1] = zero(CC)
  RR = ArbField(precision(CC))
  for k in 1:n
    z = (-1)^k * (k == 1 ? CC(const_euler(RR)) : zeta(CC(k))) * (r1 * (1 - CC(2)^-k) + r2)
    z = z + CC(r1 + r2) * _Hqk(i, k) - CC(r2)//CC(2)^k * _Hqk(q, k) - (k > 1 ? CC(0) : CC(r1) * CC(log(RR(2))))
    res[k + 1] = z//CC(k)
  end
  return res
end

function _compute_premultiplier_odd(i, r1, r2, CC::AcbField)
  q = div(i - 1, 2)
  z = (-1)^(mod((q + 1)*r1 + r2, 2)) * const_pi(CC)^(r1//2) * CC(2)^((2*q + 1)*r1) * CC(factorial(ZZRingElem(q)))^r1 # does this overflow one of the exponents?
  z = z//(CC(factorial(ZZRingElem(i)))^(r1 + r2))
  return z
end

function _compute_Aij_odd(i, r1, r2, CC::AcbField)
  CCx, x = laurent_series_ring(CC, r1 + r2 + 2, "x", cached = false)
  coef = _compute_g_function_coefficients_odd(i, r1 + r2 + 1, r1, r2, CC)
  g = sum(coef[i + 1] * x^i for i in 1:(length(coef) - 1))
  expg = exp(g)
  pr = _compute_premultiplier_odd(i, r1, r2, CC)
  res = Vector{acb}(undef, r1 + r2 + 1)
  for j in 0:(r1 + r2)
    # this is A_{i,j}
    res[j + 1] = coeff(expg, r2 - j) * pr
  end
  return res
end

function _compute_Aij(i, r1, r2, CC)
  if iseven(i)
    return _compute_Aij_even(i, r1, r2, CC)
  else
    return _compute_Aij_odd(i, r1, r2, CC)
  end
end

#julia> exp(evaluate(CCy(Hecke._compute_g_function_coefficients_odd(7, 50, 1, 1, CC)), CC(0.5))) * Hecke._compute_premultiplier_odd(7, 1, 1, CC)//CC(0.5)^(1)
#
#[-0.00090029524158452126 +/- 2.42e-21] + i*0
#
#julia> gamma(CC(-6.5)//2) * gamma(CC(-6.5))
#[-0.000900295241584521281 +/- 8.45e-22] + i*0

# so A_{ij} = _compute_Aij(i, r1, r2, CC)[j + 1] # since j begins at 0

function _compute_Aijs(i, j, s, r1, r2, CC)
  @show "Aijs", i, j, s, r1, r2
  if j > 1000
    error("asdsd")
  end
  if s == -i
    return _compute_Aij(i, r1, r2, CC)[j] # A_{-s, j - 1}
  else
    if j == r1 + r2 + 1 && iseven(i)
      return zero(CC)
    elseif j >= r2 + 1 && isodd(i)
      @show "hre"
      return zero(CC)
    else
      @show i, j, s
      return (_compute_Aijs(i, j + 1, s, r1, r2, CC) - _compute_Aij(i, r1, r2, CC)[j + 1])//(s + CC(i))
    end
  end
  error("Ads")
end

function _tollis_f(x, s::Int, i0, r1, r2, CC)
  if s >= 0
    return _tollis_f(x, CC(s), i0, r1, r2, CC)
  end

  z = zero(CC)
  for j in 1:(r1 + r2)
    for i in 0:i0
      if i == -s
        continue
      end
      z += _compute_Aijs(i, j, s, r1, r2, CC) * (1//x)^i * (log(x))^(j - 1)//CC(factorial(ZZRingElem(j-1)))
    end
  end

  for j in 1:(r1 + r2 + 1)
    z += _compute_Aijs(-s, j, s, r1, r2, CC) * x^s * (log(x))^(j - 1)//CC(factorial(ZZRingElem(j - 1)))
  end
  return z
end

function _tollis_f(x, s::acb, i0, r1, r2, CC)
  z = zero(CC)
  @show "tollis f $x $s"
  for j in 1:(r1 + r2)
    for i in 0:i0
      z += _compute_Aijs(i, j, s, r1, r2, CC) * (1//x)^i * (log(x))^(j - 1)//CC(factorial(ZZRingElem(j-1)))
      z += x^s * gamma(s//2)^r1 * gamma(s)^r2
    end
  end
  return z
end

function _tollis_summation(K, s, N, i0, CC)
  r1, r2 = signature(K)
  Z = ZetaFunction(K)
  CK = sqrt(CC(abs(discriminant(maximal_order(K)))))//(const_pi(CC)^(degree(K)//2) * CC(2)^r2)
  z = zero(CC)
  for n in 1:N
    @show n
    z += _compute_an(Z, n) * (_tollis_f(CK//n, s, i0, r1, r2, CC) + _tollis_f(CK//n, 1 - s, i0, r1, r2, CC))
  end
  return z
end

function _evaluate_zeta_K(K, _s, N0, i0, CC)
  # I need the regulator with high precision
  r1, r2 = signature(K)
  RK = regulator(maximal_order(K))
  hK = order(class_group(maximal_order(K))[1])
  wK = order(torsion_unit_group(K)[1])
  CK = sqrt(CC(abs(discriminant(maximal_order(K)))))//(const_pi(CC)^(degree(K)//2) * CC(2)^r2)
  z = CC(2)^r1 * hK * CC(RK)
  @show CK
  s = CC(_s)
  z = z//(CC(wK) * s * (s - 1))
  @show z
  Z = ZetaFunction(K)

  #z += _tollis_summation(K, s, N0, i0, CC)

  y = CK^s * gamma(s//2)^r1 * gamma(s)^r2 * sum(_compute_an(Z, n) * n^(-s) for n in 1:N0)
  @show y
  z += y
  @show z
  z += _tollis_SK(s, N0, i0, r1, r2, CK, Z, CC)
  @show z
  z += _tollis_SK(1 - s, N0, i0, r1, r2, CK, Z, CC)
  @show z
  y = CK^(1 - s) * gamma((1 - s)//2)^r1 * gamma(1 - s)^r2 * sum(_compute_an(Z, n) * n^(s - 1) for n in 1:N0)
  @show y
  z = z + y

  # this is the completed zeta function

  #fa = gamma(s//2)^r1 * gamma(s)^2 * CK^s

  #return z//fa
  return z
end

function _tollis_SK(s, N0, i0, r1, r2, CK, Z, CC)
  z = zero(CC)
  for k in 0:(r1 + r2 - 1)
    for i in 0:i0
      @assert isfinite(z)
      y = _tollis_cik(i, k, N0, CK, r1, r2, Z, CC)//(s + CC(i))^(k + 1)
      z += y
    end
  end
  return -z
end

function _tollis_cik(i, k, N0, CK, r1, r2, Z, CC)
  z = zero(CC)
  for n in 1:N0
    an = _compute_an(Z, n)
    for j in 1:(r1 + r2 - k)
      y = an * _compute_Aij(i, r1, r2, CC)[j + k + 1]
      #@show y
      @assert isfinite(y)
      w = (CC(n)//CK)^i * log(CK//n)^(j-1)//CC(factorial(ZZRingElem(j - 1)))
      #@show (i, k, n, j, w)
      y = y * w
      @assert isfinite(y)
      z += y
    end
  end
  @assert isfinite(z)
  return z
end

