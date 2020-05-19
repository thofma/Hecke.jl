export mass

#// returns q^-dim(G) * #G(F_q)
#
#function WittToHasse(Dim, Det, Finite)
#  K:= Parent(Det);
#  c:= K ! case < Dim mod 8 | 3: -Det, 4: -Det, 5: -1, 6: -1, 7: Det, 0: Det, default : 1 >;
#  return { x[1] : x in Finite | x[2] ne HilbertSymbol(K ! -1, c, x[1]) };
#end function;
#
#// Local factor of a maximal lattice in K*L following Shimura / Gan-Hanke-Yu.
function _local_factor_maximal(L, p)
  m = rank(L)
  r = div(m, 2)
  if m == 1
    return fmpq(1)
  end

  w = witt_invariant(L, p)
  d = discriminant(ambient_space(L))
  q = norm(p)
  if isodd(m)
    if isodd(valuation(d, p))
      return fmpq(q^r + w, 2)
    elseif w == -1 && iseven(valuation(d, p))
      return divexact(fmpq(q^(m-1) -1, q + 1), 2)
    end
  else
    if isodd(valuation(d, p))
      # ram
      return fmpq(1,2)
    elseif islocal_square(d, p)
      # split
      if w == -1
        return divexact(fmpq((q^(r -1) - 1) * (q^r - 1), q + 1), 2)
      end
    elseif isodd(quadratic_defect(d, p))
      # ram
      return fmpq(1, 2)
    else
      if w == -1
        return divexact(fmpq((q^(r -1) + 1) * (q^r + 1), q + 1), 2)
      end
    end
  end
  return fmpq(1)
end

_get_eps(::PosInf) = 1

_get_eps(::Any) = -1

function _local_factor_unimodular(L::QuadLat, p)
  d, s, w, a, _, G = data(_genus_symbol_kirschmer(L, p))
  @assert s == [0] && isdyadic(p)
  d = d[1]
  b = w[1]
  a = valuation(a[1], p)
  q = norm(p)
  e = ramification_index(p)

  if iseven(d)
    @assert b == e || isodd(a + b)
    r = div(d, 2)
    disc = (-1)^r * det(G[1])
    c = quadratic_defect(disc, p)
    if d == 2
      if a < b && b == 2 && c == 2 * e
        lf = fmpq(q^div(e - a - 1, 2) * (q - _get_eps(c)))
      elseif b == e && a + e + 1 <= c && c < 2 * e
        lf = fmpq(2 * q^div(c - e - a, 2))
      else
        lf = fmpq(1)
      end
    elseif iseven(a + b)
      if e == a
        lf = fmpq(1)
      elseif c >= 2 * e
        lf = fmpq(q^(Int((e - a)*(r - 1//2) - r)) * (q^r - _get_eps(c)))
      elseif a + e + 1 <= e
        lf = fmpq(2 * q^(Int((c - e - a - 1) * (r - 1//2))))
      else
        lf = fmpq(q^((c - e - a -1) * (r -1)))
      end
    else # a + b odd
      if c == a + b
        lf = fmpq(1)
      elseif c == 2 * e
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
          lf = fmpq(q^(Int((e - a - 1) * (r - 1//2))) * (q^r - ee) * (q^(r - 1) + ee), 2)
        elseif e == b
          lf = fmpq(q^(Int((e - a - 1) * (r - 1//2))) * (q + 1))
        elseif cc isa PosInf && c == cc
          ee = _get_eps(c)
          lf = fmpq(q^(Int((2 * e - b - a - 3) * (r - 1//2) + r)) * (q^r - ee) * (q^(2*r - 2) - ee), 2)
        elseif cc isa PosInf
          lf = fmpq(q^(Int((2 * e - b - a - 3 * (r - 1//2) + r)) * (q + 1)))
        elseif c == cc
          ee = _get_eps(c)
          lf = fmpq(q^(Int((2 * e - b - a - 3) * (r - 1//2) + r)) * (q^(r - 1) + 1) * (q^r - ee) * (q^(r - 1) + ee), 2)
        else
          lf = fmpq(q^(Int((2 * e - b - a - 3) * (r - 1//2) + r)) * (q^(r - 1) + 1) * (q + 1))
        end
      elseif b == e
        lf = fmpq(2 * q^(Int((c - e - a) * (r - 1//2))))
      else
        lf = fmpq(q^((2 *r - 2) - 1) * q^(Int((c - a -b - 2) * (r - 1//2) + 1)))
      end
    end
  else # odd dimension
    @assert a == 0
    r = div(d - 3, 2)
    w = witt_invariant(L, p)
    if e == b
      lf = fmpq(1)
    elseif isodd(e)
      lf = fmpq((q^(r + 1) - w) * q^((r + 1) * (e - b - 1)))
    else
      lf = (w == 1 ? fmpq(q^(2 * r +2) - 1, 2) : fmpq(q + 1)) * fmpq(q^((r + 1) * (e - b - 1)))
    end
  end
  return _local_factor_maximal(rescale(L, 2), p) * lf
end

# General local factor driver

function local_factor(L::QuadLat, p)
  # The local factor of L at the prime p in the Minkowski-Siegel mass formula
  @req order(p) == base_ring(L) "Ideal not an ideal of the base ring of the lattice"

  @show "adsad", p

  if rank(L) == 1
    return fmpq(1)
  end

  R = base_ring(L)
  K = nf(R)

  if isdyadic(p)
    if ramification_index(p) == 1
      return _local_factor_cho(L, p)
    elseif ismaximal(L, p)[1]
      s = uniformizer(p)^(-valuation(norm(L), p))
      return _local_factor_maximal(rescale(L, s), p)
    elseif ismodular(L, p)[1]
      s = uniformizer(p)^(-valuation(scale(L), p))
      return _local_factor_unimodular(rescale(L, s), p)
    else
      a = _isdefinite(rational_span(L))
      def = !iszero(a)
      s = uniformizer(p)^(-valuation(norm(L), p))
      if def
        R = base_ring(L)
        rlp = real_places(K)
        A, _exp, _log = infinite_primes_map(R, rlp, p)
        sa = s * a
        t = (1 + _exp(A([ sign(sa, rlp[j]) == 1 ? 0 : 1 for j in 1:length(rlp)])))
        @assert t - 1 in p
        @assert all(i -> sign(t, rlp[i]) == sign(sa, rlp[i]), 1:length(rlp))
        s = s * t
      end
      L = rescale(L, s)
      chain = typeof(L)[L]
      ok, LL = ismaximal_integral(L, p)
      while !ok
        push!(chain, LL)
        ok, LL = ismaximal_integral(LL, p)
      end
      f = _local_factor_maximal(L, p)

      for i in 1:(length(chain) - 1)
        M, E = maximal_sublattices(chain[i + 1], p, use_auto = false)# should be use_auto = def)
        f = f * sum(E[j] for j in 1:length(M) if islocally_isometric(chain[i], M[j], p))
        M, E = minimal_superlattices(chain[i], p, use_auto = false)# should be use_auto = def)
        f = divexact(f, sum(E[j] for j in 1:length(M) if islocally_isometric(chain[i + 1], M[j], p)))
      end
      return f
    end
  end

  # The odd primes
  _, G, s = jordan_decomposition(L, p)
  if length(s) == 1
    return fmpq(1)
  end

  @show s

  m = rank(L)
  q = norm(p)
  if isodd(m)
    f = group_order("O+", m, q)
  else
    @show "here"
    d = discriminant(ambient_space(L))
    if isodd(valuation(d, p))
      f = group_order("O+", m - 1, q)
    elseif islocal_square(d, p)
      f = group_order("O+", m, q)
    else
      f = group_order("O-", m, q)
    end
  end

  @show f

  N = fmpq(0)

  for i in 1:length(s)
    mi = ncols(G[i])
    ri = sum(Int[ncols(G[j]) for j in (i + 1):length(s)])
    det = _discriminant(G[i])
    sq = islocal_square(det, p)[1]
    @show i, mi, ri, sq, s[i]
    f = divexact(f, group_order(sq ? "O+" : "O-", mi, q))
    @show f
    N = N - s[i] * divexact(mi*(mi+1), 2) - s[i] * mi * ri
    @show N
    N = N + s[i] * mi * (m + 1)* 1//2 # volume?
    @show N
  end

  @show N

  if iseven(m) && isodd(valuation(d, p))
    N = N + fmpq(1 - m, 2)
  end

  @show N

  @assert isintegral(N)
  @show q^Int(FlintZZ(N)) * f

  return q^Int(FlintZZ(N)) * f
end

function mass_exact(L::QuadLat)
  fl, m = _exact_standard_mass(L)

  if fl
    return m * local_mass(L)
  end

  lm = local_mass(L)

  prec = 10
  mu = _minkowski_multiple(rank(L) * absolute_degree(nf(base_ring(L))))

  d = mu * numerator(lm)

  while true
    z = d * _standard_mass(L, prec)
    @show z
    fl, b = unique_integer(z)
    if fl
      return b//d * lm
    end
    prec += 1
  end
end

function _exact_standard_mass(L::QuadLat)
  m = rank(L)
  if m == 0
    return true, fmpq(1)
  elseif m == 1
    return true, fmpq(1, 2)
  end

  R = base_ring(L)
  K = nf(R)
  r = div(m, 2)

  fl = true

  standard_mass = FlintQQ(2)^(-absolute_degree(K) * r)
  if isodd(m)
    #standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-2))
    if _exact_dedekind_zeta_cheap(K, false)
      standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-2))
    else
      return false, fmpq(0)
    end
  else
    #standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-3))

    if _exact_dedekind_zeta_cheap(K, false)
      standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-3))
    else
      return false, fmpq(0)
    end

    dis = discriminant(rational_span(L))
    if issquare(dis)[1]
      if _exact_dedekind_zeta_cheap(K, false)
        standard_mass *= dedekind_zeta_exact(K, 1 - r)
      else
        return false, fmpq(0)
      end
    else
      Kt, t = PolynomialRing(K, "t", cached = false)
      E, = NumberField(t^2 - denominator(dis)^2 * dis, "b", cached = false)
      #standard_mass *= dedekind_zeta_exact(E, 1 - r, true)
      @show K, E
      if _exact_dedekind_zeta_cheap(E, true)
        standard_mass *= dedekind_zeta_exact(Eabs, 1 - r, true)
      else
        return false, fmpz(0)
      end
      #wprec = prec
      #local relzeta
      #while true
      #  @show zK = dedekind_zeta(K, 1 - r, wprec)
      #  Eabs, _ = absolute_field(E)
      #  @show zE = dedekind_zeta(Eabs, 1 - r, wprec)
      #  relzeta = zE//zK
      #  if radiuslttwopower(relzeta, -prec)
      #    break
      #  end
      #  wprec = wprec + 1
      #end
      #standard_mass *= relzeta
      ##standard_mass *= dedekind_zeta_exact(Eabs, 1 - r, prec, true)
    end
  end

  return true, standard_mass
end

function local_mass(L::QuadLat)
  lf = fmpq(1)

  for p in bad_primes(L, even = true)
    @show minimum(p), local_factor(L, p)
    lf *= local_factor(L, p)
  end

  return lf
end

function _standard_mass(L::QuadLat, prec::Int = 10)
  m = rank(L)
  if m == 0
    return fmpq(1)
  elseif m == 1
    return fmpq(1, 2)
  end

  R = base_ring(L)
  K = nf(R)
  r = div(m, 2)

  standard_mass = FlintQQ(2)^(-absolute_degree(K) * r)
  if isodd(m)
    #standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-2))
    standard_mass *= prod(dedekind_zeta(K, -i, prec) for i in 1:2:(m-2))
  else
    #standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-3))
    standard_mass *= prod(dedekind_zeta(K, -i, prec) for i in 1:2:(m-3))

    @show standard_mass

    dis = discriminant(rational_span(L))
    if issquare(dis)[1]
      #standard_mass *= dedekind_zeta_exact(K, 2 - r)
      standard_mass *= dedekind_zeta(K, 1 - r, prec)
    else
      Kt, t = PolynomialRing(K, "t", cached = false)
      E, = NumberField(t^2 - denominator(dis)^2 * dis, "b", cached = false)
      #standard_mass *= dedekind_zeta_exact(E, 1 - r, true)
      @show K, E
      wprec = prec
      local relzeta
      while true
        @show zK = dedekind_zeta(K, 1 - r, wprec)
        Eabs, _ = absolute_field(E)
        @show zE = dedekind_zeta(Eabs, 1 - r, wprec)
        relzeta = zE//zK
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
    return fmpq(1)
  elseif m == 1
    return fmpq(1, 2)
  end

  R = base_ring(L)
  K = nf(R)
  r = div(m, 2)

  if standard_mass == 0
    standard_mass = FlintQQ(2)^(-absolute_degree(K) * r)
    if isodd(m)
      #standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-2))
      standard_mass *= prod(dedekind_zeta(K, -i, prec) for i in 1:2:(m-2))
    else
      #standard_mass *= prod(dedekind_zeta_exact(K, -i) for i in 1:2:(m-3))
      standard_mass *= prod(dedekind_zeta(K, -i, prec) for i in 1:2:(m-3))

      @show standard_mass

      dis = discriminant(rational_span(L))
      if issquare(dis)[1]
        #standard_mass *= dedekind_zeta_exact(K, 2 - r)
        standard_mass *= dedekind_zeta(K, 1 - r, prec)
      else
        Kt, t = PolynomialRing(K, "t", cached = false)
        E, = NumberField(t^2 - denominator(dis)^2 * dis, "b", cached = false)
        #standard_mass *= dedekind_zeta_exact(E, 1 - r, true)
        @show K, E
        wprec = prec
        local relzeta
        while true
          @show zK = dedekind_zeta(K, 1 - r, wprec)
          Eabs, _ = absolute_field(E)
          @show zE = dedekind_zeta(Eabs, 1 - r, wprec)
          relzeta = zE//zK
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

  @show mass

  lf = fmpq(1)

  for p in bad_primes(L, even = true)
    @show minimum(p), local_factor(L, p)
    lf *= local_factor(L, p)
  end

  return mass, lf
end

function mass(L::QuadLat, prec::Int = 10)
  m, lf = _mass(L, 0, prec)
  return m * lf
end

# Local factor for dyadic unramified p S. Cho.
function _local_factor_cho(L, p)
  @assert isdyadic(p) && ramification_index(p) == 1
  @show "here"
  @show p
  m = rank(L)
  R = base_ring(L)
  K = nf(R)
  _, G, S = jordan_decomposition(L, p)
  k, h = ResidueField(R, p)
  hext = extend(h, K)
  V = []

  for s in S
    #@show s
    AG = diagonal_matrix([2^(S[j] < s ? 2*(s - S[j]) : 0) * G[j] for j in 1:length(G)])
    _,B = left_kernel(matrix(k, nrows(AG), 1, [hext(d//2^s) for d in diagonal(AG)]))
    @assert all(issquare(x)[1] for x in B)
    B = map_entries(x -> sqrt(x), B)
    #B:= Matrix(k, Ncols(B), [ Sqrt(x): x in Eltseq(B) ]);

    #@show matrix(k, nrows(AG), 1, [hext(d//2^s) for d in diagonal(AG)])
    BK = map_entries(x -> hext\x, B)
    #@show BK
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

    #@show Q
    Q = map_entries(hext, Q)
    #@show Q

    BB = []
    for i in 1:nrows(B)
      b = zero_matrix(k, 1, nrows(B))
      b[1, i] = 1
      push!(BB, b)
    end

    #@show BB
    #@show Q + transpose(Q)
    #@show matrix(k, length(BB), length(BB), [ (b * Q * transpose(c))[1, 1] + (c * Q * transpose(b))[1, 1] for b in BB, c in BB])
    @assert matrix(k, length(BB), length(BB), [ (b * Q * transpose(c))[1, 1] + (c * Q * transpose(b))[1, 1] for b in BB, c in BB]) == Q + transpose(Q)

#    assert Matrix(k, #BB, [ (b*Q, c) + (c*Q, b): b, c in BB ]) eq Q + Transpose(Q);
#
    _, N = left_kernel(Q + transpose(Q))
    #@show N
    ok = isdiagonal(N * Q * transpose(N))
    @assert ok
    D = diagonal(N * Q * transpose(N))
    #@show N * Q * transpose(N)
    #@show D

    @assert ok
    #@show matrix(k, length(D), 1, D)
    _, rad = left_kernel(matrix(k, length(D), 1, D))

    rad = rad * N

    #@show rad

    VV = vector_space(k, nrows(B))

    SS, mSS = sub(VV, [ VV([rad[i, j] for j in 1:ncols(rad) ]) for i in 1:nrows(rad)])
    W, g = quo(VV, SS)

    @assert length(rels(W)) == 0

    if ngens(W) == 0
      push!(V, (s, zero_matrix(k, 0, 0)))
    else
      #@show Q
      #@show [ preimage(g, w) for w in gens(W)]
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

  M = [ ncols(g) for g in G]

  PT = [ valuation(norm(quadratic_lattice(K, identity_matrix(K, nrows(G[i])), gram_ambient_space = G[i])), p) == S[i] for i in 1:length(S) ] # parity type I
  # could try with # get_norm_valuation_from_gram_matrix(G[i], p)
  #
  alpha = []
  #@show PT
  #@show M
  for i in 1:length(G)
    j = findfirst(v -> v[1] == S[i], V)
    @assert j !== nothing
    v = V[j]
    if ncols(v[2]) != 0 && (!((S[i] - 1) in S) || !(PT[i-1])) && (!((S[i] + 1) in S) || !PT[i + 1])
      push!(alpha, i)
    end
  end

  beta = []
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

    #@show QFT

    #@show fmpq(group_order(QFT, mi, q))//2

    res *= fmpq(group_order(QFT, mi, q))//2
    #@show res
  end

  #@show res

  beta = fmpq(1, 2) * q^N * res

  exp = fmpq(m + 1, 2) * sum(S[i] * M[i] for i in 1:length(S)) # from det

  #@show exp

  if isodd(m)
    exp += fmpq(m + 1, 2)
    H = group_order("O", m, q)
  else
    exp += m
    d = discriminant(ambient_space(L))
    #@show d
    #@show exp
    if islocal_square(d, p)
      #@show "locals"
      H = group_order("O+", m, q)
    else
      #@show "localns"
      Kt, t = PolynomialRing(K, "t", cached = false)
      E, = number_field(t^2 - denominator(d)^2 * d) # broken for non-integral polynomials
      v = valuation(discriminant(maximal_order(E)), p)
      #@show v
      if v == 0
        H = group_order("O-", m, q)
      else
        H = group_order("O", m - 1, q)
        exp += v * fmpq(1 - m, 2)
      end
    end
  end

  #@show exp

  @assert isintegral(exp)

  return q^Int(FlintZZ(exp)) * H//2 * fmpq(1)//beta
end

################################################################################
#
#  Exact values of Dedekind zeta values
#
################################################################################

function _exact_dedekind_zeta_cheap(K, relative = false)

  if absolute_degree(K) == 1
    return true
  elseif absolute_degree(K) == 2 && istotally_real(K)
    return true
  end

  return false
end

function _eval_dedekind_zeta(K, z, relative)
  if isodd(z)
    k = 1 - z
    if absolute_degree(K) == 1
      return bernoulli(k)//-k
    elseif absolute_degree(K) == 2 && istotally_real(K)
      d = discriminant(maximal_order(K))
      if relative
        return _bernoulli_kronecker(k, d)//-k
      else
        return bernoulli(k) * _bernoulli_kronecker(k, d)//k^2
      end
    else
      throw(NotImplemented())
    end
  else
    throw(NotImplemented())
  end
end

function dedekind_zeta_exact(K, z, relative = false)
  #{Evaluates the Dedekind zeta function of K at the negative integer z}
  @req (relative && z == 0 || z < 0) "The argument must be a negative integer"
  return _eval_dedekind_zeta(K, z, relative)
end

function _modulus_of_kronecker_as_dirichlet(D)
  return abs(fundamental_discriminant(D))
end

function _bernoulli_kronecker(z, D)
  @assert z >= 0
  N = _modulus_of_kronecker_as_dirichlet(D)
  K = FlintQQ
  Rt, t = PowerSeriesRing(K, z + 3, "t", cached = false, model = :capped_absolute)
  denom = exp(N*t) - 1
  num = sum(_kronecker_as_dirichlet(a, N) * t * exp(a * t) for a in 1:Int(N))
  F = divexact(num, denom)
  p = precision(F)
  @assert p >= z + 1
  return coeff(F, z) * factorial(fmpz(z))
end

function _kronecker_as_dirichlet(n, D)
  if gcd(n, D) == 1
    return _kronecker_symbol(_modulus_of_kronecker_as_dirichlet(D), n)
  end
  return 0
end

function _kronecker_symbol(n, m)
  e, mm = remove(m, 2)
  res = _jacobi_symbol(n, mm)
  if e > 0 && iseven(n)
    return 0
  end
  if isodd(e)
    nmod8 = n % 8
    if nmod8 < 0
      nmod8 += 8
    end
    if nmod8 == 3 || nmod8 == 5
      res = res * -1
    end
  end
  return res
end

# don't use this, this is slow
function _jacobi_symbol(n, m)
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
#  Dedekind zeta function evaluation a la Tollis
#
################################################################################

# This does not work at the moment.

mutable struct ZetaFunction
  K::AnticNumberField
  coeffs::Vector{fmpz}
  dec_types

  function ZetaFunction(K::AnticNumberField)
    z = new()
    z.K = K
    z.coeffs = fmpz[]
    dec_types = []
    return z
  end
end

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
    return fmpz(1)
  elseif n > 1 && h == 0
    return fmpz(0)
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
  return sum(fmpq(1, fmpz(j)^k) for j in 1:Int(q))
end

function _compute_g_function_coefficients_even(i, n, r1, r2, CC::AcbField)
  @assert i % 2 == 0
  q = div(i, 2)
  res = Vector{acb}(undef, n + 1)
  res[1] = zero(CC)
  RR = ArbField(prec(CC))
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
  z = z//(CC(factorial(fmpz(q)))^r1 * (CC(factorial(2*fmpz(q))))^r2)
  return z
end

function _compute_Aij_even(i, r1, r2, CC::AcbField)
  CCx, x = LaurentSeriesRing(CC, r1 + r2 + 2, "x", cached = false)
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
  RR = ArbField(prec(CC))
  for k in 1:n
    z = (-1)^k * (k == 1 ? CC(const_euler(RR)) : zeta(CC(k))) * (r1 * (1 - CC(2)^-k) + r2)
    z = z + CC(r1 + r2) * _Hqk(i, k) - CC(r2)//CC(2)^k * _Hqk(q, k) - (k > 1 ? CC(0) : CC(r1) * CC(log(RR(2))))
    res[k + 1] = z//CC(k)
  end
  return res
end

function _compute_premultiplier_odd(i, r1, r2, CC::AcbField)
  q = div(i - 1, 2)
  z = (-1)^(mod((q + 1)*r1 + r2, 2)) * const_pi(CC)^(r1//2) * CC(2)^((2*q + 1)*r1) * CC(factorial(fmpz(q)))^r1 # does this overflow one of the exponents?
  z = z//(CC(factorial(fmpz(i)))^(r1 + r2))
  return z
end

function _compute_Aij_odd(i, r1, r2, CC::AcbField)
  CCx, x = LaurentSeriesRing(CC, r1 + r2 + 2, "x", cached = false)
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
    throw(error("asdsd"))
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
  throw(error("Ads"))
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
      z += _compute_Aijs(i, j, s, r1, r2, CC) * (1//x)^i * (log(x))^(j - 1)//CC(factorial(fmpz(j-1)))
    end
  end

  for j in 1:(r1 + r2 + 1)
    z += _compute_Aijs(-s, j, s, r1, r2, CC) * x^s * (log(x))^(j - 1)//CC(factorial(fmpz(j - 1)))
  end
  return z
end

function _tollis_f(x, s::acb, i0, r1, r2, CC)
  z = zero(CC)
  @show "tollis f $x $s"
  for j in 1:(r1 + r2)
    for i in 0:i0
      z += _compute_Aijs(i, j, s, r1, r2, CC) * (1//x)^i * (log(x))^(j - 1)//CC(factorial(fmpz(j-1)))
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
      w = (CC(n)//CK)^i * log(CK//n)^(j-1)//CC(factorial(fmpz(j - 1)))
      #@show (i, k, n, j, w)
      y = y * w
      @assert isfinite(y)
      z += y
    end
  end
  @assert isfinite(z)
  return z
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
  @show s, T
  while p <= T
    dectyp = prime_decomposition_type(OK, p)
    for (f, e) in dectyp
      z = z * inv(1 - RR(p^f)^(-s))
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
  RR = ArbField(128)
  d = degree(K)
  
  local_cor = prod(arb[_local_correction(K, p, RR) for p in primes_up_to(100)])
  @show local_cor

  b = local_cor * zeta(RR(s))^d * (RR(d) + 1)//(RR(s - 1))//(RR(2))^(-(prec + 1))
  b = root(b, s - 1)
  T = upper_bound(b, fmpz)
  # z_K(s) - truncated at T < 1/2^(prec + 1)
  @assert fits(Int, T)
  Tint = Int(T)

  @show Tint

  otherbound = local_cor * zeta(RR(s))^d * ((1 +1//((s - 1) * RR(div(Tint, 2))^(s - 1)))^d - 1)
  @show otherbound
  @show RR(2)^(-prec - 1)
  while otherbound < RR(2)^(-prec - 1)
    @show Tint
    Tint = div(Tint, 2)
    otherbound = local_cor * zeta(RR(s))^d * ((1 + 1//((s - 1) * RR(div(Tint, 2))^(s - 1)))^d - 1)
  end

  otherbound = zeta(RR(s))^d * ((1 + 1//((s - 1) * RR(Tint)^(s - 1)))^d - 1)
  @assert radiuslttwopower(otherbound, -prec - 1)

  @show Tint

  wprec = 3 * prec

  error_arf = arf_struct(0, 0, 0, 0)
  ccall((:arf_set_si_2exp_si, libarb), Nothing,
        (Ref{arf_struct}, Int, Int), error_arf, Int(1), Int(-(prec + 1)))

  local valaddederror

  while true
    @show wprec
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

  return valaddederror
end

function _dedekind_zeta_attwell_duval_negative(K::AnticNumberField, s, target_prec::Int)
  @assert s < 0
  if iseven(s)
    return zero(ArbField(target_prec))
  end
  sp = 1 - s
  z = _dedekind_zeta_attwell_duval_positive(K, sp, target_prec + 1)
  zprec = prec(parent(z))
  wprec = zprec * 2
  RR = ArbField(wprec)
  dK = abs(discriminant(maximal_order(K)))
  d = degree(K)

  local res

  @show sp

  i = 1

  while true
    RR = ArbField(wprec)
    CK = RR(dK)//(const_pi(RR)^d * 2^d)
    prefac = (-1)^(div(d * sp, 2)) * CK^sp * (2 * RR(factorial(fmpz(sp) - 1)))^d//sqrt(RR(dK))
    res = z * prefac
    if radiuslttwopower(res, -target_prec)
      break
    end
    wprec = 2 * wprec
    i += 1
    z = _dedekind_zeta_attwell_duval_positive(K, sp, target_prec + i)
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

function group_order(G::String, m::Int, q::fmpz)
  if G[1] != 'O'
    if G[1] == 'G' # GL_m
      o = prod(fmpq[ 1 - fmpq(q)^(-j) for j in 1:m ])
    elseif G[1] == 'U' # U_m
      o = prod(fmpq[ 1 - fmpq(-q)^(-j) for j in 1:m ])
    else # Default Sp_m
      o = prod(fmpq[ 1 - fmpq(q)^(-j) for j in 1:div(m, 2) ])
    end
  else # orthogonal case
    if iseven(m)
      k = div(m, 2)
      e = G[2] == '+' ? 1 : -1
      o = 2 * (1 - e * fmpq(q)^(-k)) * prod(fmpq[ 1 - fmpq(q)^(-j) for j in 2:2:(m-2)])
    else
      o = 2 * prod(fmpq[1 - fmpq(q)^(-j) for j in 2:2:m])
    end
  end
  return o
end

function quadratic_form_type(v)
  return _orthogonal_signum_even(v + transpose(v), v)
end

function _orthogonal_signum_even(form, quad)
	# Bring symmetric form into standard form
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
  Rt, t = PolynomialRing(base_ring(form), "t", cached = false)
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
        if !isirreducible(pol)
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

function _multiple_of_finite_group_order_glnz(n::Int)
  return _minkowski_multiple(n)
end

function _minkowski_multiple(n)
  if n == 1
    return fmpz(1)
  elseif n == 2
    return fmpz(24)
  elseif n == 3
    return fmpz(48)
  else
    if isodd(n)
      return 2 * _minkowski_multiple(n - 1)
    else
      return denominator(divexact(bernoulli(n), n)) * _minkowski_multiple(n - 1)
    end
  end
end
