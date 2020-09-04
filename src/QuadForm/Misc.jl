# Return an element Delta, such that K_p(\sqrt{Delta}) is the unique quadratic unramified extension.

@doc Markdown.doc"""
    kummer_generator_of_local_unramified_quadratic_extension(p::Idl) -> NumFieldElem

Given a dyadic prime ideal $\mathfrak p$ of a number field $K$, return a local
unit $\Delta$, such that $K(\sqrt(\Delta))$ is unramified at $\mathfrak p$.
"""
function kummer_generator_of_local_unramified_quadratic_extension(p)
  @assert isdyadic(p)
  K = nf(order(p))
  k, h = ResidueField(order(p), p)
  kt, t = PolynomialRing(k, "t", cached = false)
  a = rand(k)
  f = t^2 - t + a
  while !isirreducible(f)
    a = rand(k)
    f = t^2 - t + a
  end
  Kt, t = PolynomialRing(K, "t", cached = false)
  g = t^2 - t + elem_in_nf(h\a)
  aa = elem_in_nf(h\a)
  gg = evaluate(g, inv(K(2)) * (t + 1))
  @assert iszero(coeff(gg, 1))
  D = -coeff(gg, 0) * 4
  @assert quadratic_defect(D, p) == valuation(4, p)
  DD = -4 * aa + 1
  @assert D == DD
  @assert quadratic_defect(DD, p) == valuation(4, p)
  return DD
end

# {Given a unit at the prime p, find a local unit v in the same square class such that v-1 generates the quadratic defect of u}

function _find_special_class(u, p)
  R = order(p)
  K = nf(R)
  @assert valuation(u, p) == 0
  k, _h = ResidueField(R, p)
  h = extend(_h, K) 
  fl, s = issquare(h(u))
  @assert fl
  u = divexact(u, (h\s)^2)
  @assert isone(h(u))
  e = valuation(2, p)
  pi = elem_in_nf(uniformizer(p))
  val = isone(u) ? inf : valuation(u - 1, p)
  while val < 2 * e 
    if isodd(val)
      return u
    end
    fl, s = issquare(h((u - 1)//pi^val))
    @assert fl 
    # TODO:FIXME the div is wrong for negative valuations I think
    @assert val >= 0
    u = divexact(u, (1 + (h\s) * pi^(div(val, 2)))^2)
    val = valuation(u - 1, p) 
  end
  kt, t = PolynomialRing(k, "t", cached = false)
  return val == 2 * e && isirreducible(kt([h(divexact(u - 1, 4)), one(k), one(k)])) ? u : one(K)
end

################################################################################
#
#  Should go somewhere else
#
################################################################################

function image(f::NfToNfRel, I::NfAbsOrdIdl, OK)
  return reduce(+, (OK(f(elem_in_nf(b))) * OK for b in basis(I)), init = 0 * OK)
end

function image(f::NfToNfRel, I::NfAbsOrdIdl)
  OK = maximal_order(codomain(f))
  return image(f, I, OK)
end

function image(f::NfRelToNfRelMor{nf_elem, nf_elem}, I::NfRelOrdIdl)
  OK = order(I)
  return reduce(+, (OK(f(elem_in_nf(b))) * OK for b in absolute_basis(I)), init = 0 * OK)
end

function preimage(f::NfToNfRel, I::NfRelOrdIdl, OK)
  return reduce(+, (OK(f\(b)) * OK for b in absolute_basis(I)), init = 0 * OK)
end

function preimage(f::NfToNfRel, I::NfRelOrdIdl)
  OK = maximal_order(domain(f))
  return preimage(f, I, OK)
end

################################################################################
#
#  "Strong" approximation
#
################################################################################

#absolute_minimum(I::NfAbsOrdIdl) = minimum(I)

# Cohen 1.3.11
function _strong_approximation(S, ep, xp)
  OK = order(S[1])
  if length(S) > 1
    @assert sum(S) == 1 * OK
  end
  if all(x -> x >= 0, ep) && all(isintegral, xp)
    return _strong_approximation_easy(S, ep, xp)
  else
    d = reduce(lcm, (denominator(x) for x in xp), init = one(fmpz))
    for i in 1:length(S)
      l = valuation(d, S[i]) - ep[i]
      if l < 0
        d = d * absolute_minimum(S[i])^(l)
      end
      @assert valuation(d, S[i]) + ep[i] >= 0
    end
  end
  _ep = fmpz[]
  _xp = nf_elem[]
  _S = support(d * OK)
  _SS = ideal_type(OK)[]
  for i in 1:length(S)
    push!(_ep, ep[i] + valuation(d, S[i]))
    push!(_xp, d * xp[i])
    push!(_SS, S[i])
  end
  for p in _S
    if !(p in _SS)
      push!(_ep, valuation(d, p))
      push!(_xp, zero(nf(OK)))
      push!(_SS, p)
    end
  end

  y = _strong_approximation_easy(_SS, _ep, _xp)
  z = y//d

  for i in 1:length(ep)
    @assert valuation(xp[i] - z, S[i]) == ep[i]
  end
  return z
end

function _strong_approximation_easy(S, ep, xp)
  if length(S) == 1
    p = S[1]
    ap = uniformizer(p)
    z = xp[1] - ap^(ep[1])
    @assert valuation(xp[1] - z, S[1]) == ep[1]
    @assert z == 0 || all(p -> (valuation(z, p) >= 0 || p in S), support(z * order(S[1])))
    return z
  end
  OK = order(S[1])
  # assume ep non-negative and xp in R
  I = reduce(*, (S[i]^(ep[i] + 1) for i in 1:length(S)), init = 1 * OK)
  aps = ideal_type(OK)[]
  bps = elem_type(nf(OK))[]
  for i in 1:length(S)
    bp = elem_in_nf(uniformizer(S[i]))^(ep[i])
    push!(bps, bp)
    ap = divexact(I, S[i]^(ep[i] + 1))
    @assert ap * S[i]^(ep[i] + 1) == I
    push!(aps, ap)
  end
  as = _idempotents(aps)
  for i in 1:length(as)
    @assert as[i] in aps[i]
  end
  @assert sum(as) == one(OK)
  @assert length(as) == length(aps)
  z = elem_in_nf(reduce(+, (as[i]* (xp[i] + bps[i]) for i in 1:length(as)), init = zero(OK)))
  for i in 1:length(ep)
    @assert valuation(z - xp[i], S[i]) == ep[i]
  end
  return z
end

function _idempotents(x::Vector)
  @assert length(x) >= 2

  k = length(x)
  O = order(x[1])
  @assert sum(x) == 1 * O
  d = degree(O)
  # form the matrix
  #
  # ( 1 |  1  | 0 )
  # ( 0 | M_x | I )
  # ( 0 | M_y | 0 )

  V = zero_matrix(FlintZZ, d * k + 1, d * k + 1)

  u = coordinates(one(O))

  V[1, 1] = 1

  for i in 1:d
    V[1, i + 1] = u[i]
  end

  for i in 1:k
    VV = view(V, (2 + (i - 1)*d):(2 + i*d - 1), 2:(2 + d))
    B = basis_matrix(x[i], copy = false)
    for m in 1:d
      for n in 1:d
        VV[m, n] = B[m, n]
      end
    end
  end

  #println("V:\n", sprint(show, "text/plain", V))

  for i in 1:(k - 1)
    VV = view(V, (2 + (i-1)*d):(2 + i*d - 1), (i*d + 2):((i + 1)*d + 1))
    for m in 1:d
      VV[m, m] = 1
    end
    #println("V:\n", sprint(show, "text/plain", V))
  end

  #println("V:\n", sprint(show, "text/plain", V))

  m = lcm(fmpz[minimum(x[i], copy = false) for i in 1:length(x)])
 
  H = hnf_modular_eldiv!(V, m) # upper right

  for i in 2:(1 + d)
    if H[1, i] != 0
      error("Ideals are not coprime")
    end
  end

  els = elem_type(O)[]

  #println("H:\n", sprint(show, "text/plain", H))

  for i in 1:(k - 1)
    B = basis(x[i], copy = false)
    z = zero(O)
    for j in 1:d
      z += H[1, 1 + j + (i)*d] * B[j]
    end
    push!(els, z)
  end

  @assert one(O) + sum(els[i] for i in 1:length(els)) in x[end]

  push!(els, (one(O) + sum(els[i] for i in 1:k - 1)))
  for i in 1:length(els) - 1
    els[i] = -els[i]
  end
  @assert sum(els) == one(O)
  return els
end


