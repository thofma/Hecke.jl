### Attempt of a "generic" implementation for roots of a polynomial over a local
#   field
#
# Does work at most for polynomials without multiple roots.

# Everything is inspired by the implementation in characteristic 0 in
# src/LocalField/automorphisms.jl
#
# The main idea seems to be to follow the factorization algorithm described in
#
# Carlo Sircana, "Factoring polynomials over ZZ/(n)", Master's Thesis,
#   Università di Pisa, 2016, http://poisson.phc.dm.unipi.it/~sircana/tesi1.pdf
#
# or
#
# Sebastian Pauli, "Factoring Polynomials over Local Fields II",
#   Algorithmic Number Theory, pages 301–315, 2010
#   https://mathstats.uncg.edu/sites/pauli/publications/pauli_factoring-polynomial-over-local-fields.pdf
#
# The basic idea is:
#  * Do a factorization over the residue field and lift it up (Hensel factorization)
#  * Do a squarefree factorization of every factor that splits over the residue field
#  * Do a "slope factorization" of the squarefree factors to separate the roots
#
# The algorithm assumes (seems to assume) that the coefficients of the polynomial
# have non-negative valuation.
#
# Known problems:
#  * Requires a squarefree factorization, which we don't have in characteristic p > 0.
#  * Currently, polynomials are moved around a lot between the field, the valuation
#    ring and residue rings. This is mathematically nice, but somehow cumbersome.
#  * It is not clear what the theoretical assumption on the polynomial are:
#    integral?, squarefree?, separable?
#  * See the TODOs.

function roots(f::PolyRingElem{<: NonArchLocalFieldElemTypes})
  K = base_ring(f)
  if is_zero(f)
    return elem_type(K)[]
  end

  # Make the polynomial integral
  v = minimum(_valuation_integral, Iterators.filter(!is_zero, coefficients(f)))
  if v < 0
    f *= uniformizer(K)^-v
  end

  R = valuation_ring(K)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fR = Rx([R(c) for c in coefficients(f)])

  return _roots(fR)
end

# This also returns non-integral roots
function _roots(f::PolyRingElem{<: NonArchLocalFieldValuationRingElem})
  R = base_ring(f)
  Rx = parent(f)
  K = _field(R)
  res = elem_type(K)[]
  if is_zero(f)
    return res
  end

  f = divexact(f, _content(f))

  S, RtoS = residue_ring(R, uniformizer(R)^precision(f))
  Sx, _ = polynomial_ring(S, "x", cached = false)
  fS = map_coefficients(c -> S(c, check = false), f, parent = Sx)

  if !is_zero(valuation(leading_coefficient(f)))
    gS, fS = fun_factor(fS)
    # Now fS is monic and gS has a constant term of valuation zero,
    # so we can proceed with fS and reverse(gS) for the Hensel step
    f = map_coefficients(c -> lift(c), fS, parent = Rx)
    g = map_coefficients(c -> lift(c), gS, parent = Rx)
    res = [inv(a) for a in _roots(reverse(g))]
  end

  # First do a "Hensel factorization": factor fS over the residue field and
  # lift the factorization up.
  # It is not clear what the best way of representing f is for this.
  # Using the residue ring S is mathematical precise, but requires moving f
  # around between the different rings. In the implementation in characteristic
  # 0 one always works with a polynomial over the field and simply adjusts the
  # precision of the coefficients for the lifting.
  h_factor = Hensel_factorization(fS)
  for (gS, hS) in h_factor
    # (gS, hS) are pairs of irreducible factors gS over the residue field and
    # their Hensel lifts hS to S
    # If gS is not of degree 1, then hS cannot have any zeros.
    !is_one(degree(gS)) && continue

    # gS is of degree 1, so hS splits over the residue field

    if is_one(degree(hS))
      # Easy case, we found a root
      h = map_coefficients(c -> lift(c), hS, parent = Rx)
      push!(res, -K(constant_coefficient(h))//K(leading_coefficient(h)))
      continue
    end

    # TODO: Now we need to do a squarefree factorization of hS as the slope
    # factorization only works if the roots are distinct. Possibly, this
    # should be done right at the beginning (before the Hensel factorization).
    # In the characteristic 0 implementation, it is done as part of
    # slope_factorization.

    @assert is_unit(leading_coefficient(hS))

    # Do a slope factorization (see references above) to split hS. This should
    # be called for every squarefree factor of hS.
    h = map_coefficients(c -> lift(c), hS, parent = Rx)
    g = map_coefficients(c -> lift(c), gS, parent = Rx)
    s_factor = slope_factorization(h, g)
    for (p, e) in s_factor
      if is_one(degree(p))
        for _ in 1:e
          push!(res, -K(constant_coefficient(p))//K(leading_coefficient(p)))
        end
        continue
      end

      # In src/LocalField/automorphisms.jl, there is a function _roots implemented
      # I don't know what this is doing.
      # TODO: do more? like in _roots?
    end
  end
  return res
end

function _content(f::PolyRingElem{<:LocalFieldValuationRingResidueRingElem})
  R = base_ring(f)
  fO = map_coefficients(lift, f)
  return R(_content(fO))
end

# Return (g, h) with f = g*h, h a monic polynomial and g a unit in the polynomial ring
function fun_factor(f::PolyRingElem{T}) where T <: LocalFieldValuationRingResidueRingElem
  @assert is_one(_content(f))

  Rx = parent(f)
  R = coefficient_ring(Rx)
  K = _field(R)

  if is_unit(leading_coefficient(f))
    return Rx(leading_coefficient(f)), divexact(f, leading_coefficient(f))
  end

  ind = degree(f) - 1
  while !is_unit(coeff(f, ind))
    ind -= 1
  end

  g = Rx([coeff(f, i) for i in ind:degree(f)])
  h = Rx([divexact(coeff(f, i), coeff(f, ind)) for i in 0:ind])
  s = Rx(inv(coeff(f, ind)))
  t = zero(Rx)

  # We now have f = g*h mod pi, where pi is a uniformizer in K and lift this up
  # to a solution mod pi^e via Hensel.
  # Note: s*g + t*h = 1 mod pi.

  step = 1
  while step < _exponent(R)
    step *= 2
    S = LocalFieldValuationRingResidueRing(valuation_ring(K), step)
    Sx, x = polynomial_ring(S, "x", cached = false)
    fSx = map_coefficients(x -> S(lift(x), check = false), f, parent = Sx)
    g = map_coefficients(x -> S(lift(x), check = false), g, parent = Sx)
    h = map_coefficients(x -> S(lift(x), check = false), h, parent = Sx)
    s = map_coefficients(x -> S(lift(x), check = false), s, parent = Sx)
    t = map_coefficients(x -> S(lift(x), check = false), t, parent = Sx)
    g, h, s, t = _hensel(fSx, g, h, s, t)
    @assert g*h == fSx
    @assert s*g + t*h == one(Sx)
  end
  g = map_coefficients(x -> R(lift(x), check = false), g, parent = Rx)
  h = map_coefficients(x -> R(lift(x), check = false), h, parent = Rx)
  @assert is_one(leading_coefficient(h))
  return g, h
end

function Hensel_factorization(f::PolyRingElem{<: LocalFieldValuationRingResidueRingElem})
  @assert !is_zero(f)
  @assert is_one(_content(f))
  @assert is_unit(leading_coefficient(f))

  R = base_ring(f)
  Rx = parent(f)

  res = Dict{typeof(f), typeof(f)}()

  K = _field(R)
  k, Ktok = residue_field(K)
  # TODO: Would be nice if we could efficiently map from R to k (without going via K)

  kt, _ = polynomial_ring(k, "t", cached = false)
  fk = map_coefficients(c -> Ktok(K(lift(c))), f, parent = kt)

  lfk = factor(fk)
  if length(lfk) == 1
    #The Hensel factorization is trivial...
    g, _ = only(lfk)
    phi = map_coefficients(c -> R(Ktok\c, check = false, copy = false), g, parent = Rx)
    res[phi] = f
    return res
  end

  vlfk = Vector{dense_poly_type(elem_type(k))}(undef, length(lfk))
  ind = 1
  gs = Vector{typeof(f)}(undef, length(vlfk))
  for (g, v) in lfk
    vlfk[ind] = g^v
    gs[ind] = map_coefficients(c -> R(Ktok\c, check = false, copy = false), g, parent = Rx)
    ind += 1
  end
  H = HenselCtxdr{elem_type(R)}(f, vlfk)
  lift(H, _exponent(R))
  for i in 1:H.n
    res[gs[i]] = H.lf[i]
  end
  return res
end

function lift(C::HenselCtxdr{<: LocalFieldValuationRingResidueRingElem}, mx::Int)
  if length(C.lf) == 1
    return nothing
  end
  Rx = parent(C.f)
  R = coefficient_ring(Rx)
  K = _field(R)
  N = _exponent(coefficient_ring(parent(C.lf[1])))
  ch = Int[mx]
  while ch[end] > N
    push!(ch, div(ch[end]+1, 2))
  end
  for k in length(ch) - 1:-1:1
    N2 = ch[k]
    i = length(C.lf)
    j = i - 1

    RN2 = LocalFieldValuationRingResidueRing(valuation_ring(K), N2)
    RN2x, _ = polynomial_ring(RN2, "x", cached = false)
    p = uniformizer(RN2, ch[k + 1])
    while j > 0
      if i == length(C.lf)
        f = map_coefficients(x -> RN2(lift(x), check = false), C.f, parent = RN2x)
      else
        f = map_coefficients(x -> RN2(lift(x), check = false), C.lf[i], parent = RN2x)
      end
      #formulae and names from the Flint doc
      h = C.lf[j]
      g = C.lf[j - 1]
      b = C.la[j]
      a = C.la[j - 1]
      h = map_coefficients(x -> RN2(lift(x), check = false), h, parent = RN2x)
      g = map_coefficients(x -> RN2(lift(x), check = false), g, parent = RN2x)
      a = map_coefficients(x -> RN2(lift(x), check = false), a, parent = RN2x)
      b = map_coefficients(x -> RN2(lift(x), check = false), b, parent = RN2x)
      fgh = divexact(f - g * h, p)
      G = rem(fgh * b, g) * p + g
      H = rem(fgh * a, h) * p + h
      t = divexact((one(RN2x) - a * G - b * H), p)
      B = rem(t * b, g) * p + b
      A = rem(t * a, h) * p + a
      if i < length(C.lf)
        C.lf[i] = G * H
      end
      C.lf[j - 1] = G
      C.lf[j] = H
      C.la[j - 1] = A
      C.la[j] = B
      i -= 1
      j -= 2
    end
  end
  return nothing
end

# f = phi^k modulo the uniformizer for some k
# Probably assumes that f is squarefree
function slope_factorization(f::PolyRingElem{T}, phi::PolyRingElem{T}) where {T <: NonArchLocalFieldValuationRingElem}
  @assert is_unit(leading_coefficient(f))

  R = base_ring(f)
  Rx = parent(f)
  K = _field(R)
  Kx, x = polynomial_ring(K, "x", cached = false)

  res = Dict{typeof(f), Int}()
  if degree(phi) == degree(f)
    res[f] = 1
    return res
  end

  fact = Vector{typeof(f)}()
  g = f
  phiK = map_coefficients(c -> K(c), phi, parent = Kx)
  gK = map_coefficients(c -> K(c), g, parent = Kx)
  NP = newton_polygon(f, phi)
  L = lines(NP)
  L1 = sort(L, rev = true, by = x -> slope(x))
  last_s = QQFieldElem(0)
  for l in L1
    if l == L1[end]
      push!(fact, g)
      break
    end
    s = slope(l)
    mu = phiK^Int(denominator(s)) * uniformizer(K, Int(numerator(s)))

    chi = characteristic_polynomial(gK, mu)
    S, _ = residue_ring(R, uniformizer(R)^precision(chi))
    chiS = map_coefficients(c -> S(c), chi)
    Sx = parent(chiS)
    hchi = Hensel_factorization(chiS)
    for (p, h) in hchi
      if p == gen(Sx)
        continue
      end
      hK = map_coefficients(c -> K(lift(c)), h, parent = Kx)
      com = hK(mu)
      com = divexact(com, _content(com))
      gc = gcd(com, gK)
      @assert degree(gc) > 0
      #if degree(gc) < 1
      #  continue
      #end
      push!(fact, map_coefficients(c -> R(c), gc, parent = Rx))
      gK = divexact(gK, gc)
      g = map_coefficients(c -> R(c), gK, parent = Rx)
    end
  end
  for g in fact
    res[g] = 1
  end
  return res
end
