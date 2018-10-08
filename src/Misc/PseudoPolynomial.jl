mutable struct PseudoPoly{S, T}
  poly::S
  coeff::T
  
  function PseudoPoly{S, T}(f::S, A::T) where {S, T}
    return new{S, T}(f, A)
  end
end

function PseudoPoly(f::S, A::T) where {S, T}
  return PseudoPoly{S, T}(f, A)
end

iszero(f::PseudoPoly) = iszero(polynomial(f))

base_ring(f::PseudoPoly) = parent(polynomial(f))

pseudo_polynomial(f, A) = PseudoPoly(f, A)

polynomial(f::PseudoPoly) = f.poly

coefficient_ideal(f::PseudoPoly) = f.coeff

pseudo_polynomial(f) = pseudo_polynomial(f, one(base_ring(f)) * maximal_order(base_ring(f)))

leading_coefficient(f::PseudoPoly) = leading_coefficient(polynomial(f)) * coefficient_ideal(f)

leading_monomial(f::PseudoPoly) = leading_monomial(polynomial(f))

################################################################################
#
#  Reduction
#
################################################################################

function can_reduce(f::PseudoPoly{S, T}, G::Array{PseudoPoly{S, T}, 1}) where {S, T}
  lmf = leading_monomial(polynomial(f))
  I = [ i for i in 1:length(G) if divides(leading_monomial(f), leading_monomial(G[i]))[1]]
  if isempty(I)
    return false, f
  end
  b = leading_coefficient(f)//sum(leading_coefficient(G[i]) for i in I)
  simplify(b)
  if isone(denominator(b))
    c = sum(leading_coefficient(G[i]) for i in I)//coefficient_ideal(f)
    l = _contains(leading_coefficient(polynomial(f)), [leading_coefficient(G[i])//coefficient_ideal(f) for i in I])
    l = [ l[i]//leading_coefficient(polynomial(G[I[i]])) for i in 1:length(I)]
    g = deepcopy(polynomial(f))
    @assert leading_coefficient(polynomial(f)) == sum(l[i] * leading_coefficient(polynomial(G[I[i]])) for i in 1:length(I))
    for i in 1:length(I)
      g = g - l[i] * polynomial(G[I[i]]) * divexact(lmf, leading_monomial(G[I[i]]))
    end
    @assert leading_monomial(g) != lmf
    return true, pseudo_polynomial(g, coefficient_ideal(f))
  else
    return false, f
  end
end

function reduce(f::PseudoPoly{S, T}, G::Array{PseudoPoly{S, T}, 1}) where {S, T}

  while true
    if iszero(f)
      return f
    end

    b, g = can_reduce(f, G)

    if !b
      return f
    else
      f = g
    end
  end
end

function _contains(a::nf_elem, I)
  @assert a in sum(I)
  OK = maximal_order(parent(a))
  dena = denominator(a, OK)
  d = lcm(dena, lcm([denominator(id) for id in I]))
  v = matrix(FlintZZ, 1, degree(OK), elem_in_basis(OK(d * a)))
  @assert all(isone(denominator(basis_mat(d * id))) for id in I)
  M = vcat([numerator(basis_mat(d * id)) for id in I ])
  b, w = cansolve(M', v')
  @assert b
  res = nf_elem[]
  for i in 1:length(I)
    B = basis(I[i])
    push!(res, sum(w[(i - 1) * degree(OK) + k, 1] * B[k] for k in 1:degree(OK)))
  end
  @assert a == sum(res)
  return res
end

################################################################################
#
#  S-polynomial
#
################################################################################

function spoly(f::PseudoPoly, g::PseudoPoly)
  lmf = leading_monomial(f)
  lmg = leading_monomial(g)
  lcpolf = leading_coefficient(polynomial(f))
  lcpolg = leading_coefficient(polynomial(g))
  _gcd = gcd(lmf, lmg)
  return pseudo_polynomial(inv(lcpolf) * divexact(lmg, _gcd) * polynomial(f) - inv(lcpolg) * divexact(lmf, _gcd) * polynomial(g), lcm(leading_coefficient(f), leading_coefficient(g)))
end

################################################################################
#
#  Buchbergers Algorithm
#
################################################################################

function gb(G)
  GG = deepcopy(G)
  L = [ (GG[i], GG[j]) for i in 1:length(GG) for j in 1:(i - 1)]
  while !isempty(L)
    reverse!(L)
    (f, g) = pop!(L)
    reverse!(L)
    r = reduce(spoly(f, g), GG)
    if !iszero(r)
      for f in GG
        push!(L, (f, r))
      end
      push!(GG, r)
    end
  end
  return GG
end

################################################################################
#
#  Support
#
################################################################################

function lcm(a::NfOrdFracIdl, b::NfOrdFracIdl)
  da = denominator(a)
  db = denominator(b)
  d = lcm(da, db)
  newa = d * a
  newb = d * b
  simplify(newa)
  simplify(newb)
  c = lcm(numerator(newa), numerator(newb))
  return frac_ideal(order(a), c, d)
end


function divides(a::NfAbsOrdElem, b::NfAbsOrdElem)
  c = divexact(elem_in_nf(a), elem_in_nf(b))
  x, y = _check_elem_in_order(c, parent(a))
  if x
    return true, NfAbsOrdElem(parent(a), c, y)
  else
    return true, a
  end
end

function leading_monomial(f::Generic.MPoly)
  R = parent(f)
  l = length(f)
  if l == 0
    return f
  end
  A = f.exps
  r, c = size(A)
  e = A[1:r, 1:1]
  return R([one(base_ring(R))], e)
end

function leading_coefficient(f::Generic.MPoly)
  return f.coeffs[1]
end

