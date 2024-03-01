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

function can_reduce(f::PseudoPoly{S, T}, G::Vector{PseudoPoly{S, T}}) where {S, T}
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
    l = AbsSimpleNumFieldElem[ l[i]//leading_coefficient(polynomial(G[I[i]])) for i in 1:length(I)]
    g = deepcopy(polynomial(f))
    @assert leading_coefficient(polynomial(f)) == sum(l[i] * leading_coefficient(polynomial(G[I[i]])) for i in 1:length(I))
    for i in 1:length(I)
      g = g - l[i] * polynomial(G[I[i]]) * divexact(lmf, leading_monomial(G[I[i]]))
    end
    @assert leading_monomial(g) != lmf
    @show leading_monomial(g)
    return true, pseudo_polynomial(g, coefficient_ideal(f))
  else
    return false, f
  end
end

function reduce(f::PseudoPoly{S, T}, G::Vector{PseudoPoly{S, T}}) where {S, T}

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

function _contains(a::AbsSimpleNumFieldElem, I)
  @assert a in sum(I)
  OK = maximal_order(parent(a))
  dena = denominator(a, OK)
  d = lcm(dena, lcm([denominator(id) for id in I]))
  v = matrix(FlintZZ, 1, degree(OK), coordinates(OK(d * a)))
  @assert all(isone(denominator(basis_matrix(d * id))) for id in I)
  M = reduce(vcat, [numerator(basis_matrix(d * id)) for id in I ])
  w = solve(M', v', side = :right)
  res = AbsSimpleNumFieldElem[]
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
  return pseudo_polynomial(inv(lcpolf) * divexact(lmg, _gcd) * polynomial(f) - inv(lcpolg) * divexact(lmf, _gcd) * polynomial(g), (lcm(leading_coefficient(f), leading_coefficient(g))))
end

################################################################################
#
#  Buchbergers Algorithm
#
################################################################################

function _den(f)
  return lcm([denominator(coeff(f, i)) for i in 1:length(f)])
end

function _simplify(pp)
  f = polynomial(pp)
  den = _den(f)
  g = f * den
  I = coefficient_ideal(pp) * inv(base_ring(f)(den))
  I = simplify(I)
  return pseudo_polynomial(g, I)
end

function gb_naive(G::Vector{S}) where {S}
  GG::Vector{S} = deepcopy(G)
  #reverse!(GG)
  L = Tuple{S, S}[ (GG[i], GG[j]) for i in 1:length(GG) for j in 1:(i - 1)]
  while !isempty(L)
    @show length(L)
    sort!(L, by = x -> total_degree(polynomial(x[1])) + total_degree(polynomial(x[2])))
    reverse!(L)
    (f, g) = pop!(L)
    sp = spoly(f, g)
    r = reduce(sp, GG)
    if !iszero(r)
      r = _simplify(r)
      if total_degree(polynomial(r)) == 0
        @show norm(coefficient_ideal(r)) * norm(coeff(polynomial(r), 1))
      else
        @show polynomial(r)
      end
      for f in GG
        push!(L, (f, r))
      end
      push!(GG, r)
    end
  end
  return GG
end

function gb(G::Vector{S}, mmod) where {S}
  GG::Vector{S} = deepcopy(G)
  reverse!(GG)
  push!(GG, pseudo_polynomial(one(parent(G[1].poly)), mmod))
  L = Tuple{S, S}[ (GG[i], GG[j]) for i in 1:length(GG) for j in 1:(i - 1)]
  while !isempty(L)
    #@show length([x for x in GG if is_constant(polynomial(x))])
    #@show [ norm(coefficient_ideal(x)) for x in GG]
    #@show [ norm(coefficient_ideal(_simplify(x))) for x in GG]
    #@show [ (_den(polynomial(x))) for x in GG]
    #@show [ (_den(polynomial(_simplify(x)))) for x in GG]
    #@show length(GG)
    #@show length(L)
    (f, g) = pop!(L)

    lmf = leading_monomial(f)
    lmg = leading_monomial(g)
    lcf = leading_coefficient(f)
    lcg = leading_coefficient(g)
    if isone(gcd(lmf, lmg)) && isone(lcf + lcg)
      println("Skipping ...")
      continue
    end

    sp = spoly(f, g)
    r = sp

    A = coefficient_ideal(r)
    C, b = reduce_ideal(A)
    rp = r.poly
    r = pseudo_polynomial(b * rp, fractional_ideal(order(C), C))
    Nfinv = mmod * inv(C)::AbsSimpleNumFieldOrderFractionalIdeal
    newcoeffs = AbsSimpleNumFieldElem[]
    indices = Int[]
    for i in 1:length(r.poly.coeffs)
      c = r.poly.coeffs[i]
      cc = c - mod(c, Nfinv)
      if !iszero(cc)
        push!(newcoeffs, c - mod(c, Nfinv))
        push!(indices, i)
      end
    end

    newexps = Matrix{UInt}(undef, size(r.poly.exps, 1), length(indices))
    for j in 1:length(indices)
      for k in 1:size(r.poly.exps, 1)
        newexps[k, j] = r.poly.exps[k, indices[j]]
      end
    end

    r = pseudo_polynomial(parent(r.poly)(newcoeffs, newexps), coefficient_ideal(r))

    r = reduce(r, GG)


    if iszero(polynomial(r))
      continue
    end

    println("first r")
    @show r

    A = coefficient_ideal(r)
    C, b = reduce_ideal(A)
    rp = r.poly
    r = pseudo_polynomial(b * rp, fractional_ideal(order(C), C))
    Nfinv = mmod * inv(C)::AbsSimpleNumFieldOrderFractionalIdeal
    newcoeffs = AbsSimpleNumFieldElem[]
    indices = Int[]
    for i in 1:length(r.poly.coeffs)
      c = r.poly.coeffs[i]
      cc = c - mod(c, Nfinv)
      if !iszero(cc)
        push!(newcoeffs, c - mod(c, Nfinv))
        push!(indices, i)
      end
    end

    newexps = Matrix{UInt}(undef, size(r.poly.exps, 1), length(indices))
    for j in 1:length(indices)
      for k in 1:size(r.poly.exps, 1)
        newexps[k, j] = r.poly.exps[k, indices[j]]
      end
    end

    r = pseudo_polynomial(parent(r.poly)(newcoeffs, newexps), coefficient_ideal(r))

    r = reduce(r, GG)

    @show r

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

function lcm(a::AbsSimpleNumFieldOrderFractionalIdeal, b::AbsSimpleNumFieldOrderFractionalIdeal)
  a = simplify(a)
  b = simplify(b)
  da = denominator(a)
  db = denominator(b)
  d = lcm(da, db)
  newa = d * a
  newb = d * b
  simplify(newa)
  simplify(newb)
  c = lcm(numerator(newa), numerator(newb))
  return simplify(fractional_ideal(order(a), c, d))
end


function divides(a::AbsNumFieldOrderElem, b::AbsNumFieldOrderElem)
  c = divexact(elem_in_nf(a), elem_in_nf(b))
  x, y = _check_elem_in_order(c, parent(a))
  if x
    return true, AbsNumFieldOrderElem(parent(a), c, y)
  else
    return false, a
  end
end



