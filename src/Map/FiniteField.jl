function prime_field(K::NumField)
  return FlintRationalField()
end

function prime_field(F::FqNmodFiniteField; cached::Bool = true)
  return GF(Int(characteristic(F)), cached = cached)
end

function prime_field(F::FqFiniteField; cached::Bool = true)
  return GF(characteristic(F), cached = cached)
end

function prime_field(F::T; cached::Bool = true) where T <: Union{GaloisField, GaloisFmpzField}
  return F
end

function hom(F::FinField, K::FinField, a::FinFieldElem; check::Bool = true)
  @assert parent(a) == K

  if check
    @assert iszero(defining_polynomial(F)(a))
  end

  #We need a preimage function
  p = characteristic(K)
  Kp = prime_field(K, cached = false)
  Kpx = PolynomialRing(Kp, "x", cached = false)[1]
  Fp = prime_field(F, cached = false)
  Fpx = PolynomialRing(Fp, "x", cached = false)[1]
  M = zero_matrix(Kp, degree(F), degree(K))
  el = one(K)
  M[1, 1] = one(Kp)
  for i = 2:nrows(M)
    el = mul!(el, el, a)
    for j = 1:ncols(M)
      M[i, j] = coeff(el, j-1)
    end
  end

  aux = zero_matrix(Kp, 1, degree(F))
  aux1 = zero_matrix(Kp, 1, degree(K))
  function img(x::FinFieldElem)
    @assert parent(x) == F
    for i = 1:degree(F)
      aux[1, i] = Kp(coeff(x, i-1))
    end
    mul!(aux1, aux, M)
    pol = Kpx(elem_type(Kp)[aux1[1, j] for j = 1:degree(K)])
    return K(pol)
  end


  function preimg(x::FinFieldElem)
    @assert parent(x) == K
    for i = 1:degree(K)
      aux1[1, i] = Kp(coeff(x, i-1))
    end
    fl, y = can_solve_with_solution(M, aux1, side = :left)
    if !fl
      error("The element is not in the image!")
    end
    polF = Fpx(elem_type(Fp)[Fp(lift(y[1, j])) for j = 1:degree(F)])
    return F(polF)
  end

  return Nemo.FinFieldMorphism(F, K, img, preimg)
end

#Function that finds an embedding of k into K
function Nemo.embed_any(k::FinField, K::FinField)
  f = defining_polynomial(k)
  rt = roots(f, K)[1]
  return hom(k, K, rt)
end


function tr(a::FinFieldElem, mp::Nemo.FinFieldMorphism)
  @assert parent(a) == codomain(mp)
  q = order(domain(mp))
  d = divexact(degree(codomain(mp)), degree(domain(mp)))
  el = a
  aq = a
  for i = 1:d-1
    aq = aq^q
    el += aq
  end
  return mp\(el)
end

function norm(a::FinFieldElem, mp::Nemo.FinFieldMorphism)
  @assert parent(a) == codomain(mp)
  q = order(domain(mp))
  d = divexact(degree(codomain(mp)), degree(domain(mp)))
  el = a
  aq = a
  for i = 1:d-1
    aq = aq^q
    el *= aq
  end
  return mp\(el)
end

#TODO: compute via linear algebra.
function minpoly(a::FinFieldElem, mp::Nemo.FinFieldMorphism)
  conjs = Set{typeof(a)}()
  q = order(domain(mp))
  push!(conjs, a)
  el = a^q
  while !(el in conjs)
    push!(conjs, el)
    el = el^q
  end
  t = PolynomialRing(codomain(mp), "x", cached = false)[2]
  pol = prod(t-x for x in conjs)
  return map_coefficients(preimage_map(mp), pol)
end

function Nemo.generator_minimum_polynomial(mp::Nemo.FinFieldMorphism{FqFiniteField, FqFiniteField})
  return minpoly(gen(codomain(mp)), mp)
end

function Nemo.any_root(f::PolyElem{T}) where T <: FinFieldElem
  return roots(f)[1]
end
