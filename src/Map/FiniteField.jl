function hom(F::FinField, K::FinField, a::FinFieldElem; check::Bool = true)
  @assert parent(a) == K

  # I will be jumping through a lot of hoops to make
  # base_field(F) == F_p work
  if check
    if absolute_degree(base_field(F)) == 1 || base_field(F) !== base_field(K)
      @assert iszero(map_coefficients(x -> base_field(K)(lift(ZZ, x)), defining_polynomial(F), cached = false)(a))
    else
      @assert iszero(defining_polynomial(F)(a))
    end
  end

  if F isa FqField
    @assert K isa FqField
    @assert absolute_degree(F) == 1 || base_field(F) === base_field(K)
    k = base_field(F)
    kx = parent(defining_polynomial(F))

    img = function(x::FqFieldElem)
      @assert parent(x) === F
      return lift(kx, x)(a)
    end

    M = zero_matrix(k, degree(F), degree(K))
    M[1, 1] = one(k)
    el = one(K)
    for i = 2:nrows(M)
      el = mul!(el, el, a)
      for j = 1:ncols(M)
        M[i, j] = coeff(el, j-1)
      end
    end
    aux1 = zero_matrix(k, 1, degree(K))
    function preimg(x::FqFieldElem)
      @assert parent(x) == K
      for i = 1:degree(K)
        aux1[1, i] = coeff(x, i-1)
      end
      fl, y = can_solve_with_solution(M, aux1, side = :left)
      if !fl
        error("The element is not in the image!")
      end
      polF = kx([y[1, i] for i in 1:ncols(y)])
      return F(polF)
    end

    return Nemo.FinFieldMorphism(F, K, img, preimg)
  end

  #We need a preimage function
  p = characteristic(K)
  Kp = prime_field(K, cached = false)
  Kpx = polynomial_ring(Kp, "x", cached = false)[1]
  Fp = prime_field(F, cached = false)
  Fpx = polynomial_ring(Fp, "x", cached = false)[1]
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
  img = function(x::FinFieldElem)
    @assert parent(x) == F
    for i = 1:degree(F)
      aux[1, i] = Kp(coeff(x, i-1))
    end
    mul!(aux1, aux, M)
    pol = Kpx(elem_type(Kp)[aux1[1, j] for j = 1:degree(K)])
    return K(pol)
  end


  preimg = function(x::FinFieldElem)
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
  rt = roots(K, f)[1]
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
  t = polynomial_ring(codomain(mp), "x", cached = false)[2]
  pol = prod(t-x for x in conjs)
  return map_coefficients(preimage_map(mp), pol, cached = false)
end

function Nemo.generator_minimum_polynomial(mp::Nemo.FinFieldMorphism{FqPolyRepField, FqPolyRepField})
  return minpoly(gen(codomain(mp)), mp)
end

function Nemo.any_root(f::PolyRingElem{T}) where T <: FinFieldElem
  return roots(f)[1]
end
