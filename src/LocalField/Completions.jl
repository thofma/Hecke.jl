################################################################################
#
#  Functions for completion map
#
################################################################################

function image(f::CompletionMap, a::nf_elem)
  Qx = parent(parent(a).pol)
  return evaluate(Qx(a), f.prim_img)
end

function preimage(f::CompletionMap{LocalField{qadic, EisensteinLocalField}, LocalFieldElem{qadic, EisensteinLocalField}}, a::LocalFieldElem{qadic, EisensteinLocalField})
  Kp = codomain(f)
  @assert Kp === parent(a)
  Qq = base_field(Kp)
  Qpx = parent(defining_polynomial(Qq))
  coeffs = Vector{nf_elem}()
  for i = 0:degree(a.data)
    as_pol = Qpx(coeff(a.data, i))
    as_fmpq_poly = map_coefficients(lift, as_pol)
    push!(coeffs, evaluate(as_fmpq_poly, f.inv_img[1]))
  end
  K = domain(f)
  Kx = PolynomialRing(K, "x")[1]
  r = Kx(coeffs)
  return evaluate(r, f.inv_img[2])
end

function preimage(f::CompletionMap{LocalField{padic, EisensteinLocalField}, LocalFieldElem{padic, EisensteinLocalField}}, a::LocalFieldElem{padic, EisensteinLocalField})
  @assert codomain(f) === parent(a)
  return evaluate(map_coefficients(lift, a.data), f.inv_img[2])
end

function preimage(f::CompletionMap{FlintQadicField, qadic}, a::qadic)
  Kp = codomain(f)
  @assert Kp == parent(a)
  Qpx = parent(defining_polynomial(Kp))
  as_pol = Qpx(a)
  as_fmpq_poly = map_coefficients(lift, as_pol)
  return evaluate(as_fmpq_poly, f.inv_img[1])
end


function _lift(a::nf_elem, f::fmpz_poly, prec::Int)
  n = clog(prec, 2)
  for i = 2:n
    a = a - f(a)//f'(a)
  end
  return a
end


function completion(K::AnticNumberField, P::NfOrdIdl, precision::Int = 64)
  OK = order(P)
  @assert isprime(P)
  @assert nf(OK) == K
  f = degree(P)
  e = ramification_index(P)
  Qp = PadicField(minimum(P), precision)
  Qq, gQq = QadicField(minimum(P), f, precision)
  Qqx, gQqx = PolynomialRing(Qq, "x")
  q, mq = ResidueField(Qq)
  F, mF = ResidueFieldSmall(OK, P)
  mp = find_morphism(q, F)
  g = gen(q)
  gq_in_K = (mF\(mp(g))).elem_in_nf
  Zx = PolynomialRing(FlintZZ, "x")[1]
  pol_gq = lift(Zx, defining_polynomial(q))
  gq_in_K = _lift(gq_in_K, pol_gq, precision)
  u = uniformizer(P)
  pows_gq = powers(gq_in_K, f)
  els = Vector{nf_elem}()
  el = one(K)
  #TODO: multiply elements up to a certain precision instead of exactly
  for i = 1:e
    for j = 1:f
      push!(els, el*pows_gq[j])
    end
    mul!(el, el, u.elem_in_nf) 
  end
  MK = basis_matrix(els)
  bK = basis_matrix(nf_elem[u.elem_in_nf^e, gen(K)])
  MQp = map_entries(Qp, MK)
  bQp = map_entries(Qp, bK)
  fl, xQp = can_solve_with_solution(MQp, bQp, side = :left)
  @assert fl
  coeffs_eisenstein = Vector{qadic}(undef, e+1)
  for i = 1:e
    coeff = Qq()
    for j = 0:f-1
      coeff -= (gQq^j)*xQp[1, j+1+(i-1)*f]
    end
    coeffs_eisenstein[i] = coeff
  end
  coeffs_eisenstein[e+1] = one(Qq)
  pol_gen = Qqx(coeffs_eisenstein)
  Kp, gKp = local_field(pol_gen, "a", EisensteinLocalField)
  img_prim_elem = Vector{qadic}(undef, e)
  for i = 1:e
    coeff = Qq()
    for j = 0:f-1
      coeff += (gQq^j)*xQp[2, j+1+(i-1)*f]
    end
    img_prim_elem[i] = coeff
  end
  img = Kp(Qqx(img_prim_elem))
  return Kp, CompletionMap(K, Kp, img, (gq_in_K, u.elem_in_nf), precision)
end

function totally_ramified_completion(K::AnticNumberField, P::NfOrdIdl, precision::Int = 64)
  OK = order(P)
  @assert isprime(P)
  @assert nf(OK) == K
  @assert isone(degree(P)) 
  e = ramification_index(P)
  Qp = PadicField(minimum(P), precision)
  Qpx = PolynomialRing(Qp, "x")[1]
  u = uniformizer(P).elem_in_nf
  pows_u = powers(u, e-1)
  MK = basis_matrix(pows_u)
  bK = basis_matrix(nf_elem[u*pows_u[end], gen(K)])
  MQp = map_entries(Qp, MK)
  bQp = map_entries(Qp, bK)
  fl, xQp = can_solve_with_solution(MQp, bQp, side = :left)
  @assert fl
  coeffs_eisenstein = Vector{padic}(undef, e+1)
  for i = 1:e
    coeffs_eisenstein[i] = -xQp[1, i]
  end
  coeffs_eisenstein[e+1] = one(Qp)
  pol_gen = Qpx(coeffs_eisenstein)
  Kp, gKp = local_field(pol_gen, "a", EisensteinLocalField)
  img_prim_elem = Vector{padic}(undef, e)
  for i = 1:e
    img_prim_elem[i] = xQp[2, i]
  end
  img = Kp(Qpx(img_prim_elem))
  return Kp, CompletionMap(K, Kp, img, u, precision)
end
