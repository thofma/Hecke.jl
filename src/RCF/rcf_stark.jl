################################################################################
#
#  Small interface to characters
#
################################################################################

mutable struct RCFCharacter{S, T}
  C::ClassField{S, T}
  x::GrpAbFinGenElem
  mGhat::Map
  factored_conductor::Dict{NfOrdIdl, Int}
  conductor::NfOrdIdl
  conductor_inf_plc::Vector{InfPlc}
  mrcond::Union{MapClassGrp, MapRayClassGrp}
  mp_cond::GrpAbFinGenMap
  
  function RCFCharacter(C::ClassField{S, T}, x::GrpAbFinGenElem, mGhat::Map) where {S, T}
    z = new{S, T}()
    z.C = C
    z.x = x
    z.mGhat = mGhat
    return z
  end
end

function character(C::ClassField, x::GrpAbFinGenElem, mGhat::Map)
  return RCFCharacter(C, x, mGhat)
end

function _conjugate(chi::RCFCharacter)
  return character(chi.C, -chi.x, chi.mGhat)
end

function iszero(chi::RCFCharacter)
  return iszero(chi.x)
end

function conductor(chi::RCFCharacter)
  if isdefined(chi, :conductor)
    return chi.conductor
  end
  C = chi.C
  x = chi.x
  mGhat = chi.mGhat
  mp = mGhat(x) #The character as a map
  k, mk = kernel(mp)
  q, mq = cokernel(mk)
  C1 = ray_class_field(C.rayclassgroupmap, C.quotientmap*mq)
  chi.conductor, chi.conductor_inf_plc = conductor(C1)
  return chi.conductor
end

(chi::RCFCharacter)(I::NfOrdIdl, prec::Int) = image(chi, I, prec)
(chi::RCFCharacter)(I::GrpAbFinGenElem, prec::Int) = image(chi, I, prec)

function image(chi::RCFCharacter, I::NfOrdIdl, prec::Int)
  CC = AcbField(prec)
  x = chi.x
  mGhat = chi.mGhat
  mpc = mGhat(x)
  if iscoprime(I, conductor(chi.C)[1])
    C = chi.C
    mR = C.rayclassgroupmap
    mQ = C.quotientmap
    img = lift(mpc(mQ(mR\I)))
    return exppii(CC(2*img))
  end
  assure_with_conductor(chi)
  mR = chi.mrcond
  mp = chi.mp_cond
  mQ = chi.C.quotientmap
  el = mR\I
  el = mp\el
  el = mQ(el)
  el = mpc(el)
  img = lift(el)
  return exppii(CC(2*img))
end

function image(chi::RCFCharacter, x::GrpAbFinGenElem, prec::Int)
  CC = AcbField(prec)
  mp = chi.mGhat(chi.x)
  img = lift(mp(x))
  return exppii(CC(2*img))
end



function assure_with_conductor(chi::RCFCharacter)
  if isdefined(chi, :mrcond)
    return nothing
  end
  C = chi.C
  mR = C.rayclassgroupmap
  c = conductor(chi)
  r, mr = ray_class_group(c, chi.conductor_inf_plc, n_quo = degree(C))
  lp, sR = find_gens(mR)
  imgs = GrpAbFinGenElem[mr\x for x in lp]
  mpR = hom(sR, imgs)
  chi.mrcond = mr
  chi.mp_cond = mpR
  return nothing
end

################################################################################
#
#  RCF using Stark units
#
################################################################################

function rcf_using_stark_units(C::T; cached::Bool = true) where T <: ClassField_pp
  K = base_field(C)
  @assert istotally_real(K)
  c, inf_plc = conductor(C)
  @assert isempty(inf_plc)
  C1, mp = _find_suitable_quadratic_extension(C)
  @show conductor(C1)
  kmp, mkmp = kernel(mp)
  comp = mkmp*C1.quotientmap
  imgc, mimgc = image(comp)
  @assert order(imgc) == 2
  y = mimgc(imgc[1])
  Ghat, mGhat = dual(codomain(C1.quotientmap))
  p = 100
  #I don't need the character with value 1 on the generator of the
  #quadratic extension
  chars = [character(C1, x, mGhat) for x in Ghat if !iszero(lift(mGhat(x)(y)))]
  @assert length(chars) == degree(C)
  while true
    approximations_derivative_Artin_L_functions = approximate_derivative_Artin_L_function(chars, p)
    @show el = approximate_artin_zeta_derivative_at_0(C1, approximations_derivative_Artin_L_functions)
    error("stop")
    f = find_defining_polynomial(K, el, real_places(K)[1])
    if degree(f) != degree(C)
      p *= 2 
      continue
    end
    mR = C.rayclassgroupmap
    mQ = C.quotientmap
    ng, mng = norm_group(f, mR, cached = false, check = false)
    if iszero(mng*mQ)
      C.A = number_field(f, cached = false, check = false)[1]
      return nothing
    end
    p *= 2
  end
end

function find_defining_polynomial(K::AnticNumberField, el::Vector{acb}, v::InfPlc)
  OK = maximal_order(K)
  Kt, t = PolynomialRing(K, "t", cached = false)
  prec = precision(parent(el[1]))
  R = ArbField(prec, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  v = arb_poly[x-(real(exp(2*a)-exp(-2*a))) for a in el]
  f = my_prod(v)
  n = degree(f)
  coeffs = arb[coeff(f, i) for i = 0:n-1]
  for x in coeffs 
    if !radiuslttwopower(x, 8)
      return Kt()
    end
  end
  final_coeffs = Vector{nf_elem}(undef, n)
  #TODO: Choose a proper bound!
  bound = 1
  for i = 0:n-1
    bound_other_embs = 2^(n-i)*binomial(n, i)
    bound_v = upper_bound(coeffs[i+1], fmpz)
    bound = max((n-1)*bound_other_embs^2+bound_v, bound)
  end
 
  #Now, I have a polynomial over the reals. I use lattice enumeration to recover the 
  #coefficients as elements of K
  gram_mat = trace_matrix(OK) #The field is totally real :)
  @assert isposdef(gram_mat)
  elts = __enumerate_gram(gram_mat, Int(bound))
  for x in elts
    x = OK(x[1])
    r = real(evaluate(x, v))
    for j = 1:length(final_coeffs)
      if overlaps(r, coeffs[i])
        if isassigned(final_coeffs, i)
          return K(t)
        end
        final_coeffs[i] = r
      end
    end
  end
  push!(final_coeffs, K(1))
  return Kt(final_coeffs)
end


function _find_suitable_quadratic_extension(C::T) where T <: ClassField_pp
  c = factored_modulus(C)
  K = base_field(C)
  mR = C.rayclassgroupmap
  mQ = C.quotientmap
  R = codomain(mQ)
  OK = maximal_order(K)
  real_plc = real_places(K)
  @assert length(real_plc) == degree(K)
  v = real_plc[1]
  w = real_plc[2:end]
  inf_plc_ram = Set(w)
  bound = fmpz(100)
  ctx = rayclassgrp_ctx(OK, Int(exponent(C))*2)
  lc = _squarefree_ideals_with_bounded_norm(OK, bound, coprime = minimum(defining_modulus(C)[1], copy = false))
  cnt = 0 
  while true
    @vprint :ClassField 1 "Batch of ideals with $(length(lc)) elements \n"
    for I in lc
      newc = merge(max, c, I[1])
      r, mr = ray_class_group_quo(OK, newc, w, ctx)
      gens, group_gens = find_gens(mr)
      images = GrpAbFinGenElem[mQ(mR\J) for J in gens]
      mp = hom(group_gens, images, check = false)
      k, mk = kernel(mp)
      ls = subgroups(k, quotype = Int[2], fun = (x, y) -> sub(x, y, false)[2])
      for ms in ls
        ms::GrpAbFinGenMap
        q, mq = cokernel(ms*mk, false)
        Cnew = ray_class_field(mr, mq)
        cnew, inf_plcc = conductor(Cnew)
        if Set(inf_plcc) != inf_plc_ram
          continue
        end
        acceptable = true
        for (P, v) in c
          pdt1 = prime_decomposition_type(C, P)
          pdt2 = prime_decomposition_type(Cnew, P)
          if pdt1[3] != pdt2[3]
            acceptable = false
            break
          end
        end
        if acceptable
          return Cnew, mp
        end
      end
    end
    #Need to consider more moduli.
    bound *= 2
    lc1 = _squarefree_ideals_with_bounded_norm(OK, bound, coprime = minimum(defining_modulus(C)[1], copy = false))
    lc = setdiff(lc, lc1)
  end
end

function approximate_artin_zeta_derivative_at_0(C::ClassField, D::Dict{S, T}) where {S, T}
  Dzeta = Vector{acb}()
  ks = keys(D)
  CC = parent(first(values(D)))
  for x in codomain(C.quotientmap)
    v = zero(CC)
    for k in ks
      v += D[k]*_conjugate(k)(x, CC.prec)
    end
    push!(Dzeta, v//(degree(C)))
  end
  return Dzeta
end

function approximate_derivative_Artin_L_function(chars::Vector, prec::Int) 
  D = Dict{typeof(chars[1]), acb}()
  RR = ArbField(prec)
  nterms = 10
  K = base_field(chars[1].C)
  n = degree(K)
  @show Acoeffs = Vector{arb}[_compute_A_coeffs(n, i, prec) for i = 0:nterms]
  coeffs_0 = Vector{arb}[_Aij_at_0(i, n, Acoeffs[i+1]) for i = 0:nterms]
  coeffs_1 = Vector{arb}[_Aij_at_1(i, n, Acoeffs[i+1]) for i = 0:nterms]
  den = 2*const_pi(RR)^(RR(n-1)/2)
  for x in chars
    A = _A_function(x, prec)
    cx = _conjugate(x)
    @show lambda = _lambda(cx, prec, nterms, coeffs_0, coeffs_1)
    W = artin_root_number(cx, prec)
    num = A*lambda
    den1 = den*W
    D[x] = num/den1
  end
  return D
end

function _A_function(chi::RCFCharacter, prec::Int)
  R = AcbField(prec)
  if iszero(chi)
    #We have the trivial character sending everything to 1.
    #we return 0
    return zero(R)
  end
  C = chi.C
  cC = conductor(C)[1]
  cchi = conductor(chi)
  if cchi == cC
    return one(R)
  end
  fcC = factor(cC)
  fcchi = factor(cchi)
  res = one(R)
  for (p, v) in fcC
    if haskey(fcchi.fac, p)
      continue
    end
    res *= (1 - chi(p, prec))
  end
  return res
end

function artin_root_number(chi::RCFCharacter, prec::Int)
  R = AcbField(prec)
  C = chi.C
  c = conductor(chi)
  OK = base_ring(C)
  D = different(OK)
  J = D*c
  lfJ = factor(J)
  lambda = OK(approximate(collect(values(lfJ)), collect(keys(lfJ))))
  lambda = make_positive(lambda, minimum(J)^2)
  g = numerator(simplify(ideal(OK, lambda) * inv(J)))
  u = idempotents(g, c)[1]
  u = make_positive(u, minimum(c^2))
  h = numerator(ideal(OK, u) * inv(g))
  Qc, mQc = quo(OK, c)
  G, mG = multiplicative_group(Qc)
  reps = NfOrdElem[make_positive(lift(mG(x)), minimum(c)^2) for x in G]
  Gsum = R(0)
  for i = 1:length(reps)
    Gsum += chi(ideal(OK, reps[i]), prec) * exppii(2*R(tr((reps[i]*u).elem_in_nf//lambda.elem_in_nf)))
  end
  Gsum *= chi(h, prec)
  res = (-onei(R))^length(chi.conductor_inf_plc)*Gsum/sqrt(R(norm(c)))
  return res
end


function _lambda(chi::RCFCharacter, prec::Int, nterms::Int, coeffs_0, coeffs_1)
  K = base_field(chi.C)
  coeffs_chi = first_n_coefficients_L_function(chi, nterms, prec)
  Wchi = artin_root_number(chi, prec)
  CC = AcbField(prec)
  res1 = zero(CC)
  res2 = zero(CC)
  cchi = _C(chi, prec)
  n = degree(K)
  for i = 1:nterms
    evpoint = cchi/i
    ev0, ev1 = _evaluate_f_x_0_1(evpoint, n, prec, nterms, coeffs_0, coeffs_1)
    res1 += coeffs_chi[i]*ev1
    res2 += conj(coeffs_chi[i])*ev0
  end
  return res1 + Wchi*res2
end

function _C(chi::RCFCharacter, prec::Int)
  RR = ArbField(prec)
  c = conductor(chi)
  OK = order(c)
  nc = norm(c)
  p = const_pi(RR)
  d = abs(discriminant(OK))
  return sqrt(RR(d*nc)/(p^degree(OK)))
end

#C is the class field
#x is the character, mGhat interprets it
#prec is the precision
function first_n_coefficients_L_function(chi::RCFCharacter, n::Int, prec::Int)
  C = chi.C
  OK = base_ring(C)
  lp = prime_ideals_up_to(OK, n)
  sort!(lp, by = x -> norm(x, copy = false))
  CC = AcbField(prec)
  coeffs = Dict{Tuple{Int, Int}, acb}()
  coeffs[(1, 0)] = one(CC)
  for i = 2:n
    coeffs[(i, 0)] = zero(CC)
  end
  for h = 1:length(lp)
    P = lp[h]
    np = norm(P, copy = false)
    for i = 1:n
      v = valuation(i, np)
      if iszero(v)
        coeffs[(i, h)] = coeffs[(i, h-1)]
        continue
      end
      r = chi(P, prec)
      res = zero(CC)
      for k = 0:v
        kk = (Int(divexact(i, np^k)), h-1)
        res += coeffs[kk]*r^k
      end
      coeffs[(i, h)] = res
    end
  end
  coeffs_res = Vector{acb}(undef, n)
  for i = 1:n
    coeffs_res[i] = coeffs[(i, length(lp))]
  end
  return coeffs_res
end

function _evaluate_f_x_0_1(x::arb, n::Int, prec::Int, nterms::Int, coeffs_0::Vector{Vector{arb}}, coeffs_1::Vector{Vector{arb}})
  RR = ArbField(prec)
  res0 = zero(RR)
  res1 = zero(RR)
  factorials = Vector{fmpz}(undef, n+1)
  factorials[1] = fmpz(1)
  for i = 2:n+1
    factorials[i] = factorials[i-1]*(i-1)
  end
  lnx = log(x)
  powslogx = powers(lnx, n)

  #Case i = 0 by hand.

  aij1 = coeffs_1[1]
  for j = 1:n
    res1 += (aij1[j]*powslogx[j])/factorials[j]
  end
  res1 += x*gamma(fmpq(1, 2), RR)*gamma(fmpz(1), RR)^(n-1)
  
  aij0 = coeffs_0[1]
  for j = 1:n+1
    res0 += (aij0[j]*powslogx[j])/factorials[j]
  end

  for i = 1:nterms
    aij1 = coeffs_1[i+1]
    auxres1 = zero(RR)
    for j = 1:n
      auxres1 += (aij1[j]*powslogx[j])/factorials[j]
    end
    res1 += x^(-i)*auxres1
    
    aij0 = coeffs_0[i+1]
    auxres0 = zero(RR)
    for j = 1:n
      auxres0 += (aij0[j]*powslogx[j])/factorials[j]
    end
    res0 += x^(-i)*auxres0
  end

  return res0, res1

end

function _Aij_at_0(i::Int, n::Int, aij::Vector{arb})
  #aij starts with ai0 and finishes with ain
  CC = parent(aij[1])
  @show aij
  if iszero(i)
    #=
    ev = CC(0.001)
    val1 = (gamma(ev/2)*gamma((ev+1)/2)^(n-1))/ev
    val2 = sum(aij[j+1]/(ev^j) for j = 0:1)
    @show val1, val2
    =#
    return aij
  end
  D = Vector{arb}(undef, n+1)
  D[n+1] = zero(CC)
  for j = n:-1:1
    D[j] = (D[j+1] - aij[j+1])/i
  end
  @show iseven(i)
  @show D
  return D
end

function _Aij_at_1(i::Int, n::Int, aij::Vector{arb})
  #aij starts with ai0 and finishes with ain
  @assert length(aij) == n+1
  CC = parent(aij[1])
  if iszero(i)
    return aij[1:n]
  end
  
  D = Vector{arb}(undef, n+1)
  D[n+1] = zero(CC)
  for j = n:-1:1
    D[j] = (D[j+1] - aij[j+1])/(i+1)
  end
  return D[1:n]
end

function _compute_A_coeffs(n::Int, i::Int, prec::Int)
  RR = ArbField(prec)
  res = Vector{arb}(undef, n+1)
  #res[j] contains A_{i,(j-1)}
  if iseven(i)
    q = divexact(i, 2)
    r = _coeff_0_even(n, q, RR)
    res[2] = r
    for j = 3:n+1
      res[j] = zero(RR)
    end
    r1 = _coeff_exp_1_even(n, q, RR)
    res[1] = r*r1
  else
    q = divexact(i-1, 2)
    r0 = _coeff_0_odd(n, q, RR)
    vg = _coeff_exp_odd(n, q, RR) 
    res[n+1] = zero(RR)
    for j = 1:n
      res[j] = vg[n-j+1]*r0  
    end
  end
  ev = RR(-i)+RR(0.0001)
  val1 = gamma(ev/2)*gamma((ev+1)/2)^(n-1)
  val2 = sum(res[j+1]/((ev+i)^j) for j = 0:n)
  @show i
  @show val1
  @show val2
  return res
end

function _coeff_0_odd(n::Int, q::Int, RR::ArbField)
  exc_num = (-1)^(q*n+1)*fmpz(2)^(n+2*q)
  exc_den = (2*q+1)*factorial(fmpz(2*q))*factorial(fmpz(q))^(n-2)
  return sqrt(const_pi(RR))*fmpq(exc_num, exc_den)
end

function _coeff_exp_odd(n::Int, q::Int, RR::ArbField)
  res = Vector{arb}(undef, n-1)
  res[1] = _sum_pow_inv_odd(q, 1) + (n-1)*_sum_pow_inv_even(q, 1) - log(RR(2)) - fmpq(n, 2)*const_euler(RR)
  for k = 2:n-1
    res[k] = (-1)^k*zeta(k, RR)*(1+fmpq(n-2, fmpz(2)^k)) + _sum_pow_inv_odd(q, k) + (n-1)*_sum_pow_inv_even(q, k)
    res[k] = res[k]/k
  end
  RRx = PowerSeriesRing(RR, n, "x")[1]
  g = RRx(res, length(res), n, 1)
  gexp = exp(g)
  return arb[coeff(gexp, i) for i = 0:n-1]
end


function _coeff_exp_1_even(n::Int, q::Int, RR::ArbField)
  exc = (n-1)*_sum_pow_inv_odd(q-1, 1) + _sum_pow_inv_even(q, 1)
  inexc = fmpq(n, 2)*const_euler(RR)+(n-1)*log(RR(2))
  return exc - inexc
end

function _coeff_0_even(n::Int, q::Int, RR::ArbField)
  num = 2 * fmpz(4)^(q*(n-1))*factorial(fmpz(q))^(n-2)
  den = factorial(fmpz(2*q))^(n-1)
  r = fmpq(num, den)
  return (-1)^(q*n)*r*const_pi(RR)^(n-1)
end


function _sum_pow_inv_odd(n::Int, k::Int)
  res = fmpq(0)
  for i = 0:n
    res += fmpq(1, (2*i+1)^k)
  end
  return res
end 

function _sum_pow_inv_even(n::Int, k::Int)
  res = fmpq(0)
  for i = 1:n
    res += fmpq(1, (2*i)^k)
  end
  return res
end