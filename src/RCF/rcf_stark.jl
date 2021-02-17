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

function Base.show(io::IO, C::RCFCharacter) 
  println(IOContext(io, :compact => true), "Character of $(C.C)")
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

function ==(x::RCFCharacter, y::RCFCharacter)
  if x.C === y.C
    return x.x == y.x
  end
  error("Not yet implemented!")
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
  q, mq = cokernel(mk, false)
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
  if iscoprime(I, defining_modulus(chi.C)[1])
    C = chi.C
    mR = C.rayclassgroupmap
    mQ = C.quotientmap
    img = lift(mpc(mQ(mR\I)))
    if iszero(img)
      return one(CC)
    end
    return exppii(2*CC(img))
  end
  assure_with_conductor(chi)
  if !iscoprime(I, conductor(chi))
    return zero(CC)
  end
  mR = chi.mrcond
  mp = chi.mp_cond
  mQ = chi.C.quotientmap
  el = mR\I
  el = mp\el
  el = mQ(el)
  el = mpc(el)
  img = lift(el)
  if iszero(img)
    return one(CC)
  end
  return exppii(2*CC(img))
end

function image(chi::RCFCharacter, x::GrpAbFinGenElem, prec::Int)
  CC = AcbField(prec)
  mp = chi.mGhat(chi.x)
  img = lift(mp(x))
  if iszero(img)
    return one(CC)
  end
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
  @hassert :ClassField 1 istotally_real(K)
  c, inf_plc = conductor(C)
  @hassert :ClassField 1 isempty(inf_plc)
  C1, mp, v = _find_suitable_quadratic_extension(C)
  @show conductor(C1)
  kmp, mkmp = kernel(mp)
  comp = mkmp*C1.quotientmap
  imgc, mimgc = image(comp)
  @hassert :ClassField 1 order(imgc) == 2
  simgs, msimgs = snf(imgc)
  y = mimgc(msimgs(simgs[1]))
  Ghat, mGhat = dual(codomain(C1.quotientmap))
  p = 64
  #I don't need the character with value 1 on the generator of the
  #quadratic extension
  chars = RCFCharacter{MapRayClassGrp, GrpAbFinGenMap}[character(C1, x, mGhat) for x in Ghat if !iszero(lift(mGhat(x)(y)))]
  @hassert :ClassField 1 length(chars) == degree(C)
  #First, we get an approximation of the defpoly at v
  fl = false
  nb = 1
  while !fl
    approximations_derivative_Artin_L_functions = approximate_derivative_Artin_L_function(chars, p)
    el = approximate_artin_zeta_derivative_at_0(C1, mp, approximations_derivative_Artin_L_functions)
    fl, nb = approximate_defpoly(K, el)
    if !fl
      p *= 2
      @vprint :ClassField 1 "Guess not useful. Increasing precision to $(2*p) \n"
    end
  end
  p = 3*nb
  @vprint :ClassField 1 "Guess: we need precision $(p) \n"
  while true
    approximations_derivative_Artin_L_functions = approximate_derivative_Artin_L_function(chars, p)
    el = approximate_artin_zeta_derivative_at_0(C1, mp, approximations_derivative_Artin_L_functions)
    f = find_defining_polynomial(K, el, v)
    if degree(f) != degree(C)
      p *= 2
      @vprint :ClassField 1 "Wrong guess, setting precision to $(p) \n"
      continue
    end
    mR = C.rayclassgroupmap
    mQ = C.quotientmap
    ng, mng = norm_group(f, mR, false, cached = false, check = false, of_closure = false)
    if iszero(mng*mQ)
      C.A = number_field(f, cached = false, check = false)[1]
      return nothing
    end
    p *= 2
  end
end

function power_sums(v::Vector{T}) where T <: FieldElem
  res = Vector{T}(undef, length(v))
  pows = T[x for x in v]
  res[1] = sum(pows)
  for i = 2:length(v)
    for j = 1:length(pows)
      pows[j] *= v[j]
    end
    res[i] = sum(pows)
  end
  return res
end

function approximate_defpoly(K::AnticNumberField, el::Vector{acb})
  rts = arb[real(exp(2*x)+exp(-2*x)) for x in el]
  ps = power_sums(rts)
  pol = power_sums_to_polynomial(ps)
  @vprint :ClassField 1 "Approximation: $pol \n"
  l2norm = fmpz(0)
  for i = 0:degree(pol)
    c = coeff(pol, i)
    if radiuslttwopower(c, 0)
      l2norm += upper_bound(abs(c)^2, fmpz)
    else
      return false, 0
    end
  end
  return true, nbits(l2norm)
end

function find_defining_polynomial(K::AnticNumberField, el::Vector{acb}, v::InfPlc)
  OK = maximal_order(K)
  Kt = PolynomialRing(K, "t", cached = false)[1]
  rts = arb[real(exp(2*x)+exp(-2*x)) for x in el]
  ps = power_sums(rts)
  pol = power_sums_to_polynomial(ps)
  B = basis(OK, K)
  bconjs = [real(evaluate(x, v, 2*precision(parent(pol)))) for x in B]
  coeffs = Vector{nf_elem}(undef, length(el)+1)
  for i = 1:degree(pol)
    c = coeff(pol, i-1)
    vs = arb[c]
    append!(vs, bconjs)
    bn = 3*nbits(Hecke.upper_bound(c, fmpz))
    fl, comb = _lindep(vs, bn)
    if !fl || abs(comb[1]) != 1
      return Kt()
    end
    if !isone(comb[1])
      comb = map(x -> -x, comb)
    end
    coeffs[i] = -dot(comb[2:degree(K)+1], B)
  end
  coeffs[end] = one(K)
  return Kt(coeffs)
end

function _lindep(A::Array{arb, 1}, bits::Int)
  n = length(A)
  V = [floor(ldexp(s, bits) + 0.5) for s in A]
  M = zero_matrix(ZZ, n, n + 1)
  for i = 1:n
    M[i, i] = 1
    flag, M[i, n + 1] = unique_integer(V[i])
    !flag && return false, fmpz[M[1, 1]]
  end
  lll!(M, lll_ctx(0.99999, 0.5001))
  res = fmpz[M[1, i] for i = 1:n]
  return true, res
end




function _find_suitable_quadratic_extension(C::T) where T <: ClassField_pp
  c = factored_modulus(C)
  K = base_field(C)
  mR = C.rayclassgroupmap
  mQ = C.quotientmap
  R = codomain(mQ)
  OK = maximal_order(K)
  real_plc = real_places(K)
  @hassert :ClassField 1 length(real_plc) == degree(K)
  v = real_plc[end]
  w = real_plc[1:end-1]
  inf_plc_ram = Set(w)
  bound = fmpz(100)
  ctx = rayclassgrp_ctx(OK, Int(exponent(C))*2)
  allow_cache!(ctx.class_group_map)
  lc = _squarefree_ideals_with_bounded_norm(OK, bound, coprime = minimum(defining_modulus(C)[1], copy = false))
  cnt = 0 
  while true
    @vprint :ClassField 1 "Batch of ideals with $(length(lc)) elements \n"
    for I in lc
      for i = 1:length(real_plc)
        v = real_plc[i]
        w = [real_plc[j] for j = 1:length(real_plc) if j != i]
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
          if length(inf_plcc) != length(real_plc)-1
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
            return Cnew, mp, v
          end
        end
      end
    end
    #Need to consider more moduli.
    bound *= 2
    lc1 = _squarefree_ideals_with_bounded_norm(OK, bound, coprime = minimum(defining_modulus(C)[1], copy = false))
    lc = setdiff(lc, lc1)
  end
end

function approximate_artin_zeta_derivative_at_0(C::ClassField, mp::GrpAbFinGenMap, D::Dict{S, T}) where {S, T}
  Dzeta = Vector{acb}()
  ks = keys(D)
  CC = parent(first(values(D)))
  mp1 = inv(C.quotientmap)*mp
  k1, mk1 = kernel(mp1)
  ck, mck = cokernel(mk1)
  for x1 in ck
    x = mck\x1
    v = zero(CC)
    for k in ks
      v += D[k]*conj(k(x, CC.prec))
    end
    push!(Dzeta, v//(degree(C)))
  end
  return Dzeta
end

function approximate_derivative_Artin_L_function(chars::Vector{RCFCharacter{MapRayClassGrp, GrpAbFinGenMap}}, prec::Int)
  chars1 = Vector{RCFCharacter{MapRayClassGrp, GrpAbFinGenMap}}()
  idxs = Tuple{Int, Bool}[]
  for i = 1:length(chars)
    idx = 0
    cx = _conjugate(chars[i])
    for j = 1:length(chars1)
      if cx == chars1[j]
        idx = j
        break
      end
    end
    if iszero(idx)
      #The conjugate is not there.
      push!(chars1, chars[i])
      push!(idxs, (length(chars1), false))
    else
      push!(idxs, (idx, true))
    end
  end
  coeffs1 = _approximate_derivative_Artin_L_function(chars1, prec)
  if length(chars1) == length(chars)
    return Dict{RCFCharacter{MapRayClassGrp, GrpAbFinGenMap}, acb}(zip(chars, coeffs1))
  end
  coeffs = Dict{RCFCharacter{MapRayClassGrp, GrpAbFinGenMap}, acb}()
  for i = 1:length(chars)
    if idxs[i][2]
      coeffs[chars[i]] = conj(coeffs1[idxs[i][1]])
    else
      coeffs[chars[i]] = coeffs1[idxs[i][1]]
    end
  end
  return coeffs
end

function _find_N0(K::AnticNumberField, target_prec::Int, C::arb)
  R = ArbField(20+target_prec)
  r1, r2 = signature(K)
  n = degree(K)
  r = r1 + r2
  c_1 = n*R(2)^fmpq(-2*r2, n)
  p1 = (2*const_pi(R))^(r-1)
  p2 = n^r*p1//2^r2
  c_0 = sqrt(p2//(c_1^(r+1)))
  A0 = log(c_0*(fmpz(2)^target_prec))
  p2 = A0//c_1
  p1 = n*(r+1)*log(p2)//(2*(r+1)+4*A0)
  N0 = C*p2^(fmpq(n, 2))//(p1+1)
  return N0
end

function _approximate_derivative_Artin_L_function(chars::Vector, target_prec::Int)
  prec = 20+target_prec
  RR = ArbField(prec)
  K = base_field(chars[1].C)
  n = degree(K)
  maxC = (root(norm(conductor(chars[1].C)[1])*abs(discriminant(maximal_order(K))), 2)+1)//(sqrt(const_pi(RR))^degree(K))
  nterms = Int(Hecke.upper_bound(target_prec*sqrt(maxC)//2, fmpz))
  Acoeffs = Vector{arb}[_compute_A_coeffs(n, i, prec) for i = 0:nterms]
  coeffs_0 = Vector{arb}[_Aij_at_0(i, n, Acoeffs[i+1]) for i = 0:nterms]
  coeffs_1 = Vector{arb}[_Aij_at_1(i, n, Acoeffs[i+1]) for i = 0:nterms]
  den = 2*sqrt(const_pi(RR)^(n-1))
  coeffs_chi = compute_coeffs_L_function(chars, nterms, prec)
  res = Vector{acb}()
  for i = 1:length(chars)
    x = chars[i]
    A = _A_function(x, prec)
    lambda = _lambda_and_artin(x, target_prec, coeffs_0, coeffs_1, coeffs_chi[i])
    num = A*lambda
    push!(res, num/den)
  end
  return res
end

################################################################################
#
#  Coefficients L-function
#
################################################################################

function compute_coeffs_L_function(chars::Vector{T}, n::Int, prec::Int) where T <: RCFCharacter
  C = chars[1].C
  OK = base_ring(C)
  lp = prime_ideals_up_to(OK, n)
  sort!(lp, by = x -> norm(x, copy = false))
  CC = AcbField(prec)
  coeffs = Dict{Tuple{Int, Int, Int}, acb}()
  for j = 1:length(chars)
    coeffs[(j, 1, 0)] = one(CC)
    for i = 2:n
      coeffs[(j, i, 0)] = zero(CC)
    end
  end
  for h = 1:length(lp)
    P = lp[h]
    np = norm(P, copy = false)
    for i = 1:n
      v = valuation(i, np)
      if iszero(v)
        for j = 1:length(chars)
          coeffs[(j, i, h)] = coeffs[(j, i, h-1)]
        end
        continue
      end
      for j = 1:length(chars)
        chi = chars[j]
        r = chi(P, prec)
        res = zero(CC)
        for k = 0:v
          kk = (j, Int(divexact(i, np^k)), h-1)
          ckk = coeffs[kk]
          res += ckk*r^k
        end
        coeffs[(j, i, h)] = res
      end
    end
  end
  coeffs_res = Vector{Vector{acb}}(undef, length(chars))
  s = length(lp)
  for j = 1:length(chars)
    v = Vector{acb}(undef, n)
    for i = 1:n
      v[i] = coeffs[(j, i, s)]
    end
    coeffs_res[j] = v
  end
  return coeffs_res
end

function _test_coeffs(chi::RCFCharacter, n::Int, prec::Int)
  C = chi.C
  OK = base_ring(C)
  lI = ideals_up_to(OK, n)
  CC = AcbField(prec)
  coeffs = Vector{acb}(undef, n)
  for i = 1:n
    coeffs[i] = zero(CC)
  end
  for j = 1:length(lI)
    n = Int(norm(lI[j], copy = false))
    coeffs[n] += chi(lI[j], prec)
  end
  return coeffs
end


function ideals_up_to(OK::NfOrd, n::Int)

  lp = prime_ideals_up_to(OK, n)
  lI = NfOrdIdl[ideal(OK, 1)]
  for i = 1:length(lp)
    lnew = NfOrdIdl[]
    P = lp[i]
    nP = Int(norm(P, copy = false))
    @assert nP <= n
    expon = Int(flog(fmpz(n), nP))
    for j = 1:length(lI)
      I = lI[j]
      if norm(I, copy = false)*nP > n
        break
      end
      push!(lnew, I*P)
      for s = 2:expon
        if nP^s*norm(I, copy = false) > n
          break
        end
        push!(lnew, I*P^s)
      end
    end
    append!(lI, lnew)
    sort!(lI, by = x -> norm(x, copy = false))
  end
  return lI
end

################################################################################
#
#  Correction term
#
################################################################################

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
    if haskey(fcchi, p)
      continue
    end
    res = mul!(res, res, 1 - chi(p, prec))
  end
  return res
end

################################################################################
#
#  Artin root number
#
################################################################################

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
  @hassert :ClassField 1 istotally_positive(lambda)
  @hassert :ClassField 1 lambda in J
  g = numerator(simplify(ideal(OK, lambda) * inv(J)))
  @hassert :ClassField 1 iscoprime(g, c)
  u = idempotents(g, c)[1]
  u = make_positive(u, minimum(g^2))
  @hassert :ClassField 1 istotally_positive(u)
  @hassert :ClassField 1 u in g
  h = numerator(simplify(ideal(OK, u) * inv(g)))
  @hassert :ClassField 1 iscoprime(h, c)
  Qc, mQc = quo(OK, c)
  G, mG = multiplicative_group(Qc)
  reps = NfOrdElem[make_positive(lift(mG(x)), minimum(c)^2) for x in G]
  for (j, x) in enumerate(G)
    @hassert :ClassField 1 x == mG\Qc(reps[j])
    @hassert :ClassField 1 istotally_positive(reps[j])
  end
  Gsum = R(0)
  for i = 1:length(reps)
    el = reps[i].elem_in_nf*u.elem_in_nf//lambda.elem_in_nf
    trel = 2*tr(el)
    newtrel = fmpq(mod(numerator(trel), 2*denominator(trel)), denominator(trel))
    expi = exppii(R(newtrel))
    Gsum += chi(ideal(OK, reps[i]), prec) * expi
  end
  Gsum = mul!(Gsum, Gsum, chi(h, prec))
  res = (-onei(R))^length(chi.conductor_inf_plc)*Gsum/sqrt(R(norm(c)))
  return res
end

################################################################################
#
#  Lambda evaluation
#
################################################################################

global deb = []
function _lambda_and_artin(chi::RCFCharacter, target_prec::Int, coeffs_0, coeffs_1, coeffs_chi)
  prec = 20+target_prec
  K = base_field(chi.C)
  Wchi = artin_root_number(chi, prec)
  CC = AcbField(prec)
  res1 = zero(CC)
  res2 = zero(CC)
  cchi = _C(chi, prec)
  
  n = degree(K)
  terms = Vector{acb}()
  @show nterms_chi = Int(Hecke.upper_bound((target_prec*sqrt(cchi))//2, fmpz))
  @show _find_N0(K, target_prec, cchi)
  res = zero(CC)
  for i = 1:nterms_chi
    if iszero(coeffs_chi[i])
      continue
    end
    evpoint = cchi//i
    ev0, ev1 = _evaluate_f_x_0_1(evpoint, n, target_prec, coeffs_0, coeffs_1)
    res += coeffs_chi[i]*ev0 + Wchi*conj(coeffs_chi[i])*ev1
  end
  return res
end

function _C(chi::RCFCharacter, prec::Int)
  RR = ArbField(prec)
  c = conductor(chi)
  OK = order(c)
  nc = norm(c)
  p = const_pi(RR)^degree(OK)
  d = sqrt(RR(abs(discriminant(OK))))*sqrt(RR(nc)) 
  return d//sqrt(p)
end



function _evaluate_f_x_0_1(x::arb, n::Int, target_prec::Int, coeffs_0::Vector{Vector{arb}}, coeffs_1::Vector{Vector{arb}})
  RR = ArbField(20+target_prec)
  #nterms1 = min(nterms, 100)
  res0 = zero(RR)
  res1 = zero(RR)
  factorials = Vector{fmpz}(undef, n)
  factorials[1] = fmpz(1)
  for i = 2:n
    factorials[i] = factorials[i-1]*(i-1)
  end
  lnx = log(x)
  powslogx = powers(lnx, n-1)
  logsdivfact = arb[powslogx[i]//factorials[i] for i = 1:n]
  ix = inv(x)
  th = fmpq(1, 2)^(3+target_prec)
  ixpow = RR(1)
  for i = 0:length(coeffs_0)-1
    if iseven(i)
      m = 1
    else
      m = n-1
    end
    aij1 = coeffs_1[i+1]
    auxres1 = zero(RR)
    for j = 2:m+1
      auxres1 += aij1[j]*logsdivfact[j-1]
    end
    auxres1 = mul!(auxres1, auxres1, ixpow)
    res1 = add!(res1, res1, auxres1)

    aij0 = coeffs_0[i+1]
    auxres0 = zero(RR)
    for j = 2:length(aij0)
      auxres0 += aij0[j]*logsdivfact[j-1]
    end
    auxres0 = mul!(auxres0, auxres0, ixpow)
    res0 = add!(res0, res0, auxres0)
    if abs(auxres0) < th && abs(auxres1) < th
      break
    end
    #res0 += ixpow*auxres0
    ixpow = mul!(ixpow, ixpow, ix)
  end
  res1 += x*gamma(fmpq(1, 2), RR)*gamma(fmpz(1), RR)^(n-1)

  #CC = AcbField(prec)
  #res0int = (one(CC)/(2*const_pi(CC)*onei(CC)))*Nemo.integrate(CC, y -> x^y * gamma(y/2)*gamma((y+1)/2)^(n-1)/y, 1.1 - (nterms+0.1)*onei(CC), 1.1 + (nterms+0.1) * onei(CC))
  #res1int = (one(CC)/(2*const_pi(CC)*onei(CC)))*Nemo.integrate(CC, y -> x^y * gamma(y/2)*gamma((y+1)/2)^(n-1)/(y-1), 1.1 - (nterms+0.1)*onei(CC), 1.1 + (nterms+0.1) * onei(CC))
  #@assert overlaps(real(res0int), res0)
  #@assert overlaps(real(res1int), res1)
  #@show res0
  #@show res0int
  #return real(res0int), real(res1int)
  return res0, res1
end

function _Aij_at_0(i::Int, n::Int, aij::Vector{arb})
  #aij starts with ai0 and finishes with ain
  CC = parent(aij[1])
  if iseven(i)
    m = 1
  else
    m = n-1
  end
  if iszero(i)
    D = aij[1:m+2]
  else
    D = Vector{arb}(undef, m+1)
    D[m+1] = -aij[m+1]/i
    for j = m:-1:1
      D[j] = (D[j+1] - aij[j])/i
    end
  end
  #=
  ev = CC(-i)+CC(0.001)
  @show val1 = (gamma(ev/2)*gamma((ev+1)/2)^(n-1))/ev
  @show val2 = sum(D[j+1]/((ev+i)^j) for j = 0:m)
  @hassert :ClassField 1 radiuslttwopower(abs(val1-val2), 16)
  =#
  return D
end

function _Aij_at_1(i::Int, n::Int, aij::Vector{arb})
  #aij starts with ai0 and finishes with ain
  if iseven(i)
    m = 1
  else
    m = n-1
  end
  if iszero(i)
    aij = aij[2:end]
  end
  CC = parent(aij[1])
  D = Vector{arb}(undef, m+1)
  D[m+1] = -aij[m+1]/(i+1)
  for j = m:-1:1
    D[j] = (D[j+1] - aij[j])/(i+1)
  end
  #=
  ev = CC(-i)+CC(0.001)
  val1 = (gamma(ev/2)*gamma((ev+1)/2)^(n-1))/(ev-1)
  val2 = sum(D[j+1]/((ev+i)^j) for j = 0:m)
  @hassert :ClassField 1 radiuslttwopower(abs(val1-val2), 8)
  =#
  return D
end

function _compute_A_coeffs(n::Int, i::Int, prec::Int)
  RR = ArbField(prec)
  #res[j] contains A_{i,(j-1)}
  if iszero(i)
    #In this case, I need the i-1st coefficient
    res = Vector{arb}(undef, n+2)
    r = _coeff_0_even(n, 0, RR)
    r1 = _coeff_exp_0(n, RR)
    #Careful: in this case the indices are shifted.
    res[1] = r1[3]*r
    res[2] = r1[2]*r
    res[3] = r1[1]*r
    for j = 4:n+2
      res[j] = zero(RR)
    end
    #=
    ev = RR(0.00000001)
    val1 = gamma(ev/2)*gamma((ev+1)/2)^(n-1)/ev
    val2 = sum(res[j+1]/((ev)^j) for j = 0:n+1)
    @show i
    @show val1
    @show val2
    =#
    return res
  end
  if iseven(i)
    res = Vector{arb}(undef, n+1)
    q = divexact(i, 2)
    r = _coeff_0_even(n, q, RR)
    res[2] = r
    for j = 3:n+1
      res[j] = zero(RR)
    end
    r1 = _coeff_exp_1_even(n, q, RR)
    res[1] = r*r1
  else
    res = Vector{arb}(undef, n+1)
    q = divexact(i-1, 2)
    r0 = _coeff_0_odd(n, q, RR)
    vg = _coeff_exp_odd(n, q, RR) 
    res[n+1] = zero(RR)
    for j = 1:n
      res[j] = vg[n-j+1]*r0  
    end
  end
  #=
  ev = RR(-i)+RR(0.00000001)
  val1 = gamma(ev/2)*gamma((ev+1)/2)^(n-1)
  val2 = sum(res[j+1]/((ev+i)^j) for j = 0:n)
  @show i
  @show val1
  @show val2
  =#
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
  RRx = PowerSeriesRing(RR, n, "x", cached = false)[1]
  g = RRx(res, length(res), n, 1)
  gexp = exp(g)
  return arb[coeff(gexp, i) for i = 0:n-1]
end


function _coeff_exp_1_even(n::Int, q::Int, RR::ArbField)
  exc = (n-1)*_sum_pow_inv_odd(q-1, 1) + _sum_pow_inv_even(q, 1)
  inexc = fmpq(n, 2)*const_euler(RR)+(n-1)*log(RR(2))
  return exc - inexc
end

function _coeff_exp_0(n::Int, RR::ArbField)
  c0 = -fmpq(n, 2)*const_euler(RR)-(n-1)*log(RR(2))
  c1 = zeta(2, RR)*fmpq(3*n-2, 8)
  RRx = PowerSeriesRing(RR, 3, "x", cached = false)[1]
  g = RRx([c0, c1], 2, 3, 1)
  expg = exp(g)
  return arb[coeff(expg, i) for i = 0:2]
end

function _coeff_0_even(n::Int, q::Int, RR::ArbField)
  num = 2 * fmpz(4)^(q*(n-1))*factorial(fmpz(q))^(n-2)
  den = factorial(fmpz(2*q))^(n-1)
  r = fmpq(num, den)
  return (-1)^(q*n)*r*sqrt(const_pi(RR))^(n-1)
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


################################################################################
#
#  BigFloat version of the integral.
#
################################################################################
#=

function _evaluate_f_x_0_1BF(x::BigFloat, n::Int, prec::Int, nterms::Int, coeffs_0::Vector{Vector{BigFloat}}, coeffs_1::Vector{Vector{BigFloat}})
  nterms1 = nterms
  #nterms1 = min(nterms, 100)
  res0 = BigFloat(0)
  res1 = BigFloat(0)
  factorials = Vector{fmpz}(undef, n+1)
  factorials[1] = fmpz(1)
  for i = 2:n+1
    factorials[i] = factorials[i-1]*(i-1)
  end
  lnx = log(x)
  powslogx = powers(lnx, n-1)
  ix = inv(x)
  ixpow = RR(1)
  for i = 0:nterms1
    if iseven(i)
      m = 1
    else
      m = n-1
    end
    aij1 = coeffs_1[i+1]
    auxres1 = BigFloat(0)
    for j = 2:m+1
      auxres1 += (aij1[j]*powslogx[j-1])//factorials[j-1]
    end
    auxres1 *= ixpow
    res1 += auxres1

    aij0 = coeffs_0[i+1]
    auxres0 = BigFloat(0)
    for j = 2:length(aij0)
      auxres0 += (aij0[j]*powslogx[j-1])//factorials[j-1]
    end
    auxres0 *= ixpow
    res0 += auxres0

    ixpow *= ix
  end
  res1 += x*BigFloat(gamma(fmpq(1, 2), RR))*BigFloat(gamma(fmpz(1), RR))^(n-1)

  #CC = AcbField(prec)
  #res0int = (one(CC)/(2*const_pi(CC)*onei(CC)))*Nemo.integrate(CC, y -> x^y * gamma(y/2)*gamma((y+1)/2)^(n-1)/y, 1.1 - (nterms+0.1)*onei(CC), 1.1 + (nterms+0.1) * onei(CC))
  #res1int = (one(CC)/(2*const_pi(CC)*onei(CC)))*Nemo.integrate(CC, y -> x^y * gamma(y/2)*gamma((y+1)/2)^(n-1)/(y-1), 1.1 - (nterms+0.1)*onei(CC), 1.1 + (nterms+0.1) * onei(CC))
  #@assert overlaps(real(res0int), res0)
  #@assert overlaps(real(res1int), res1)
  #@show res0
  #@show res0int
  #return real(res0int), real(res1int)
  return res0, res1
end

function _Aij_at_0(i::Int, n::Int, aij::Vector{BigFloat})
  #aij starts with ai0 and finishes with ain
  if iseven(i)
    m = 1
  else
    m = n-1
  end
  if iszero(i)
    D = aij[1:m+2]
  else
    D = Vector{BigFloat}(undef, m+1)
    D[m+1] = -aij[m+1]/i
    for j = m:-1:1
      D[j] = (D[j+1] - aij[j])/i
    end
  end
  return D
end

function _Aij_at_1(i::Int, n::Int, aij::Vector{BigFloat})
  #aij starts with ai0 and finishes with ain
  if iseven(i)
    m = 1
  else
    m = n-1
  end
  if iszero(i)
    aij = aij[2:end]
  end
  D = Vector{BigFloat}(undef, m+1)
  D[m+1] = -aij[m+1]/(i+1)
  for j = m:-1:1
    D[j] = (D[j+1] - aij[j])/(i+1)
  end
  return D
end

function _compute_A_coeffs(n::Int, i::Int, prec::Int)
  #res[j] contains A_{i,(j-1)}
  if iszero(i)
    #In this case, I need the i-1st coefficient
    res = Vector{BigFloat}(undef, n+2)
    r = _coeff_0_even(n, 0, RR)
    r1 = _coeff_exp_0(n, RR)
    #Careful: in this case the indices are shifted.
    res[1] = r1[3]*r
    res[2] = r1[2]*r
    res[3] = r1[1]*r
    for j = 4:n+2
      res[j] = zero(BigFloat)
    end
    return res
  end
  if iseven(i)
    res = Vector{BigFloat}(undef, n+1)
    q = divexact(i, 2)
    r = _coeff_0_even(n, q)
    res[2] = r
    for j = 3:n+1
      res[j] = zero(BigFloat)
    end
    r1 = _coeff_exp_1_even(n, q)
    res[1] = r*r1
  else
    res = Vector{BigFloat}(undef, n+1)
    q = divexact(i-1, 2)
    r0 = _coeff_0_odd(n, q)
    vg = _coeff_exp_odd(n, q) 
    res[n+1] = zero(BigFloat)
    for j = 1:n
      res[j] = vg[n-j+1]*r0  
    end
  end

  return res
end

function _coeff_0_odd(n::Int, q::Int)
  exc_num = (-1)^(q*n+1)*fmpz(2)^(n+2*q)
  exc_den = (2*q+1)*factorial(fmpz(2*q))*factorial(fmpz(q))^(n-2)
  return sqrt(BigFloat(pi))*BigFloat(fmpq(exc_num, exc_den))
end

function _coeff_exp_odd(n::Int, q::Int)
  RR = ArbField(1000)
  res = Vector{BigFloat}(undef, n-1)
  res[1] = _sum_pow_inv_odd(q, 1) + (n-1)*_sum_pow_inv_even(q, 1) - log(BigFloat(2)) - fmpq(n, 2)*BigFloat(const_euler(RR))
  for k = 2:n-1
    res[k] = (-1)^k*BigFloat(zeta(k, RR))*(1+fmpq(n-2, fmpz(2)^k)) + _sum_pow_inv_odd(q, k) + (n-1)*_sum_pow_inv_even(q, k)
    res[k] = res[k]/k
  end
  RRx = PowerSeriesRing(parent(RR[1]), n, "x", cached = false)[1]
  g = RRx(res, length(res), n, 1)
  gexp = exp(g)
  return BigFloats[coeff(gexp, i) for i = 0:n-1]
end

function _coeff_exp_1_even(n::Int, q::Int)
  exc = (n-1)*_sum_pow_inv_odd(q-1, 1) + _sum_pow_inv_even(q, 1)
  inexc = fmpq(n, 2)*const_euler(RR)+(n-1)*log(RR(2))
  return exc - inexc
end

function _coeff_exp_0(n::Int, RR::ArbField)
  c0 = -fmpq(n, 2)*const_euler(RR)-(n-1)*log(RR(2))
  c1 = zeta(2, RR)*fmpq(3*n-2, 8)
  RRx = PowerSeriesRing(RR, 3, "x", cached = false)[1]
  g = RRx([c0, c1], 2, 3, 1)
  expg = exp(g)
  return [coeff(expg, i) for i = 0:2]
end

function _coeff_0_even(n::Int, q::Int, RR::ArbField)
  num = 2 * fmpz(4)^(q*(n-1))*factorial(fmpz(q))^(n-2)
  den = factorial(fmpz(2*q))^(n-1)
  r = fmpq(num, den)
  return (-1)^(q*n)*r*sqrt(const_pi(RR))^(n-1)
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


=#
