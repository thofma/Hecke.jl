################################################################################
#
#  Small interface to characters
#
################################################################################

function Base.show(io::IO, C::RCFCharacter)
  println(IOContext(io, :compact => true), "Character of $(C.C)")
end

function character(C::ClassField, x::FinGenAbGroupElem, mGhat::Map)
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

(chi::RCFCharacter)(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, prec::Int) = image(chi, I, prec)
(chi::RCFCharacter)(I::FinGenAbGroupElem, prec::Int) = image(chi, I, prec)

function image(chi::RCFCharacter{MapClassGrp, T}, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, prec::Int) where T
  CC = AcbField(prec)
  x = chi.x
  mGhat = chi.mGhat
  mpc = mGhat(x)
  C = chi.C
  mR = C.rayclassgroupmap
  mQ = C.quotientmap
  img = lift(mpc(mQ(mR\I)))
  if iszero(img)
    return one(CC)
  end
  return cispi(2*CC(img))
end

function image(chi::RCFCharacter{MapRayClassGrp, T}, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, prec::Int) where T
  CC = AcbField(prec)
  x = chi.x
  mGhat = chi.mGhat
  mpc = mGhat(x)
  c = conductor(chi)
  dc = defining_modulus(chi.C)[1]
  if c == dc
    if !is_coprime(I, c)
      return zero(CC)
    end
    C = chi.C
    mR = C.rayclassgroupmap
    if !isdefined(mR, :prime_ideal_preimage_cache)
      mR.prime_ideal_preimage_cache = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FinGenAbGroupElem}()
    end
    if haskey(mR.prime_ideal_preimage_cache, I)
      pim = mR.prime_ideal_preimage_cache[I]
    else
      pim = mR\I
      mR.prime_ideal_preimage_cache[I] = pim
    end
    mQ = C.quotientmap
    img = lift(mpc(mQ(pim)))
    if iszero(img)
      return one(CC)
    end
    return cispi(2*CC(img))
  end
  assure_with_conductor(chi)
  if !is_coprime(I, conductor(chi))
    return zero(CC)
  end
  mR = chi.mrcond
  mp = chi.mp_cond
  mQ = chi.C.quotientmap
  if !isdefined(mR, :prime_ideal_preimage_cache)
    mR.prime_ideal_preimage_cache = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FinGenAbGroupElem}()
  end
  if haskey(mR.prime_ideal_preimage_cache, I)
    el = mR.prime_ideal_preimage_cache[I]
  else
    el = mR\I
    mR.prime_ideal_preimage_cache[I] = el
  end
  el = mp\el
  el = mQ(el)
  el = mpc(el)
  img = lift(el)
  if iszero(img)
    return one(CC)
  end
  return cispi(2*CC(img))
end

function image(chi::RCFCharacter, x::FinGenAbGroupElem, prec::Int)
  CC = AcbField(prec)
  mp = chi.mGhat(chi.x)
  img = lift(mp(x))
  if iszero(img)
    return one(CC)
  end
  return cispi(CC(2*img))
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
  imgs = FinGenAbGroupElem[mr\x for x in lp]
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
  @hassert :ClassField 1 is_totally_real(K)
  c, inf_plc = conductor(C)
  @hassert :ClassField 1 isempty(inf_plc)
  C1, mp, v = _find_suitable_quadratic_extension(C)
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
  chars = RCFCharacter{MapRayClassGrp, FinGenAbGroupHom}[character(C1, x, mGhat) for x in Ghat if !iszero(lift(mGhat(x)(y)))]
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
      @vprintln :ClassField 1 "Guess not useful. Increasing precision to $(2*p)"
    elseif nb < p
      f = find_defining_polynomial(K, el, v)
      if degree(f) != degree(C)
        continue
      end
      mR = C.rayclassgroupmap
      mQ = C.quotientmap
      ng, mng = norm_group(f, mR, false, cached = false, check = false, of_closure = false)
      if iszero(mng*mQ)
        C.A = number_field(f, cached = false, check = false)[1]
        return nothing
      end
    end
  end
  p = max(64+p, nb)
  @vprintln :ClassField 1 "Guess: we need precision $(p)"
  while true
    approximations_derivative_Artin_L_functions = approximate_derivative_Artin_L_function(chars, p)
    el = approximate_artin_zeta_derivative_at_0(C1, mp, approximations_derivative_Artin_L_functions)
    f = find_defining_polynomial(K, el, v)
    if degree(f) != degree(C)
      p = 2*p
      @vprintln :ClassField 1 "Wrong guess, setting precision to $(p)"
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
    @vprintln :ClassField 1 "The reconstructed polynomial is wrong, setting precision to $(p)"
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

function approximate_defpoly(K::AbsSimpleNumField, el::Vector{AcbFieldElem})
  rts = ArbFieldElem[2*real(cosh(x)) for x in el]
  ps = power_sums(rts)
  pol = power_sums_to_polynomial(ps)
  @vprintln :ClassField 1 "Approximation: $pol"
  l2norm = ZZRingElem(0)
  for i = 0:degree(pol)
    c = coeff(pol, i)
    l2norm += upper_bound(ZZRingElem, abs(c)^2)
  end
  return true, nbits(l2norm)
end

function find_defining_polynomial(K::AbsSimpleNumField, el::Vector{AcbFieldElem}, v::InfPlc)
  OK = maximal_order(K)
  rts = ArbFieldElem[2*real(cosh(x)) for x in el]
  ps = power_sums(rts)
  pol = power_sums_to_polynomial(ps)
  attempt = _find_coeffs(K, pol, v)
  if degree(attempt) == length(el)
    return attempt
  end
  rt1 = ArbFieldElem[x^2-2 for x in rts]
  ps = power_sums(rt1)
  pol = power_sums_to_polynomial(ps)
  return _find_coeffs(K, pol, v)
end

function _find_coeffs(K, pol, v)
  Kt = polynomial_ring(K, "t", cached = false)[1]
  OK = maximal_order(K)
  B = basis(OK, K)
  bconjs = [real(evaluate(x, _embedding(v), 2*precision(parent(pol)))) for x in B]
  coeffs = Vector{AbsSimpleNumFieldElem}(undef, degree(pol)+1)
  for i = 1:degree(pol)
    c = coeff(pol, i-1)
    bn = 3*nbits(Hecke.upper_bound(ZZRingElem, c))
    fl, comb = _approximate(c, bconjs, bn)
    if !fl
      add = 10
      while !fl && add < 100
        fl, comb = _approximate(c, bconjs, bn)
        add += 10
      end
      return Kt()
    end
    coeffs[i] = dot(comb, B)
  end
  coeffs[end] = one(K)
  return Kt(coeffs)
end

function _approximate(el::ArbFieldElem, A::Vector{ArbFieldElem}, bits::Int)
  n = length(A)
  V0 = floor(ldexp(el, bits) + 0.5)
  V = [floor(ldexp(s, bits) + 0.5) for s in A]
  M = zero_matrix(ZZ, n + 1, n + 2)
  for i = 1:n
    M[i, i] = 1
    flag, M[i, n + 2] = unique_integer(V[i])
    !flag && return false, ZZRingElem[M[1, 1]]
  end
  M[n + 1, n + 1] = 1
  flag, M[n + 1, n + 2] = unique_integer(-V0)
  !flag && return false, ZZRingElem[M[1, 1]]
  lll!(M, LLLContext(0.99999, 0.5001))
  if !isone(abs(M[1, n + 1]))
    return false, ZZRingElem[M[1, 1]]
  end
  if isone(M[1, n + 1])
    res = ZZRingElem[M[1, i] for i = 1:n]
  else
    res = ZZRingElem[-M[1, i] for i = 1:n]
  end
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
  bound = 10
  ctx = rayclassgrp_ctx(OK, Int(exponent(C))*2)
  allow_cache!(ctx.class_group_map)
  lc = ideals_up_to(OK, bound, conductor(C)[1])
  cnt = 0
  while true
    @vprintln :ClassField 1 "Batch of ideals with $(length(lc)) elements"
    for I in lc
      for i = 1:length(real_plc)
        v = real_plc[i]
        w = [real_plc[j] for j = 1:length(real_plc) if j != i]
        lf = factor(I)
        newc = merge(max, c, lf)
        r, mr = ray_class_group_quo(OK, newc, w, ctx)
        gens, group_gens = find_gens(mr)
        images = FinGenAbGroupElem[mQ(mR\J) for J in gens]
        mp = hom(group_gens, images, check = false)
        k, mk = kernel(mp)
        ls = subgroups(k, quotype = Int[2], fun = (x, y) -> sub(x, y, false)[2])
        for ms in ls
          ms::FinGenAbGroupHom
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
    lc1 = ideals_up_to(OK, bound, conductor(C)[1])
    lc = setdiff(lc1, lc)
  end
end

function approximate_artin_zeta_derivative_at_0(C::ClassField, mp::FinGenAbGroupHom, D::Dict{S, T}) where {S, T}
  Dzeta = Vector{AcbFieldElem}()
  ks = keys(D)
  CC = parent(first(values(D)))
  R = codomain(C.quotientmap)
  mp1 = hom(R, codomain(mp), FinGenAbGroupElem[mp(C.quotientmap\x) for x in gens(R)])
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

function approximate_derivative_Artin_L_function(chars::Vector{RCFCharacter{MapRayClassGrp, FinGenAbGroupHom}}, prec::Int)
  chars1 = Vector{RCFCharacter{MapRayClassGrp, FinGenAbGroupHom}}()
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
    return Dict{RCFCharacter{MapRayClassGrp, FinGenAbGroupHom}, AcbFieldElem}(zip(chars, coeffs1))
  end
  coeffs = Dict{RCFCharacter{MapRayClassGrp, FinGenAbGroupHom}, AcbFieldElem}()
  for i = 1:length(chars)
    if idxs[i][2]
      coeffs[chars[i]] = conj(coeffs1[idxs[i][1]])
    else
      coeffs[chars[i]] = coeffs1[idxs[i][1]]
    end
  end
  return coeffs
end

function _limx(K::AbsSimpleNumField, target_prec::Int)
  R = ArbField(3*target_prec)
  r1, r2 = signature(K)
  n = degree(K)
  r = r1 + r2
  c_1 = n*R(2)^QQFieldElem(-2*r2, n)
  p1 = (2*const_pi(R))^(r-1)
  p2 = n^r*p1//2^r2
  c_0 = sqrt(p2//(c_1^(r+1)))
  A0 = log(c_0*(ZZRingElem(2)^target_prec))
  p2 = A0//c_1
  p1 = n*(r+1)*log(p2)//(2*(r+1)+4*A0)
  return p2^(QQFieldElem(n, 2))//(p1+1)
end

function _find_N0(K::AbsSimpleNumField, target_prec::Int, C::ArbFieldElem)
  N0 = C*_limx(K, target_prec)
  return N0
end

function _B(K::AbsSimpleNumField, target_prec::Int)
  R = ArbField(3*target_prec)
  return degree(K)*R(2)^(target_prec)//sqrt(const_pi(R)^3*_limx(K, target_prec))
end

function _find_i0(K::AbsSimpleNumField, target_prec::Int)
  B = _B(K, target_prec)
  limx = _limx(K, target_prec)
  i0 = 300
  while limx^i0*(factorial(ZZRingElem(div(i0, 2)))) < B
    i0 *= 2
  end
  imax = i0
  imin = div(i0, 2)
  while imax - imin > 2
    attempt = div(imax + imin, 2)
    if limx^attempt*(factorial(ZZRingElem(div(attempt, 2)))) < B
      imin = attempt
    else
      imax = attempt
    end
  end
  return imax
end

function _approximate_derivative_Artin_L_function(chars::Vector, target_prec::Int)
  K = base_field(chars[1].C)
  n = degree(K)
  if n == 2
   return  _approximate_derivative_Artin_L_function_quadratic(chars, target_prec)
  end
  prec = min(10, div(degree(chars[1].C), 2))*target_prec
  RR = ArbField(prec)
  maxC = (iroot(norm(conductor(chars[1].C)[1])*abs(discriminant(maximal_order(K))), 2)+1)//(sqrt(const_pi(RR))^degree(K))
  nterms = Int(Hecke.upper_bound(ZZRingElem, target_prec*maxC//2))
  i0 = _find_i0(K, target_prec)
  Acoeffs = _compute_A_coeffs(n, i0, prec)
  factorials = Vector{ZZRingElem}(undef, n)
  factorials[1] = ZZRingElem(1)
  for i = 2:length(factorials)
    factorials[i] = factorials[i-1]*(i-1)
  end
  coeffs_0 = Vector{ArbFieldElem}[_Aij_at_0(i, n, Acoeffs[i+1], factorials) for i = 0:i0]
  coeffs_1 = Vector{ArbFieldElem}[_Aij_at_1(i, n, Acoeffs[i+1], factorials) for i = 0:i0]
  den = 2*sqrt(const_pi(RR)^(n-1))
  res = Vector{AcbFieldElem}()
  for i = 1:length(chars)
    x = chars[i]
    A = _A_function(x, prec)
    lambda = _lambda_and_artin(x, target_prec, coeffs_0, coeffs_1, compute_coeffs_L_function(x, nterms, prec))
    num = A*lambda
    push!(res, num/den)
  end
  return res
end

function _approximate_derivative_Artin_L_function_quadratic(chars::Vector, target_prec::Int)
  prec = min(10, div(degree(chars[1].C), 2))*target_prec
  RR = ArbField(prec)
  res = Vector{AcbFieldElem}()
  den = 2*sqrt(const_pi(RR))
  @vtime :ClassField 1 vf = compute_values_f_quadratic(chars, target_prec)
  for i = 1:length(chars)
    x = chars[i]
    A = _A_function(x, prec)
    lambda = _lambda_and_artin_quadratic(x, target_prec, vf)
    num = A*lambda
    push!(res, num/den)
  end
  return res
end

function compute_values_f_quadratic(chars::Vector, target_prec::Int)
  prec = min(10, div(degree(chars[1].C), 2))*target_prec
  res = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{Tuple{ArbFieldElem, ArbFieldElem}}}()
  for x in chars
    c = conductor(x)
    if haskey(res, c)
      continue
    end
    cx = _C(x, prec)
    nterms = Int(Hecke.upper_bound(ZZRingElem, (target_prec*cx)//2))
    v = Vector{Tuple{ArbFieldElem, ArbFieldElem}}(undef, nterms)
    v0 = _evaluate_f_x_0(cx, prec, 2*target_prec, nterms)
    for i = 1:length(v)
      val = cx//i
      v1 = _evaluate_f_x_1(val, prec)
      v[i] = (v0[i], v1)
    end
    res[c] = v
  end
  return res
end


################################################################################
#
#  Coefficients L-function
#
################################################################################

function compute_coeffs_L_function(chi::T, n::Int, prec::Int) where T <: RCFCharacter
  C = chi.C
  OK = base_ring(C)
  lp = prime_ideals_up_to(OK, n)
  sort!(lp, by = x -> norm(x, copy = false))
  CC = AcbField(prec)
  coeffs_old = Vector{AcbFieldElem}(undef, n)
  coeffs_old[1] = one(CC)
  for j = 2:n
    coeffs_old[j] =  zero(CC)
  end
  coeffs_new = Vector{AcbFieldElem}(undef, n)
  for h = 1:length(lp)
    P = lp[h]
    r = chi(P, prec)
    np = Int(norm(P, copy = false))
    j = np
    while j <= n
      v = valuation(j, np)
      res = zero(CC)
      if iszero(r)
        coeffs_new[j] = res
        j += np
        continue
      end
      r1 = one(CC)
      aux = CC()
      for k = 0:v
        kk = divexact(j, np^k)
        ckk = coeffs_old[kk]
        mul!(aux, ckk, r1)
        add!(res, res, aux)
        #res += ckk*r1
        mul!(r1, r1, r)
      end
      coeffs_new[j] = res
      j += np
    end
    #Now, I need to shift the column...
    j = np
    while j <= n
      coeffs_old[j] = coeffs_new[j]
      j += np
    end
  end
  return coeffs_old
end

function ideals_up_to(OK::AbsSimpleNumFieldOrder, n::Int, coprime_to::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem} = ideal(OK, 1))

  lp = prime_ideals_up_to(OK, n)
  filter!(x -> is_coprime(x, coprime_to), lp)
  lI = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[ideal(OK, 1)]
  for i = 1:length(lp)
    lnew = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
    P = lp[i]
    nP = Int(norm(P, copy = false))
    @assert nP <= n
    expon = Int(flog(ZZRingElem(n), nP))
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
  @hassert :ClassField 1 is_totally_positive(lambda)
  @hassert :ClassField 1 lambda in J
  g = numerator(simplify(ideal(OK, lambda) * inv(J)))
  @hassert :ClassField 1 is_coprime(g, c)
  u = idempotents(g, c)[1]
  u = make_positive(u, minimum(g^2))
  @hassert :ClassField 1 is_totally_positive(u)
  @hassert :ClassField 1 u in g
  h = numerator(simplify(ideal(OK, u) * inv(g)))
  @hassert :ClassField 1 is_coprime(h, c)
  Qc, mQc = quo(OK, c)
  G, mG = multiplicative_group(Qc)
  reps = AbsSimpleNumFieldOrderElem[make_positive(lift(mG(x)), minimum(c)^2) for x in G]
  for (j, x) in enumerate(G)
    @hassert :ClassField 1 x == mG\Qc(reps[j])
    @hassert :ClassField 1 is_totally_positive(reps[j])
  end
  Gsum = R(0)
  for i = 1:length(reps)
    el = reps[i].elem_in_nf*u.elem_in_nf//lambda.elem_in_nf
    trel = 2*tr(el)
    newtrel = QQFieldElem(mod(numerator(trel), 2*denominator(trel)), denominator(trel))
    expi = cispi(R(newtrel))
    Gsum += chi(ideal(OK, reps[i]), prec) * expi
  end
  Gsum = mul!(Gsum, Gsum, chi(h, prec))
  res = (-onei(R))^length(chi.conductor_inf_plc)*Gsum/sqrt(R(norm(c)))
  return res
end

################################################################################
#
#  Lambda evaluation for quadratic fields
#
################################################################################

function _lambda_and_artin_quadratic(chi::RCFCharacter, target_prec::Int, vf::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{Tuple{ArbFieldElem, ArbFieldElem}}})
  prec = min(10, div(degree(chi.C), 2))*target_prec
  Wchi = artin_root_number(chi, prec)
  CC = AcbField(prec)
  c = conductor(chi)
  vals = vf[c]
  nterms_chi = length(vals)
  @vprintln :ClassField 1 "Computing $(nterms_chi) coefficients Artin L function"
  @vtime :ClassField 1 val_chi = compute_coeffs_L_function(chi, nterms_chi, prec)
  res1 = zero(CC)
  res2 = zero(CC)
  aux = CC()
  for i = 1:nterms_chi
    if iszero(val_chi[i])
      continue
    end
    mul!(aux, val_chi[i], vals[i][1])
    add!(res1, res1, aux)
    #res1 += val_chi[i]*vals[i][1]
    mul!(aux, conj(val_chi[i]), vals[i][2])
    add!(res2, res2, aux)
    #res2 += conj(val_chi[i])*vals[i][2]
  end
  return res1 + Wchi*res2
end

function _evaluate_f_x_1(x::ArbFieldElem, prec::Int)
  RR = parent(x)
  return x*sqrt(const_pi(RR))*exp(-2//x)
end

function _evaluate_f_x_0(x::ArbFieldElem, prec::Int)
  RR = parent(x)
  CC = AcbField(precision(RR))
  return 2*sqrt(const_pi(RR))*real(exp_integral_e(one(CC), CC(2//x)))
end

function _evaluate_f_x_0(x::ArbFieldElem, prec::Int, tolerance::Int, N::Int)
  CC = AcbField(prec)
  RR = ArbField(prec)
  res = Vector{ArbFieldElem}(undef, N)
  A = 2//x
  res[N] = real(exp_integral_e(one(CC), CC(N*A)))
  nstop = Int(upper_bound(ZZRingElem, ceil(4//A)))
  n = N
  e0 = exp(A)
  e1 = exp(-N*A)
  th = QQFieldElem(1, 2)^tolerance
  while n > nstop
    first = true
    res[n-1] = zero(RR)
    f0 = e1
    f1 = -f0//n
    m = 1
    d = QQFieldElem(-1)
    s = res[n]
    while abs(s) > th
      add!(res[n-1], res[n-1], s)
      #res[n-1] += s
      s = d*f1
      f0 = -A*f0
      f1 = -(m*f1+f0)//n
      m += 1
      d = -d//m
    end
    n = n-1
    e1 = e0*e1
  end
  for i = 1:nstop
    res[i] = real(exp_integral_e(one(CC), CC(2*i//x)))
  end
  cc = 2*sqrt(const_pi(RR))
  for i = 1:N
    mul!(res[i], res[i], cc)
    #res[i] = cc*res[i]
  end
  return res
end


################################################################################
#
#  Lambda evaluation - general case
#
################################################################################

function _lambda_and_artin(chi::RCFCharacter, target_prec::Int, coeffs_0, coeffs_1, coeffs_chi)
  prec = min(10, div(degree(chi.C), 2))*target_prec
  K = base_field(chi.C)
  Wchi = artin_root_number(chi, prec)
  CC = AcbField(prec)
  res1 = zero(CC)
  res2 = zero(CC)
  cchi = _C(chi, prec)
  n = degree(K)
  nterms_chi = Int(Hecke.upper_bound(ZZRingElem, target_prec*cchi//2))
  res1 = zero(CC)
  res2 = zero(CC)
  aux = CC()
  for i = 1:nterms_chi
    if iszero(coeffs_chi[i])
      continue
    end
    evpoint = cchi//i
    ev0, ev1 = _evaluate_f_x_0_1(evpoint, n, target_prec, coeffs_0, coeffs_1)
    mul!(aux, coeffs_chi[i], ev0)
    add!(res1, res1, aux)
    mul!(aux, conj(coeffs_chi[i]), ev1)
    add!(res2, res2, aux)
  end
  return res1 + Wchi*res2
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



function _evaluate_f_x_0_1(x::ArbFieldElem, n::Int, target_prec::Int, coeffs_0::Vector{Vector{ArbFieldElem}}, coeffs_1::Vector{Vector{ArbFieldElem}})
  RR = ArbField(3*target_prec)
  res0 = zero(RR)
  res1 = zero(RR)
  lnx = log(x)
  powslogx = powers(lnx, n-1)
  ix = inv(x)
  th = RR(QQFieldElem(1, 2)^(3+target_prec))
  ixpow = RR(1)
  aux = RR()
  for i = 0:length(coeffs_0)-1
    if iseven(i)
      m = 1
    else
      m = n-1
    end
    aij1 = coeffs_1[i+1]
    auxres1 = zero(RR)
    for j = 2:m+1
      mul!(aux, aij1[j], powslogx[j-1])
      add!(auxres1, auxres1, aux)
      #auxres1 += aij1[j]*powslogx[j-1]
    end
    auxres1 = mul!(auxres1, auxres1, ixpow)
    res1 = add!(res1, res1, auxres1)

    aij0 = coeffs_0[i+1]
    auxres0 = zero(RR)
    for j = 2:length(aij0)
      mul!(aux, aij0[j], powslogx[j-1])
      add!(auxres0, auxres0, aux)
      #auxres0 += aij0[j]*powslogx[j-1]
    end
    auxres0 = mul!(auxres0, auxres0, ixpow)
    res0 = add!(res0, res0, auxres0)
    if iszero(mod(i, 15)) && abs(auxres0) < th && abs(auxres1) < th
      break
    end
    #res0 += ixpow*auxres0
    ixpow = mul!(ixpow, ixpow, ix)
  end
  res1 += x*gamma(QQFieldElem(1, 2), RR)*gamma(ZZRingElem(1), RR)^(n-1)

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

function _Aij_at_0(i::Int, n::Int, aij::Vector{ArbFieldElem}, factorials::Vector{ZZRingElem})
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
    D = Vector{ArbFieldElem}(undef, m+1)
    D[m+1] = -aij[m+1]/i
    for j = m:-1:1
      D[j] = (D[j+1] - aij[j])/i
    end
  end
  for i = 2:length(D)
    D[i] = D[i]//factorials[i-1]
  end
  #=
  ev = CC(-i)+CC(0.001)
  @show val1 = (gamma(ev/2)*gamma((ev+1)/2)^(n-1))/ev
  @show val2 = sum(D[j+1]/((ev+i)^j) for j = 0:m)
  @hassert :ClassField 1 radiuslttwopower(abs(val1-val2), 16)
  =#
  return D
end

function _Aij_at_1(i::Int, n::Int, aij::Vector{ArbFieldElem}, factorials::Vector{ZZRingElem})
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
  D = Vector{ArbFieldElem}(undef, m+1)
  D[m+1] = -aij[m+1]/(i+1)
  for j = m:-1:1
    D[j] = (D[j+1] - aij[j])/(i+1)
  end
  for i = 2:length(D)
    D[i] = D[i]//factorials[i-1]
  end
  #=
  ev = CC(-i)+CC(0.001)
  val1 = (gamma(ev/2)*gamma((ev+1)/2)^(n-1))/(ev-1)
  val2 = sum(D[j+1]/((ev+i)^j) for j = 0:m)
  @hassert :ClassField 1 radiuslttwopower(abs(val1-val2), 8)
  =#
  return D
end

function _compute_A_coeffs(n::Int, nterms::Int, prec::Int)
  RR = ArbField(prec)
  #res[j] contains A_{i,(j-1)}
  res_final = Vector{Vector{ArbFieldElem}}(undef, nterms+1)
  spi = sqrt(const_pi(RR))
  coeffs_exp_even = _coeffs_exp_even(n, nterms, RR)
  coeffs_exp_odd = _coeffs_exp_odd(n, nterms, RR)
  spipow = spi^(n-1)
  for i = 0:nterms
    if iszero(i)
      #In this case, I need the i-1st coefficient
      res = Vector{ArbFieldElem}(undef, 3)
      r = spipow*_coeff_0_even(n, 0)
      r1 = _coeff_exp_0(n, RR)
      #Careful: in this case the indices are shifted.
      mul!(r1[3], r1[3], r)
      res[1] = r1[3]
      mul!(r1[2], r1[2], r)
      res[2] = r1[2]
      mul!(r1[1], r1[1], r)
      res[3] = r1[1]
    elseif iseven(i)
      res = Vector{ArbFieldElem}(undef, 2)
      q = divexact(i, 2)
      r = spipow*_coeff_0_even(n, q)
      res[2] = r
      r1 = coeffs_exp_even[q]
      res[1] = r*r1
    else
      res = Vector{ArbFieldElem}(undef, n+1)
      q = divexact(i-1, 2)
      r0 = spi*_coeff_0_odd(n, q)
      vg = coeffs_exp_odd[q+1]
      res[n+1] = zero(RR)
      for j = 1:n
        mul!(vg[n-j+1], vg[n-j+1], r0)
        res[j] = vg[n-j+1]
      end
    end
    res_final[i+1] = res
  end
  return res_final
end

function _coeff_0_odd(n::Int, q::Int)
  exc_num = ZZRingElem(2)^(n+2*q)
  exc_den = (2*q+1)*factorial(ZZRingElem(2*q))*factorial(ZZRingElem(q))^(n-2)
  r = QQFieldElem(exc_num, exc_den)
  if iseven(q) || iseven(n)
    return -r
  else
    return r
  end
end

function _coeff_exp_odd(n::Int, q::Int, RR::ArbField)
  res = Vector{ArbFieldElem}(undef, n-1)
  res[1] = _sum_pow_inv_odd(q, 1) + (n-1)*_sum_pow_inv_even(q, 1) - log(RR(2)) - QQFieldElem(n, 2)*const_euler(RR)
  for k = 2:n-1
    res[k] = (-1)^k*zeta(k, RR)*(1+QQFieldElem(n-2, ZZRingElem(2)^k)) + _sum_pow_inv_odd(q, k) + (n-1)*_sum_pow_inv_even(q, k)
    res[k] = res[k]/k
  end
  RRx = power_series_ring(RR, n, "x", cached = false)[1]
  g = RRx(res, length(res), n, 1)
  gexp = exp(g)
  return ArbFieldElem[coeff(gexp, i) for i = 0:n-1]
end

function _coeffs_exp_odd(n::Int, nterms::Int, RR::ArbField)
  nt = div(nterms, 2)
  if isodd(nterms)
    nt += 1
  end
  RRx = power_series_ring(RR, n, "x", cached = false)[1]
  res = Vector{Vector{ArbFieldElem}}(undef, nt)
  sum_pow_inv_odd = Vector{QQFieldElem}(undef, n-1)
  sum_pow_inv_even = Vector{QQFieldElem}(undef, n-1)
  for i = 1:n-1
    sum_pow_inv_odd[i] = QQFieldElem(0)
    sum_pow_inv_even[i] = QQFieldElem(0)
  end
  inexc =  log(RR(2)) + QQFieldElem(n, 2)*const_euler(RR)
  zeta_k = Vector{ArbFieldElem}(undef, n-2)
  for i = 1:n-2
    if iseven(i)
      zeta_k[i] = -zeta(i+1, RR)
    else
      zeta_k[i] = zeta(i, RR)
    end
  end
  for q = 0:nt-1
    for j = 1:n-1
      sum_pow_inv_odd[j] += QQFieldElem(1, (2*q+1)^j)
      if !iszero(q)
        sum_pow_inv_even[j] += (n-1)*QQFieldElem(1, (2*q)^j)
      end
    end
    res_q = Vector{ArbFieldElem}(undef, n-1)
    res_q[1] = sum_pow_inv_odd[1] + sum_pow_inv_even[1] - inexc
    for k = 2:n-1
      res_q[k] = zeta_k[k-1]*(1+QQFieldElem(n-2, ZZRingElem(2)^k)) + sum_pow_inv_odd[k] + sum_pow_inv_even[k]
      res_q[k] = res_q[k]/k
    end
    g = RRx(res_q, length(res_q), n, 1)
    gexp = exp(g)
    res[q+1] = ArbFieldElem[coeff(gexp, i) for i = 0:n-1]
  end
  return res
end

function _coeffs_exp_even(n::Int, nterms::Int, RR::ArbField)
  inexc = QQFieldElem(n, 2)*const_euler(RR)+(n-1)*log(RR(2))
  res = Vector{ArbFieldElem}(undef, div(nterms, 2))
  sum_inv_odd = QQFieldElem(0)
  sum_inv_even = QQFieldElem(1, 2)
  res[1] = sum_inv_even - inexc
  for q = 2:length(res)
    sum_inv_odd += (n-1)*QQFieldElem(1, (2*q-1))
    sum_inv_even += QQFieldElem(1, 2*q)
    res[q] = sum_inv_odd + sum_inv_even - inexc
  end
  return res
end

function _coeff_exp_0(n::Int, RR::ArbField)
  c0 = -QQFieldElem(n, 2)*const_euler(RR)-(n-1)*log(RR(2))
  c1 = zeta(2, RR)*QQFieldElem(3*n-2, 8)
  RRx = power_series_ring(RR, 3, "x", cached = false)[1]
  g = RRx([c0, c1], 2, 3, 1)
  expg = exp(g)
  return ArbFieldElem[coeff(expg, i) for i = 0:2]
end

function _coeff_0_even(n::Int, q::Int)
  num = 2 * ZZRingElem(4)^(q*(n-1))*factorial(ZZRingElem(q))^(n-2)
  den = factorial(ZZRingElem(2*q))^(n-1)
  r = QQFieldElem(num, den)
  if iseven(q) || iseven(n)
    return r
  else
    return -r
  end
end
