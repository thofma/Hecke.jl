function rcf_using_stark_units(C::T; cached::Bool = true) where T <: ClassField_pp
  K = base_field(C)
  @assert istotally_real(K)
  c, inf_plc = conductor(C)
  @assert isempty(inf_plc)
  C1 = _find_suitable_quadratic_extension(C)
  Ghat, mGhat = dual_group(codomain(C1.quotient_map))
  p = 32
  while true
    approximations_derivative_Artin_L_functions = Dict{GrpAbFinGenElem, acb}()
    for x in Ghat
      approximations_derivative_Artin_L_functions[x] = approximate_derivative_Artin_L_function(C1, mGhat, x, p)
    end
    el = approximate_artin_zeta_derivative_at_0(C1, mGhat, approximations_derivative_Artin_L_functions)
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
  v = arb_poly[x-(real(exp(2*a)-exp(-2*a)) for a in el]
  f = my_prod(v)
  n = degree(f)
  coeffs = arb[coeff(f, i) for i = 0:n-1]
  for x in coeffs 
    if !radiuslttwopower(x, 8)
      @show "here"
      return Kt()
    end
  end
  final_coeffs = Vector{nf_elem}(undef, n)
  #TODO: Choose a proper bound!
  bound = 1
  for i = 0:n-1
    bound_other_embs = 2^(n-i)*binomial(n, i)
    bound_v = upper_bound(coeffs[i])
    bound = max((n-1)*bound_other_embs^2+bound_v, bound)
  end
  #Now, I have a polynomial over the reals. I use lattice enumeration to recover the 
  #coefficients as elements of K
  gram_mat = trace_matrix(OK) #The field is totally real :)
  elts = __enumerate_gram(gram_mat, bound)
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
          return Cnew
        end
      end
    end
    #Need to consider more moduli.
    bound *= 2
    lc1 = _squarefree_ideals_with_bounded_norm(OK, bound, coprime = minimum(defining_modulus(C)[1], copy = false))
    lc = setdiff(lc, lc1)
  end
end