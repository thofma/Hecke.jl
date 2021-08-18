################################################################################
#
#  Steinitz number
#
################################################################################

function steinitz_number(a::T) where T <: Union{gfp_poly, gfp_fmpz_poly}
  p =  characteristic(parent(a))
  pq = fmpz(1)
  st_a = fmpz(0)
  for i = 0:degree(a)
    st_a += lift(coeff(a, i))*pq
    pq *= p
  end
  return st_a
end

function steinitz_number(a::fq_nmod)
  q = characteristic(parent(a))
  pq = fmpz(1)
  st_a = fmpz(0)
  for i = 0:degree(parent(a))
    st_a += coeff(a, i)*pq
    pq *= q
  end
  return st_a
end

function steinitz_number(a::fq)
  q = characteristic(parent(a))
  pq = fmpz(1)
  st_a = fmpz(0)
  for i = 0:degree(parent(a))
    st_a += steinitz_number(coeff(a, i))*pq
    pq *= q
  end
  return st_a
end

function steinitz_number(a::T) where T <: RelFinFieldElem
  q = order(base_field(parent(a)))
  pq = fmpz(1)
  st_a = fmpz(0)
  for i = 0:degree(parent(a))
    st_a += steinitz_number(coeff(a, i))*pq
    pq *= q
  end
  return st_a
end


function steinitz_number(a::T) where T <: Union{gfp_elem, gfp_fmpz_elem}
  return lift(a)
end

################################################################################
#
#  Presentation for extensions of prime power degree
#
################################################################################
@doc Markdown.doc"""
    presentation(p, r, n) -> FinField

Computes a presentation for the finite field of order p^(r^n) as defined
by Plesken.
"""
function presentation(p::T, r::T, n::Int) where T <: Union{fmpz, Int}
  F = GF(p, cached = false)
  if r == p
    return _presentation_artin_schreier(F, n)
  elseif iszero(mod(p - 1, r))
    return _presentation_kummer(F, r, n)
  else
    return _presentation_generic(F, r, n)
  end
end

function _presentation_artin_schreier(F, n)
  p = characteristic(F)
  Fx, x = PolynomialRing(F, "x", cached = false)
  F1, a = FiniteField(x^p-x-1, "a", cached = false, check = false)
  F1y, y = PolynomialRing(F1, "y1", cached = false)
  el = a
  for i = 2:n
    pol = y^p-y-el^(p-1)
    Frel = FiniteField(pol, "a$i", cached = false, check = false)[1]
    abs_def_pol = norm(pol)
    F1, gF1 = FiniteField(abs_def_pol, "a", check = false, cached = false)
    mp = hom(F1, Frel, gen(Frel))
    el = mp\(gen(Frel)*el)
    F1y, y = PolynomialRing(F1, "y1", cached = false)
  end
  return F1
end

function smallest_pkth_root(F, r)
  #First, I find a rk-th root of unity
  #by taking random elements
  p = order(F)
  nit, cop = ppio(p-1, fmpz(r))
  exp_order = divexact(nit, r)
  x = rand(F)^cop
  while iszero(x) || isone(x^exp_order)
    x = rand(F)^cop
  end
  k = valuation(p-1, r)
  #Now, iteratively, I search for
  #the smallest r-th root
  pow_ind = 1
  for i = 1:k
    root = x^(pow_ind*fmpz(r)^(k-i))
    roots = powers(root, Int(r-1))
    new_ind = 2
    st = steinitz_number(roots[2])
    for j = 3:length(roots)
      stj = steinitz_number(roots[j])
      if stj < st
        st = stj
        new_ind = j
      end
    end
    pow_ind *= new_ind-1
  end
  return x^pow_ind
end


function _presentation_kummer(F, r::T, n::Int) where T <: Union{fmpz, Int}
  pr_root = smallest_pkth_root(F, r)
  Fx, gFx = PolynomialRing(F, cached = false)

  def_pol1 = Fx()
  setcoeff!(def_pol1, 0, -pr_root)
  setcoeff!(def_pol1, r^n, one(F))
  F1, gF1 = FiniteField(def_pol1, "a1", cached = false, check = false)
  return F1
end

function _presentation_generic(F, r::T, n::Int) where T <: Union{fmpz, Int}
  #First, I add the right roots of unity to the field.
  xZx = ZZ["x"][2]
  phi = cyclotomic(r, xZx)
  lf = factor(phi, F)
  lF = collect(keys(lf.fac))
  ind = 1
  st = steinitz_number(lF[1])
  for i = 2:length(lF)
    st_i = steinitz_number(lF[i])
    if st_i < st
      st = st_i
      ind = i
    end
  end
  F0, gF0 = FiniteField(lF[ind], "a0", cached = false)
  f = degree(F0)
  Fn = _presentation_kummer(F0, r, n)
  #Now, I need to take the trace.
  p = characteristic(F)
  e = _find_exponent(f, p, fmpz(r), n)
  t = gen(Fn)
  g = gen(Fn)
  for i = 1:f-1
    g = g^e
    t = add!(t, t, g)
  end
  return FiniteField(_minpoly(t, r^n), "a", cached = false, check = false)[1]
end

function _find_exponent(f::Int, p::fmpz, r::fmpz, n::Int)
  xZx = ZZ["x"][2]
  phi = cyclotomic(f, xZx)
  R = ResidueRing(FlintZZ, r^(n+1), cached = false)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  phiR = Rx(phi)
  phiR1 = derivative(phiR)
  a = p
  it = max(clog(fmpz(n), 2)+1, 2)
  for i = 1:it
    ev1 = phiR(a)
    ev2 = phiR1(a)
    a = a - divexact(ev1, ev2)
  end
  return lift(a)
end