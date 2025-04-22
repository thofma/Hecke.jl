###############################################################################
#
#  Descent methods for rank computations and local solubility of quartics
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

###############################################################################
#
#  Quartic local solubility
#
###############################################################################

#TODO: Extend this to hyperelliptic curves
#TODO: Do this over number fields

@doc raw"""
    quartic_local_solubility(a::QQFieldElem, b::QQFieldElem, c::QQFieldElem, d::QQFieldElem, e::QQFieldElem) -> Bool

Check if the quartic defined by ax^4+bx^3+cx^2+dx+e is soluble over the real field $\mathbb{R}$ and over all local fields $\mathbb{Q}_p$.
"""
function quartic_local_solubility(a, b, c, d, e)

  if !R_soluble(a,b,c,d,e)
    return false
  end

  if !Qp_soluble(a,b,c,d,e,2)
    return false
  end

  R, x = polynomial_ring(QQ)

  delta = discriminant(a*x^4 + b*x^3 + c*x^2 +d*x + e)

  fac = factor(numerator(delta))
  p_list = [i[1] for i in fac]
  p_list = sort(p_list)

  for p in p_list
    if !Qp_soluble(a,b,c,d,e,p)
      return false
    end
  end

  return true
end

@doc raw"""
    R_soluble(a::QQFieldElem, b::QQFieldElem, c::QQFieldElem, d::QQFieldElem, e::QQFieldElem) -> Bool

Check if the quartic defined by $ax^4+bx^3+cx^2+dx+e$ has a solution over $\mathbb{R}$.
"""
function R_soluble(a, b, c, d, e)
  if a>0
    return true
  end

  R,x = polynomial_ring(ZZ,"x")

  return signature(a*x^4+b*x^3+c*x^2+d*x+e)[1]>0
end

@doc raw"""
    Qp_soluble(a::QQFieldElem, b::QQFieldElem, c::QQFieldElem, d::QQFieldElem, e::QQFieldElem,
    p::ZZRingElem) -> Bool

Check if the quartic defined by $ax^4+bx^3+cx^2+dx+e$ has a solution over the local field $\mathbb{Q}_p$.
"""
function Qp_soluble(a, b, c, d, e, p)
  R,x = polynomial_ring(QQ,"x")
  if Zp_soluble(a,b,c,d,e,0,p,0)
    return true
  end

  if Zp_soluble(e,d,c,b,a,0,p,1)
    return true
  end
  return false
end


function Zp_soluble(a,b,c,d,e,x_k,p,k)
  if p == 2
    code = lemma7(a,b,c,d,e,x_k,k)
  else
    code = lemma6(a,b,c,d,e,x_k,p,k)
  end

  if code == 1
    return true
  end
  if code == -1
    return false
  end

  for t in (0:p-1)
    if Zp_soluble(a,b,c,d,e,x_k+t*p^k,p,k+1)
      return true
    end
  end

  return false
end

#Z_p lifting subroutine for odd p. Lemma 6 from Cremona Chapter 3, page 82.
#For generalization to number fields, see Appendix of Siksek's thesis

function lemma6(a,b,c,d,e,x,p,n)
  gx = a*x^4+b*x^3+c*x^2+d*x+e

  if(gx == 0)
    return 1
  end

  # Test if square in Zp
  l = valuation(gx,p)
  if iseven(l)
    if jacobi_symbol(numerator(gx//(p^l)),p)==1
      return 1
    end
  end

  gdx = 4*a*x^3+3*b*x^2+2*c*x+d

  if(gdx == 0)
   return 1
  end

  m = valuation(gdx,p)
  if (l>=m+n) && (n>m)
    return 1
  end
  if (l>=2*n) && (m>=n)
    return 0
  end
  return -1
end

#Z_p lifting subroutine for p=2. Lemma 7 from Cremona Chapter 3, page 82.
#For generalization to number fields, see Appendix of Siksek's thesis
function lemma7(a,b,c,d,e,x,n)
  gx = a*x^4+b*x^3+c*x^2+d*x+e
  # Test if square in Z2
  if(gx == 0)
    return 1
  end

  l = valuation(gx,2)
  if divides(l,2)[1]
    if (mod(ZZRingElem(numerator(gx//(2^l))),8) == 1)
      return 1
    end
  end


  gdx = 4*a*x^3+3*b*x^2+2*c*x+d

  # In this case the valuation of gdx is -infinity
  if(gdx == 0)
   return 1
  end

  m = valuation(gdx,2)
  gxodd = ZZRingElem(numerator(gx//(2^l)))

  gxodd = mod(gxodd,4)

  if (l>=(m+n)) && (n>m)
    return 1
  end
  if (n>m) && (l==(m+n-1)) && iseven(l)
    return 1
  end
  if (n>m) && (l==(m+n-2)) && (gxodd==1) && iseven(l)
    return 1
  end
  if (m>=n) && (l>=2*n)
    return 0
  end
  if (m>=n) && (l==(2*n-2)) && (gxodd==1)
    return 0
  end

  return -1

end


#TODO: Make sieve-assisted
@doc raw"""
    quartic_rational_point_search(a::QQFieldElem, b::QQFieldElem, c::QQFieldElem, d::QQFieldElem, e::QQFieldElem,
    lower_bound::Int, upper_bound::Int) -> Bool

Check if the quartic defined by $ax^4+bx^3+cx^2+dx+e$ has a rational point $u/w$
where $\gcd(u,w) = 1$ with lower_bound <= u+w <= upper_bound.
"""
function quartic_rational_point_search(a, b, c, d, e, lower_bound, upper_bound, tmp1 = ZZ(), tmp2 = ZZ())
  R = Globals.Qx
  for n in lower_bound:upper_bound
    if n==1
      if AbstractAlgebra.is_square(a)
        return true
      end
      if AbstractAlgebra.is_square(e)
        return true
      end
    else
      @assert nbits(n) <= 14 # otherwise u^4 will overflow
      for u in (1:n-1)
        if gcd(u,n)==1
          w = n-u
          u2 = u^2
          u3 = u*u2
          u4 = (u2)^2
          w2 = w^2
          w3 = w*w2
          w4 = (w2)^2
          u3w = u3 * w
          u2w2 = u2 * w2
          uw3 = u * w3
          mul!(tmp1, a, u4)
          add!(tmp1, tmp1, b * u3w)
          mul!(tmp2, c, u2w2)
          add!(tmp1, tmp1, tmp2)
          add!(tmp1, tmp1, d * uw3)
          mul!(tmp2, e, w4)
          add!(tmp1, tmp1, tmp2)
          # we have tmp1 == a*u^4+b*u^3*w+c*u^2*w^2+d*u*w^3+e*w^4
          if AbstractAlgebra.is_square(tmp1)
            return true
          end
          add!(tmp1, tmp1, - 2 * b * u3w)
          add!(tmp1, tmp1, - 2 * d * uw3)
          # now tmp1 == a*u^4-b*u^3*w+c*u^2*w^2-d*u*w^3+e*w^4
          if AbstractAlgebra.is_square(tmp1)
            return true
          end
        end
      end
    end
  end
  return false
end

###############################################################################
#
#  Descent via 2-torsion
#
###############################################################################

# Following Cremona p. 87
@doc raw"""
    rank_2_torsion(E::EllipticCurve, lim1::Int, lim2::Int) -> Int, Int, Int, Int

Compute bounds on rank and Sha using descent by 2-torsion isogeny.

lim1 gives a bound on the initial rational point search, lim2 a bound on
the exhaustive rational bound search in case of local solubility
The output consists of:
r_min: lower bound on the rank
r_max: upper bound on the rank
S: upper bound on #III(E)[phi]
S': upper bound on #III(E')[phi']

Here phi: E -> E' is an isogeny defined by a rational 2-torsion point on E
and phi' is its dual isogeny.
"""
function rank_2_torsion(E::EllipticCurve, lim1=100, lim2 = 1000)
  a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))
  if (a1==a3==0)
    s2 = a2
    s4 = a4
    s6 = a6
  else
    s2 = a1^2+4*a2
    s4 = 8*(a1*a3+2*a4)
    s6 = 16*(a3^2+4*a6)
  end

  R,x = polynomial_ring(QQ,"x")
  list = roots(x^3+s2*x^2+s4*x+s6)

  if all(!is_integral, list)
    throw(DomainError(E, "No rational 2-torsion"))
  end

  x0 = numerator(list[findfirst(is_integral, list)])

  c = 3*x0+s2
  d = (c+s2)*x0+s4
  _c = -2*c
  _d = c^2-4*d

  if iszero(d*_d)
    throw(DomainError(E, "Curve is singular"))
  end

  p_list = [p for (p,e) in factor(2*d*_d)]
  #print(p_list)
  n1,n2 = count_global_local(c,d,p_list,lim1,lim2)
  _n1,_n2 = count_global_local(_c,_d,p_list,lim1,lim2)

  e1 = log(2,n1)
  e2 = log(2,n2)
  _e1 = log(2,_n1)
  _e2 = log(2,_n2)

  r_min = Int(e1+_e1-2)
  r_max = Int(e2+_e2-2)
  S = Int(_n2//_n1)
  _S = Int(n2//n1)

  return r_min,r_max,S,_S
end

#TODO: Do better bookkeeping for divisors

function count_global_local(c, d, p_list, lim1, lim2)
  n1 = n2 = 1
  _d = c^2-4*d
  #print(d)
  d1_list = _squarefree_divisors(d)
  #print(d1_list)
  length(d1_list)
  tmp1 = ZZ()
  tmp2 = ZZ()
  for d1 in d1_list
    if quartic_rational_point_search(d1, 0, c, 0, divexact(d, d1), 1, lim1, tmp1, tmp2)
      #println(d1)
      n1 = n1+1
      n2 = n2+1
    else
      if everywhere_locally_soluble(c, d, _d, d1, p_list)
        #println(d1)
        n2 = n2+1
        if quartic_rational_point_search(d1, 0, c, 0, divexact(d, d1), lim1+1, lim2, tmp1, tmp2)
          n1 = n1+1
        end
      end
    end
  end
  return n1,n2
end

function everywhere_locally_soluble(c, d, _d, d1, p_list)
  if _d < 0 && d1 < 0
    return false
  end
  if _d > 0 && d1<0
    if isqrt(_d) < -c
      return false
    end
  end
  for p in p_list
    if !(Qp_soluble(d1, 0, c, 0, divexact(d, d1), p))
      return false
    end
  end
  return true
end


###############################################################################
#
#  Miscellaneous
#
###############################################################################

function _squarefree_divisors(n)
  divs = divisors(n)
  return filter(_issquarefree2, append!(-divs, divs))
end

function _issquarefree2(n)
  if (n==1)
    return false
  end
  return AbstractAlgebra.is_squarefree(n)
end
