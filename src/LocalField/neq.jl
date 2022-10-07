#export: degree_relative, random_elem, one_root, norm_equation

degree(L::Hecke.LocalField, K::Union{FlintQadicField, Hecke.LocalField}) = divexact(absolute_degree(L), absolute_degree(K))

function degree(L::FinField, k::FinField)
  @assert characteristic(L) == characteristic(k)
  dL = absolute_degree(L)
  dk = absolute_degree(k)
  q, r = divrem(dL, dk)
  r == 0 && return q
  error("not a subfield")
end

##############################################
#random element with small coefficients
# BAD
##############################################

function random_elem(L::Union{FlintQadicField, Hecke.LocalField})
   b = basis(L)
   n = degree(L)
   r = [rand(1:5*n) for i in 1:n]   # Choose small coefficients
   return sum( [r[i]*b[i] for i in 1:n])
end


########### any_root computes a single root in the finite field extensions####

import Nemo:any_root
function any_root(f::Union{gfp_poly, fq_nmod_poly}, F::Union{FqNmodFiniteField, Hecke.RelFinField})
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f) ] )
   return any_root(g)
end

function roots(f::Union{gfp_poly, fq_nmod_poly}, F::Union{FqNmodFiniteField, Hecke.RelFinField})
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f) ] )
   return roots(g)
end

function any_root(f::Hecke.AbstractAlgebra.Generic.Poly, F::Hecke.RelFinField)
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f)])
   fac = factor(g)
   if length(fac) == 1
      error("no roots")
   end
   r = first(fac)[1]
   @assert degree(r) == 1
   return -coeff(r,0)
end

function trace_equation(F::Union{FlintQadicField, Hecke.LocalField}, a::Union{Hecke.LocalFieldElem, padic, qadic})
  A = random_elem(F)
  K = parent(a)
  while iszero(trace(A, K)) || valuation(trace(A, K)) > 0
    A = random_elem(F)
  end
  A = divexact(A, F(trace(A, K)))
  return A*F(a) #F(a) here and above due to missing promote rule
end

function norm_equation(F::Union{FlintQadicField, Hecke.LocalField{padic, Hecke.UnramifiedLocalField}}, a::padic)
  v = valuation(a)
  if v % degree(F) != 0
    error("no solution, wrong valuation")
  end
  a = divexact(a, prime(parent(a), v))
  k, mk = ResidueField(parent(a))
  K, mK = ResidueField(F)
  b = norm_equation(K, mk(a))
  T = preimage(mK, b)
  a = a//norm(T)
  #log forgets the finite field bit...
  la = log(a)
  lA = trace_equation(F, la)
  @assert trace(lA) == la
  A = exp(lA)*prime(parent(a))^divexact(v, degree(F))
  return A*T
end

######################### norm equation over finite fields ##############
@doc Markdown.doc"""
    norm_equation(F::Union{FqNmodFiniteField, Hecke.RelFinField}, b::Union{gfp_elem, fq_nmod})

Find an element `x` in `F` such that the norm from `F` down to the parent of
`b` is exactly `b`.
"""
function norm_equation(F::Union{FqNmodFiniteField, Hecke.RelFinField}, b::Union{gfp_elem, fq_nmod})
   if iszero(b)
      return zero(F)
   end
   k = parent(b)
   n = degree(F,k)
   f = polynomial(k,vcat([b],[rand(k) for i = 1:n-1],[1]))
   while !is_irreducible(f)
      f = polynomial(k,vcat([b],[rand(k) for i = 1:n-1],[1]))
   end
   return (-1)^(n)*any_root(f,F)
end

################ norm equation over local field extensions###########################

function norm_equation(R:: Hecke.LocalField, b::Union{qadic,Hecke.LocalFieldElem})
   K = parent(b)
   prec_b = precision(b)
   @assert base_field(R) == K  #"since trace(a,_) is not defined"
   f,mf = ResidueField(K)
   F,mF = ResidueField(R)
   ee = absolute_ramification_index(K)
   if degree(R) == ramification_index(R) && mf(b) !=f(1)
      error("To be implemented")
   end
   if mf(b) == f(1)
      f_nm = R(1)
   else
      f_nm = norm_equation(F,mf(b))
      f_nm = mF\(f_nm)
   end
   b = b//norm(f_nm)
   b = setprecision(b,prec_b)
   p = prime(R)
   if valuation(b-1) < ee//(p-1)+1//ee
      error("To be implemented or try norm_equation_unramified")
   end
   r = random_elem(R)
   while valuation(trace(r)) != 0 || valuation(r//R(trace(r))) != 0
      r = random_elem(R)
   end
   s = r*R(trace(r)^-1)*R(log(b))
   return exp(s)*f_nm
end

###########################################################################################################
#   The following "norm_equation_unramified" solves the norm equations only in unramified extensions
###########################################################################################################

function norm_equation_unramified(L::Hecke.LocalField, b::Hecke.LocalFieldElem)
   K = parent(b)
   @assert degree(L) == inertia_degree(L)
   prec_b = precision(b)
   piK = uniformizer(K)
   piL = uniformizer(L)
   f,mf = ResidueField(K)
   F,mF = ResidueField(L)
   ee = absolute_ramification_index(K)
   if mf(b) == f(1)
      f_nm = L(1)
   else
      f_nm = norm_equation(F,mf(b))
      f_nm = mF\(f_nm)
   end
   b = b//norm(f_nm)
   b = setprecision(b,prec_b)
   c = L(1)
   C = [L(1)]
   n = ee*valuation((b//norm(C[1]))-1)
   r = random_elem(L)
   while valuation(trace(r)) != 0 || valuation(r//L(trace(r))) != 0
      r = random_elem(L)
   end
   z = ((b//norm(c))-1)//piK^ZZ(n)
   setprecision!(z, prec_b)
   push!(C, 1+ piL^ZZ(n)* (L(z)*r//L(trace(r))))
   c = prod(C)
   nc = norm(c)
   n = ee*valuation((b//nc)-1)
   while prec_b >= n+1 #  "solve till precision n-1"
      z = ((b//nc)-1)*piK^-ZZ(n)
      setprecision!(z, prec_b)
      push!(C, 1+ piL^ZZ(n)*(L(z)*r//L(trace(r))))
      c = prod(C)
      setprecision!(c, precision(L))
      nc = norm(c)
      chk = (nc*b^-1)-1
      if iszero(chk) == true
         n = prec_b
      else
         n = ee*valuation((b//nc)-1)
      end
   end
   return c*f_nm
end
