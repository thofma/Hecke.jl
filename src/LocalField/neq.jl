#export: degree_relative, random_elem, one_root, norm_equation  


degree_relative(L::Hecke.LocalField, K::Union{FlintQadicField, Hecke.LocalField}) = Int(absolute_degree(L)//absolute_degree(K)
)

degree_relative(L::Hecke.RelFinField, K::Union{FqNmodFiniteField, Hecke.RelFinField}) = Int(absolute_degree(L)//absolute_degree(K))

degree_relative(L::FqNmodFiniteField, K::Hecke.Nemo.GaloisField) = Int(absolute_degree(L)//absolute_degree(K))


##############################################
#random element with small coefficients
##############################################

function random_elem(L::Union{FlintQadicField, Hecke.LocalField})
   b = basis(L)
   n = degree(L)
   r = [rand(1:5*n) for i in 1:n]   # Choose small coefficients
   return sum( [ r[i]*b[i] for i in 1:n])
end


################ one_root computes a single root in the finite field extensions#############################
function one_root(f::Union{gfp_poly, fq_nmod_poly}, F::Union{FqNmodFiniteField, Hecke.RelFinField})
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f) ] )
   fac = factor(g)
   if length(fac)  == 1 
      error("no roots") 
   end
   r = first(fac)[1] 
   @assert degree(r) == 1
   return -coeff(r,0)
end
 

function one_root(f::Hecke.AbstractAlgebra.Generic.Poly, F:: Hecke.RelFinField)
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f) ] )
   fac = factor(g)
   if length(fac)  == 1     
      error("no roots") 
   end
   r = first(fac)[1] 
   @assert degree(r) == 1
   return -coeff(r,0)
end

#########################################################################
# Alternative way of computing the norm due to some problem in resultant
#
##########################################################################

function norm_det(a)
   L = parent(a)
   m = matrix([[coeff(a*x, i-1) for i in 1:degree(L)] for x in basis(L)])
   return det(m)
end


######################### norm equation over finite fields ##############

function norm_equation(F::Union{FqNmodFiniteField, Hecke.RelFinField}, b::Union{gfp_elem, fq_nmod})
   k = parent(b)
   n = degree_relative(F,k)
   f = polynomial(k,vcat([b],[rand(k) for i = 1:n-1],[1] ) )
   while !isirreducible(f)
      f = polynomial(k,vcat([b],[rand(k) for i = 1:n-1],[1] ) )
   end
   return (-1)^(n)*one_root(f,F)
end

################ norm equation over local field extensions###########################

function norm_equation(R:: Hecke.LocalField, b::Union{qadic,Hecke.LocalFieldElem})
   K = parent(b)
   prec_b = precision(b)
   @assert base_field(R) == K  #"since trace(a,_) is not defined"
   f,mf = ResidueField(K);
   F,mF = ResidueField(R);
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
   b = b //norm_det((f_nm))
   b = setprecision(b,prec_b)
   p = prime(R)  
   if valuation(b-1) < ee//(p-1)+1//ee     
      error("To be implemented or try norm_equation_unramified")
   end
   r = random_elem(R);
   while valuation(trace(r)) != 0 ||  valuation(r // R(trace(r))) != 0
      r = random_elem(R);
   end
   s = r * R(trace(r)^-1) * R(log(b))   
   return exp(s)*f_nm
end
 
############### ############################################################################################
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
   b = b //norm_det((f_nm))
   b = setprecision(b,prec_b)
   c = L(1)
   C = [L(1)]
   n = ee*valuation((b //  norm_det(C[1]))-1)
   r = random_elem(L);
   while valuation(trace(r)) != 0 ||  valuation(r // L(trace(r))) != 0
      r = random_elem(L);
   end
   z = ((b // norm_det(c))-1) // piK^ZZ(n);
   push!(C, 1+ piL^ZZ(n)* (L(z)*r // L(trace(r))));
   c = prod(C)
   n = ee*valuation( (b// norm_det(c))-1);
   while prec_b >= n+2 #   == n 
      z = ((b // norm_det(c))-1) * piK^-ZZ(n);
      push!(C, 1+ piL^ZZ(n)* (L(z)*r // L(trace(r))));
      c = prod(C);
      chk = (norm_det(c) * b^-1)-1
      if iszero(chk) == true
         n = prec_b           
      else
         n = ee*valuation((b// norm_det(c))-1);
      end
   end
   return c*f_nm;
end

    





