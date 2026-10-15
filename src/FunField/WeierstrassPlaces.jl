
################################################################################
#
#  FunField/WeierstrassPlaces.jl: Weierstrass Places, Ramification Divisor 
#  and Gap Numbers
#
# References:
#
# [Hess02] F. Hess
# "An Algorithm for computing Weierstrass Points."
# Algorithmic Number Theory. ANTS 2002. 
# Lecture Notes in Computer Science, vol 2369.
#
################################################################################

#Algorithm 30 in [Hess02]
#Computes gap numbers and the ramification divisor. 
#If only_gaps is set to true. It does not continue on to compute
#the ramification divisor
function _gaps_and_ramification_divisor(D::Divisor, only_gaps::Bool)
  F = function_field(D)
  K = defining_constant_field(F)
  W = canonical_divisor(F)
  x = separating_element(F)
  dx = differential(F(x))
  
  W_D = W - D

  v = riemann_roch_space(W_D)
  n = length(v)

  if n == 0
    return Int[], trivial_divisor(F)
  end

  E = [0]
  eps = 0
  M = matrix(v)
  i = 1 
  G = Set{Int}()

  i += 1
  while i <= n 
    eps += 1
    bin_eg_neq_0 = false
    for g in G
      if K(binomial(eps, g)) != K(0)
        push!(G, eps)
        bin_eg_neq_0 = true
        break
      end 
    end
    if bin_eg_neq_0
      continue
    end

    v_new = [differentiation(w, eps) for w in v]
    M_new = [M  matrix(v_new)]
    if rank(M_new) > rank(M)
      M = M_new 
      push!(E, eps)
      i += 1
      continue
    else
      push!(G, eps)
      continue
    end
  end

  gaps = [e+1 for e in E]

  if only_gaps
    return gaps, trivial_divisor(F)
  end

  R = divisor(det(M)) + sum(E)*divisor(dx) + n*(W_D)
  
  return gaps, R
end

@doc raw"""
    gap_numbers(D::Divisor) -> Vector{Int}

Return the global gap numbers of D. 
"""
function gap_numbers(D::Divisor)
  gaps, _ = _gaps_and_ramification_divisor(D, true)
  return gaps
end

@doc raw"""
    gap_numbers(F::FunctionField) -> Vector{Int}

Return the global gap numbers of the function field F. 
"""
function gap_numbers(F::Generic.AbsSimpleFunctionField)
  return gap_numbers(trivial_divisor(F))
end

@doc raw"""
    ramification_divisor(D::Divisor) -> Divisor

Return the ramification divisor of D. 
"""
function ramification_divisor(D::Divisor)
  _, R = _gaps_and_ramification_divisor(D, false)
  return R
end

@doc raw"""
    ramification_divisor(F::FunctionField) -> Divisor

Return the ramification divisor of F. 
"""
function ramification_divisor(F::Generic.AbsSimpleFunctionField)
  return ramification_divisor(trivial_divisor(F))
end

@doc raw"""
    weierstrass_places(D::Divisor) -> Vector{}

Return the Weierstrass places of D. 
"""
function weierstrass_places(D::Divisor)
  return map(x-> x[1], support(ramification_divisor(D)))
end

@doc raw"""
    weierstrass_places(F::FunctionField) -> Vector{}

Return the Weierstrass places of F. 
"""
function weierstrass_places(F::Generic.AbsSimpleFunctionField)
  return weierstrass_places(trivial_divisor(F))
end

#Note: Differentiation, derivation, power representation, etc.
#currently take the separating element chosen on construction
#of the function field. In principle we could allow the user to 
#specify a separating element (this is what Magma does), but this
#would need some rewriting.


@doc raw"""
    differentiation(a::Generic.AbsSimpleFunctionFieldElem, j::Int) -> FunctionFieldElem

Return the jth differentiation of a with respect to the separating element x
of the function field in which a lives.
"""
function differentiation(a::Generic.AbsSimpleFunctionFieldElem, j::Int)
  F = parent(a)
  return derivation(a, j)//F(factorial(j))
end


#Algorithm 26 in [Hess02]
#Can probably be sped up by implementing Algorithm 28 and considering the 
#comments below the algorithm
function differentiation(a::Generic.AbsSimpleFunctionFieldElem{FqFieldElem, FqPolyRingElem}, j::Int)
  F = parent(a)
  p = Int(characteristic(F))
  x = separating_element(F)
  if j == 0
    return a
  end
  r, s = divrem(j, p)
  e = derivation(a, s)//F(factorial(s))
  if r == 0
    return e
  else
    lambda = power_representation(e)
    mu = []
    for i in (1:length(lambda))
      push!(mu, differentiation(lambda[i], r))
    end
    return sum([mu[i+1]^p*x^i for i in (0:p-1)])
  end
end

@doc raw"""
    power_representation(a0::Generic.AbsSimpleFunctionFieldElem{FqFieldElem, FqPolyRingElem}) -> FunctionFieldElem

Return the coefficients of the representation of a0 as a sum of powers of x 
Here x is the separating element of the function field in which a lives.
"""
#Algorithm 25 in [Hess02]
function power_representation(a0::Generic.AbsSimpleFunctionFieldElem{FqFieldElem, FqPolyRingElem})
  F = parent(a0)
  p = Int(characteristic(F))
  a = zero_matrix(F, p, 1)
  x = separating_element(F)
  a[1] = a0
  for j in (1:p-1)
    a[j+1] = derivation(a[j])//F(j)
  end
  b = zero_matrix(F, p, 1)
  b[p] = a[p]
  for j in (p - 1:-1:1)
    b[j] = a[j] - sum([b[i] * binomial(i-1, j-1) *x^(i - j) for i in (j:p)])
  end
  return [pth_root(B) for B in b]
end

#Compute the pth root of an element of a function field in characteristic p.
#Use that b -> a:=b^p is Fp-linear.
function Hecke.pth_root(a::Generic.AbsSimpleFunctionFieldElem{FqFieldElem, FqPolyRingElem})
  F = parent(a)
  p = characteristic(F)
  n = degree(F)
  kx = base_ring(F)

  #M maps pth powers of coordinates of b to coordinates of b^p s.th.
  #a = b^p = coordinates(b).^p * M * basis(F).
  #For repeated use: set_attribute!(F, :power_matrix_ctx, solve_init(M)).
  if has_attribute(F, :power_matrix_ctx)
    M = get_attribute(F, :power_matrix_ctx)
  else
    M = solve_init(matrix(base_ring(F), [coordinates(b^p) for b in basis(F)]))
    set_attribute!(F, :power_matrix_ctx, M)
  end

  coord = solve(M, coordinates(a))
  for i in 1:n
    c = coord[i]

    #Compute pth root of num and den in polynomial ring.
    c_num = numerator(c)
    #Compute pth root of variable powers and coefficients in Fq.
    c_num = map_coefficients(pth_root, deflate(c_num, p.d))

    c_den = denominator(c)
    #Compute pth root of variable powers and coefficients in Fq.
    c_den = map_coefficients(pth_root, deflate(c_den, p.d))

    #Put together to coordinate of b.
    coord[i] = kx(c_num, c_den)
  end
  b = F(coord)
  #Check if we have an actual pth root. 
  #(I.e. all terms of the form x^n had p divide n.)
  if (b)^p == a
    return b
  else
    error("Element does not have a pth root.")
  end
end
