
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
function _gaps_and_ramification_divisor(D::Divisor, only_gaps::Bool)
  F = function_field(D)
  K = constant_field(F)
  W = canonical_divisor(F)
  x = separating_element(F)
  dx = differential(F(x))
  d = dimension(W)
  
  if d == 0
    return Divisors[]
  end

  v = riemann_roch_space(W - D)
  n = length(v)
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
    return gaps, W
  end

  R = divisor(det(M)) + sum(E)*divisor(dx) + n*(W - D)
  
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



@doc raw"""
    differentiation(a::Generic.AbsSimpleFunctionFieldElem, j::Int) -> FunctionFieldElem

Return the jth differentiation of a with respect to the separating element x
of the function field in which a lives.
"""
function differentiation(a::Generic.AbsSimpleFunctionFieldElem, j::Int)
  return derivation(a, j)
end


#Algorithm 26 in [Hess02]
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
  a = zeros(F, p)
  x = separating_element(F)
  a[1] = a0
  for j in (1:p-1)
    a[j+1] = derivation(a[j])//F(j)
  end
  b = zeros(F, p)
  b[p] = a[p]
  for j in (p - 1:-1:1)
    b[j] = a[j] - sum([b[i] * binomial(i-1, j-1) *x^(i - j) for i in (j:p)])
  end
  return [pth_root(B) for B in b]
end

#Compute the pth root of an element of a function field in characteristic p.
function pth_root(a::Generic.AbsSimpleFunctionFieldElem{FqFieldElem, FqPolyRingElem})
  K = parent(a)
  y = gen(K)
  p = Int(characteristic(K))
  Ft = base_field(K)
  t = gen(Ft)
  n = degree(K)

  Mp = transpose(matrix([[coeff(y^(i * p),j) for j in (0:n-1)] for i in (0:n-1)]))
  v = matrix([coeff(a,j) for j in (0:n-1)])

  fnum_pth_root = solve(Mp, v, side = :right)
  R = parent(numerator(a))
  S = parent(denominator(a))

  for v in (1:length(fnum_pth_root))
    v_num = numerator(fnum_pth_root[v])
    coeffs_v_num = [pth_root(coeff(v_num, i)) for i in (0:p:degree(v_num))]
    v_den = denominator(fnum_pth_root[v])
    coeffs_v_den = [pth_root(coeff(v_den, i)) for i in (0:p:degree(v_den))]
    fnum_pth_root[v] = R(coeffs_v_num)(t)//S(coeffs_v_den)(t)
  end
  p_th_root = sum([fnum_pth_root[v+1]*y^v for v in (0:n-1)])
  if (p_th_root)^p == a 
    return p_th_root
  else
    error("Element does not have a pth root.")
  end
end
