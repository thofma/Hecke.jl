
@doc raw"""
    transformation_GLn(Gamma::MPolyRingElem{T}, P::MatElem{S}) -> MPolyRingElem

Given a n-ary form Gamma and an nxn matrix P in GL(n), apply the transformation P to Gamma. 
"""
function transformation_GLn(Gamma::MPolyRingElem{T}, P::MatElem{S}) where {T, S} 
  # Given a n-ary form Gamma and an nxn matrix P, apply the transformation P to Gamma. 
  K = base_ring(P)
  Gamma = change_base_ring(K, Gamma)
  RX = parent(Gamma)
  X = gens(RX)
  v = Vector(X)
  vX = collect(P * v)
  return Gamma(vX...)
end

@doc raw"""
    transvectant(f::MPolyRingElem{T}, g::MPolyRingElem{T}, k::Int) -> MPolyRingElem

Compute the transvectant (f, g)_k.
"""
function transvectant(f::MPolyRingElem{T}, g::MPolyRingElem{T}, k::Int) where T
  Kxy = parent(f)
  K = base_ring(Kxy)
  x, y = gens(Kxy)
  n = max(total_degree(f),k)
  m = max(total_degree(g),k)
  c = K(factorial(m-k) * factorial(n-k)) // K((factorial(m) * factorial(n)))

  Omega, (dfx, dfy, dgx, dgy) = polynomial_ring(K, ["dfx", "dfy", "dgx", "dgy"])
  diff_op = c * (dfx * dgy - dfy * dgx)^k

  result = Kxy(0)
  for mon in monomials(diff_op)
    dfxy_part = derivative(derivative(f, x, degree(mon, dfx)), y, degree(mon, dfy))
    dgxy_part = derivative(derivative(g, x, degree(mon, dgx)), y, degree(mon, dgy))

    result += coeff(diff_op,mon) * dfxy_part * dgxy_part
  end
  return result
end

function transvectant(f::MPolyRingElem{T}, g::MPolyRingElem{T}, r::Int, s::Int, invariant::Bool = false) where T
  R = parent(f)
  x, y, z, w = gens(R)

  if f*g == 0
    return R(0) 
  end

  R0, (X,Y) = polynomial_ring(R, 2)
  #Might need to check for homogeneous in weighted projective space
  @req is_homogeneous(f(x, y, X, Y)) && is_homogeneous(f(X, Y, z, w)) && is_homogeneous(g(x, y, X, Y)) && is_homogeneous(g(X, Y, z, w)) "f and g must be bihomogeneous"

  Sf = [[derivative(derivative(derivative(derivative(f, x, j), y, r-j), z, i), w, s-i) for j in (0:r)] for i in (0:s)]
  Sg = [[derivative(derivative(derivative(derivative(g, x, j), y, r-j), z, i), w, s-i) for j in (0:r)] for i in (0:s)]
  Tfg = R(0)

  for i in (0:s)
    for j in (0:r)
      Tfg += (-1)^(i+j)*binomial(s, i)*binomial(r, j)*(Sf[i+1][j+1]*Sg[s+1-i][r+1-j])
    end
  end

  if invariant
    return Tfg(0,0,0,0)
  else
    return Tfg
  end
end

function transvectant_sequence(Fs::Vector{S}, k::Int) where S <: Union{ZZMPolyRingElem, MPolyRingElem}
  R = parent(Fs[1])
  K = base_ring(R)
  n = number_of_generators(R)
  @req n == length(Fs) "Number of Fs needs to be equal to the number of variables."
  RX, X = polynomial_ring(K, n^2)
  M = matrix(RX, n, n, X)
  symbolic_transvectant = det(M)
  results = MPolyRingElem[]
  F_prod = prod([Fs[i](X[n*i-n+1:n*i]...) for i in (1:n)])
  F, Y = polynomial_ring(K, n)
  nY = repeat(Y, n)
  for j in (1:k)
    result = zero(RX)
    for term in terms(symbolic_transvectant)
      c = coeff(term, 1)
      E = exponent_vector(term,1)
      result_term = c*derivative(F_prod, E)
      result += result_term
    end
    F_prod = result
    push!(results, F_prod(nY...))
  end
  return results
end
