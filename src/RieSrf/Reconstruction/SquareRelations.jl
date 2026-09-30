


function odd_theta_relations(g, thetas)
  A = aronhold_system(g, azygetic_system(g))
  A2 = aronhold_system(g, azygetic_system_flip(g))

  even_indices = char_to_index.(even_theta_characteristics(g))
  odd_indices = char_to_index.(odd_theta_characteristics(g))

  d = length(odd_indices)

  I = collect((1:d))

  M1 = theta_square_relations(g, thetas, A, I);
  M2 = theta_square_relations(g, thetas, A2, I);
  M = [M1 ; M2];

  M_even = M[:, even_indices];

  CC = parent(thetas[zeros(Int, 2*g)...])
  prec = precision(CC)
  setprecision(BigFloat, prec)
  #M_even_float = Complex{BigFloat}.(collect(M_even))
  M_even_float = Complex{Float64}.(collect(M_even));
  M_even_float = (x-> abs(x) < 10^(-50) ? zero(ComplexF64) : x).(M_even_float);
  K = permutedims(nullspace(transpose(M_even_float)));
  M_float = Complex{Float64}.(collect(M));
  O = K*(M_float[:,odd_indices])
  return O
end


function theta_square_relations(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem}) where N
  return theta_square_relations(g, thetas, collect(1:2^(2*g)))
end

function theta_square_relations(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem},a,  indices::Vector{Int}) where N
  @req g >= 4 "g needs to be bigger than 3."
  a = [GF(2).(av) for av in a]
  a0 = sum(a)


  l = Vector{FqFieldElem}[]
  for p in (1:g-3)
    push!(l, a[2*p+6] + a[2*p+7])
  end

  lambda = Vector{FqFieldElem}[]
  l_M = matrix(l)
  V = Iterators.product(repeat([[GF(2)(0),GF(2)(1)]], g-3)...)
  for v in V 
    v = [v...]
    push!(lambda, v * l_M)
  end

  A = Vector{FqFieldElem}[]

  for lam in lambda
    for ai in [[a0] ; a[1:7]]
      push!(A, lam+ai)
    end
  end

  L = sum(a[i] for i in (8:2:2*g))
  if mod(g, 2) == 1
    L += a0
  end

  CC = parent(thetas[zeros(Int, 2*g)...])
  R, X = polynomial_ring(CC, 2^(2*g))


  D = Dict([(collect(GF(2).(v)), thetas[v]) for v in keys(thetas)])

  theta_indices_temp = Hecke.theta_characteristics_indices(g)
  theta_indices = theta_indices_temp[2:end]
  push!(theta_indices, theta_indices_temp[1])

  Dv = Dict([(collect(GF(2).(theta_indices[i])), i) for i in (1:2^(2*g))])

  M = zero_matrix(CC, length(indices), 2^(2*g));

  for v in (1:length(indices))
    V = indices[v]
    sigma = GF(2).(collect(theta_indices[V]))

    factor = (-1)^(half_char_inner_prod(L, a[2*g]) + half_char_inner_prod(a[2*g], L) )
  
    for h in (1:2^(g-3)) 
      first_term = (-1)^(half_char_inner_prod(lambda[h], lambda[h]) 
      + half_char_inner_prod(L+lambda[h] +a0 + a[2*g], L + lambda[h] + a0 + a[2*g])+half_char_inner_prod(sigma, L + lambda[h])) * 
      D[L + lambda[h]]
      j = Dv[L + lambda[h] + sigma]
      M[v, j] += first_term *factor
    end

    for a_rho in [[a0] ; a[1:7]]
      for j in (1:2^(g-4))
        second_term = (-1)^((half_char_inner_prod(lambda[j] + a_rho, L)  + half_char_inner_prod(L, lambda[j] +a_rho) + half_char_inner_prod(sigma, L + lambda[j] + a_rho + a[2*g]))) *
        D[L + lambda[j] + a_rho + a[2*g]]
        t = Dv[ L + lambda[j] + a_rho + a[2*g] + sigma]
        M[v, t] -= second_term
      end
    end
  end
  return M
end

function _construct_sparse_matrix(g, thetas)
  CC = parent(thetas[zeros(Int, 2*g)...])
  rho = zeros(QQ, 2*g)

  N = 2^(2*g-1)

  M = zero_matrix(CC, N, 2^(2*g));
  V = Iterators.product(repeat([[QQ(0),QQ(1//2)]], 2*g)...)
  k = 1

  for v in V
    sigma = collect(v)
    SS = max_noether_relations(g, thetas, rho, sigma)
    R = parent(SS)
    X = gens(R)
    ts = terms(SS)
    for t in ts
      c = t.coeffs[1]
      e = findfirst(!iszero, exponent_vector(t, 1))[1]
      M[k, e] = c
    end
    if k == N
      break
    end
    k += 1 
    println(k)
  end
  return M
end
