#=
using Hecke.RiemannSurfaces
using GenericLinearAlgebra
R, (x,y) = polynomial_ring(QQ, [:x,:y])
f = 2*x^5*y^3 + 5*x^4*y^3 - 9*x^4*y^2 + 3*x^3*y - 4*x^2*y^2 - 3*x*y^3 + 1
@time RS = riemann_surface(f, 200, integration_method = "heuristic")
g = genus(RS)
tau = small_period_matrix(RS)
CC = complex_field(RS)
z = zeros(CC, g)
@time thetas = Hecke.thetas(z, tau)

thetas_prym = prym_thetas(g, thetas)
fixed_thetas, non_fixed_thetas = find_fixed_even_chars(g-1)
terms = find_zero_sum_tetrads(fixed_thetas)

N = length(terms)
M = zero_matrix(GF(2), 4*N,  2^(2*(g-1)));
b = zero_matrix(GF(2), 4*N, 1);
for i in (1:4:4*N)
  test, rel = relation_with_term(g-1, thetas_prym, terms[div(i+3, 4)])
  if !test
    continue
  end
  c = rel[1][2]
  for k in (0:3)
    mon, coeff = rel[k + 1]
    b[i + k,1] = GF(2)(div(c*coeff-1,2))
    for j in mon
      M[i + k, j] = GF(2)(1)
    end
  end
end

Mbr = M[:,char_to_index.(non_fixed_thetas)];

v =  solve(Mbr, b, side = :right)

for j in (1:length(v))
  thetas_prym[non_fixed_thetas[j]...] *= ZZ(-1)^(lift(ZZ,v[j]))
end

for i in (1:N)
  println(relation_with_term(g-1, thetas_prym, terms[i], identity_matrix(GF(2), 2*(g-1))))
end


#z0 = CC.([1.4,0,3.3,1//2,1])
#@time thetas5_z0 = Hecke.thetas(z0, tau)
#Th_sq = map(x->x^2, theta_list(thetas5_z0, 5))


A = aronhold_system(g, azygetic_system(g));
A2 = aronhold_system(g, azygetic_system_flip(g));

even_indices = char_to_index.(even_theta_characteristics(g));
odd_indices = char_to_index.(odd_theta_characteristics(g));

I = collect(1:length(odd_indices));
I = collect(1:2^(2*g-1));

@time M1 = theta_square_relations(g, thetas, A, I);
@time M2 = theta_square_relations(g, thetas, A2, I);
M = [M1 ; M2];

M_even = M[:, even_indices];

#CC = parent(thetas[zeros(Int, 2*g)...])
#prec = precision(CC)
#setprecision(BigFloat, prec)
M_even_float = Complex{Float64}.(collect(M_even));
M_even_float = (x-> abs(x) < 10^(-50) ? zero(ComplexF64) : x).(M_even_float);
@time K = permutedims(nullspace(transpose(M_even_float)));
M_float = Complex{Float64}.(collect(M));
@time O = K*(M_float[:,odd_indices]);
@time rank(O)

#Sanity check:
#P = M * Th_sq;
#length(filter( x -> abs(x) > 10^(-30), P)) == 0


z0 = CC.([1.4,3.3,1//2,1])
@time thetas4_z0 = Hecke.thetas(z0, tau)
Th_sq = map(x->x^2, theta_list(thetas4_z0, 4))
P = M * Th_sq;
length(filter( x -> abs(x) > 10^(-30), P)) == 0


b = A[1:4]
B = sum(b)
A2 = [b;[B + v for v in A[5:end] ]]

g4_theta_sq = prym_thetas_sq(5, thetas)

rho = QQ.([1,1, 0,0,0,0,1,0,0,1])//2
sigma = [0,QQ(1//2),0,0,0,0,0,0,QQ(1//2),0]
SS = max_noether_relations(5, thetas5, rho, sigma)

v = [derivative(SS, i) for i in odd_indices]
Th = theta_list(thetas5, 5)
w = (x -> x(Th...)).(v)
filter( x -> x != zero(parent(x)), w)


=#

#Use bits for speed.
function bitmask(v::Vector{Int})
  m = zero(UInt128)
  for (i, x) in enumerate(v)
      iszero(x) || (m |= (UInt128(1) << (i - 1)))
  end
  return m
end

#Computes squares of the thetas of the Prym. 
function prym_thetas_sq(g::Int, thetas)
  g_min_thetas = Dict{NTuple{2*(g-1), Int64}, AcbFieldElem}()
  chars_even = even_theta_characteristics(g-1)
  for char in chars_even
    delta_new1 = (0, char[1:g-1]..., 0, char[g:2*(g-1)]...)
    delta_new2 = (0, char[1:g-1]..., 1, char[g:2*(g-1)]...)
    #Formula from Lemma 1 (p. 148) of Farkas
    g_min_thetas[char] = thetas[delta_new1]*thetas[delta_new2]
  end

  return g_min_thetas
end

function prym_thetas(g::Int, thetas)
  g_min_thetas = Dict{NTuple{2*(g-1), Int64}, AcbFieldElem}()
  chars_even = even_theta_characteristics(g-1)
  for char in chars_even
    delta_new1 = (0, char[1:g-1]..., 0, char[g:2*(g-1)]...)
    delta_new2 = (0, char[1:g-1]..., 1, char[g:2*(g-1)]...)
    #Formula from Lemma 1 (p. 148) of Farkas
    g_min_thetas[char] = sqrt(thetas[delta_new1]*thetas[delta_new2])
  end
  chars_odd = odd_theta_characteristics(g-1)
  CC = parent(thetas[zeros(Int, 2*g)...])
  for char in chars_odd 
    g_min_thetas[char] = CC(0)
  end
  return g_min_thetas
end

function azygetic_system(g::Int)
  zer = zero_matrix(GF(2), g, g)
  zer1 = zero_matrix(GF(2), g, 1)
	zer2 = zero_matrix(GF(2), g, 2)
	id = identity_matrix(GF(2), g)
	triang = zer
	for i in (1:g)
		for j in (i:g)
			triang[i,j] = 1
		end
	end

	odd_chars = [id; triang]
	even_chars = [[id zer2] ; [zer1 triang zer1]]

  return [odd_chars even_chars]
end

function aronhold_system(g::Int, M)
  a = aronhold_system(g)
  apply_transformation_to_char.(Ref(M), a)
end

function aronhold_system(g::Int)
  azy_set = azygetic_system(g)
  zer = zero_matrix(GF(2), g, g)
	id = identity_matrix(GF(2), g)
	J = [zer id; id zer]
  J1 = [zer id; zer zer]

  w = diagonal(transpose(azy_set) * J1 * azy_set)

  for i in (1:2*g+2)
    e = zeros(GF(2),2*g+2)
    e[i] += g
    test, sol = can_solve_with_solution(J*azy_set, w+e)
    if test
      return [t + sol for t in [transpose(azy_set)[j,:] for j in (1:ncols(azy_set))][(1:end) .!= i]]
    end
  end
  error("Error in computation of aronhold system.")

end

function max_noether_data(g::Int, M)
  a = aronhold_system(g, M)
  a = [QQ.(lift.(Ref(ZZ), av))/2 for av in a]
  a0 = sum(a)


  l = Vector{QQFieldElem}[]
  for p in (1:g-3)
    push!(l, a[2*p+6] + a[2*p+7])
  end

  lambda = Vector{QQFieldElem}[]
  l_M = matrix(l)
  V = Iterators.product(repeat([[QQ(0),QQ(1)]], g-3)...)
  for v in V 
    v = [v...]
    push!(lambda, v * l_M)
  end

  A = Vector{QQFieldElem}[]

  for lam in lambda
    for ai in [[a0] ; a[1:7]]
      push!(A, lam+ai)
    end
  end

  L = sum(a[i] for i in (8:2:2*g))
  if mod(g, 2) == 1
    L += a0
  end
  return L, lambda, [[a0] ; a[1:7]], a[2*g]
end

function max_noether_characteristics(g::Int)
  L, lambda, A_rho, a2g = max_noether_data(g, identity_matrix(GF(2), 2*g))

  chars = []

  for h in (1:2^(g-3)) 
    v = L + lambda[h]
    push!(chars, v)
  end

  for a_rho in A_rho
    for j in (1:2^(g-4))
      v = L + lambda[j] + a_rho + a2g
      push!(chars, v)
    end
  end

  return chars
end


function max_noether_relations(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem}, rho::Vector{QQFieldElem}, sigma::Vector{QQFieldElem}) where N
  @req g >= 4 "g needs to be bigger than 3."
  L, lambda, A_rho, a2g = compute_max_noether_characteristics(g::Int)

  CC = parent(thetas[zeros(Int, 2*g)...])
  R, X = polynomial_ring(CC, 2^(2*g))


  D = thetas

  theta_indices = Hecke.theta_characteristics_indices(g)
  Dv = Dict([(theta_indices[i+1], X[i]) for i in (1:2^(2*g)-1)])
  Dv[zeros(Int, 2*g)...] = X[2^(2*g)]

  first_term = R(0)

  factor = (-1)^(half_char_inner_prod(L, a2g) + half_char_inner_prod(a2g, L) )
 
  for h in (1:2^(g-3)) 
    first_term += (-1)^(half_char_inner_prod(lambda[h], lambda[h]) + 
    half_char_inner_prod(L+lambda[h] +a[1] + a2g, L + lambda[h] + a[1] + a2g)+half_char_inner_prod(rho+sigma, L + lambda[h])) * 
    mod(half_char_inner_prod(L + lambda[h] + rho) - 1, 2) *
    theta_HI(D, L + lambda[h]) * theta_HI(D, L + lambda[h] + rho) *
    theta_HI(Dv, L + lambda[h] + sigma) * theta_HI(Dv, L + lambda[h] + rho + sigma)

  end

  first_term *= factor

  second_term = 0
  for a_rho in A_rho
    for j in (1:2^(g-4))
      second_term += (-1)^((half_char_inner_prod(lambda[j] + a_rho, L)  + half_char_inner_prod(L, lambda[j] +a_rho) + half_char_inner_prod(rho + sigma, L + lambda[j] + a_rho + a2g))) *
      mod(half_char_inner_prod(L + lambda[j] + a_rho + a2g + rho) - 1, 2) * 
      theta_HI(D, L + lambda[j] + a_rho + a2g) * theta_HI(D, L + lambda[j] + a_rho + a2g + rho) *
      theta_HI(Dv, L + lambda[j] + a_rho + a2g + sigma) * theta_HI(Dv, L + lambda[j] + a_rho + a2g + rho + sigma)
    end
  end

  return first_term - second_term
end


function frobenius_fay_relation(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem}, rho::Vector{FqFieldElem}, sigma::Vector{FqFieldElem}) where N
  rho_Q = QQ.(lift.(Ref(ZZ), rho))/2
  sigma_Q = QQ.(lift.(Ref(ZZ), sigma))/2
  return frobenius_fay_relation(g, thetas, rho_Q, sigma_Q)
end
  

function frobenius_fay_relation(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem}, rho::Vector{QQFieldElem}, sigma::Vector{QQFieldElem}) where N
  @req g >= 4 "g needs to be bigger than 3."
  @req mod(half_char_inner_prod(rho, sigma) + half_char_inner_prod(sigma, rho), 2) == 1 "Rho and sigma must not be orthogonal."
  a = aronhold_system(g)
  a = [QQ.(lift.(Ref(ZZ), av))/2 for av in a]
  a0 = sum(a)


  l = Vector{QQFieldElem}[]
  for p in (1:g-3)
    push!(l, a[2*p+6] + a[2*p+7])
  end

  lambda = Vector{QQFieldElem}[]
  l_M = matrix(l)
  V = Iterators.product(repeat([[QQ(0),QQ(1)]], g-3)...)
  for v in V 
    v = [v...]
    push!(lambda, v * l_M)
  end

  A = Vector{QQFieldElem}[]

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

  D = thetas

  theta_indices = Hecke.theta_characteristics_indices(g)
  result = zeros(CC, 2^(2*g))


  factor = (-1)^(half_char_inner_prod(L, a[2*g]) + half_char_inner_prod(a[2*g], L) )
 
  for h in (1:2^(g-3)) 
 
    v = L + lambda[h] + sigma
    if mod(half_char_inner_prod(v), 2) == 1
      result[char_to_index(v)] += (-1)^(half_char_inner_prod(lambda[h], lambda[h]) + 
      half_char_inner_prod(L+lambda[h] +a0 + a[2*g], L + lambda[h] + a0 + a[2*g])+half_char_inner_prod(rho+sigma, L + lambda[h])) * 
      mod(half_char_inner_prod(L + lambda[h] + rho) - 1, 2) *
      theta_HI(D, L + lambda[h]) * theta_HI(D, L + lambda[h] + rho) *
      _sign_flip(v) * theta_HI(D, v + rho) * factor
    else 
      result[char_to_index(v + rho)] += (-1)^(half_char_inner_prod(lambda[h], lambda[h]) + 
      half_char_inner_prod(L+lambda[h] +a0 + a[2*g], L + lambda[h] + a0 + a[2*g])+half_char_inner_prod(rho+sigma, L + lambda[h])) * 
      mod(half_char_inner_prod(L + lambda[h] + rho) - 1, 2) *
      theta_HI(D, L + lambda[h]) * theta_HI(D, L + lambda[h] + rho) *
      _sign_flip(v + rho) * theta_HI(D, v) * factor
    end

  end

  for a_rho in [[a0] ; a[1:7]]
    for j in (1:2^(g-4))
      v = L + lambda[j] + a_rho + a[2*g] + sigma
      if mod(half_char_inner_prod(v), 2) == 1
        result[char_to_index(v)] -= (-1)^((half_char_inner_prod(lambda[j] + a_rho, L)  + half_char_inner_prod(L, lambda[j] +a_rho) + half_char_inner_prod(rho + sigma, L + lambda[j] + a_rho + a[2*g]))) *
        mod(half_char_inner_prod(L + lambda[j] + a_rho + a[2*g] + rho) - 1, 2) * 
        theta_HI(D, L + lambda[j] + a_rho + a[2*g]) * theta_HI(D, L + lambda[j] + a_rho + a[2*g] + rho) *
       _sign_flip(v) * theta_HI(D, v + rho)
      else 
        result[char_to_index(v + rho)] -= (-1)^((half_char_inner_prod(lambda[j] + a_rho, L)  + half_char_inner_prod(L, lambda[j] +a_rho) + half_char_inner_prod(rho + sigma, L + lambda[j] + a_rho + a[2*g]))) *
        mod(half_char_inner_prod(L + lambda[j] + a_rho + a[2*g] + rho) - 1, 2) * 
        theta_HI(D, L + lambda[j] + a_rho + a[2*g]) * theta_HI(D, L + lambda[j] + a_rho + a[2*g] + rho) *
        _sign_flip(v + rho) * theta_HI(D, v)
      end
    end
  end

  return result
end


function naive_non_orth_complement(rho::Vector{FqFieldElem})
  V = Iterators.product(repeat([[GF(2)(0),GF(2)(1)]], length(rho))...)
  result = Vector{FqFieldElem}[]
  for v in V 
    v = collect(v)
    if half_char_inner_prod(rho, v) + half_char_inner_prod(v, rho) == 1
      push!(result, v)
    end
  end
  return result
end

function construct_fay_matrix(g::Int, thetas, rho::Vector{FqFieldElem})
  W = naive_non_orth_complement(rho)
  M = Vector{AcbFieldElem}[]
  for w in W 
    v = frobenius_fay_relation(g, thetas, w, rho)
    push!(M, v)
  end
  return M
end

function number_of_odd_thetas(g)
  return 2^(g-1)*(2^g - 1) 
end

function number_of_even_thetas(g)
  return 2^(g-1)*(2^g + 1) 
end


function relation_with_term(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem}, terms, T::FqMatrix) where N
  @req g >= 4 "g needs to be bigger than 3."
  OO = max_noether_characteristics(g)
  v1 = max_noether_characteristics(g)[1]
  v2 = terms[1]

  a2 =  aronhold_system(g)
  M = map_even_characteristic(GF(2).(ZZ.((v1*2))), GF(2).(v2))

  a = aronhold_system(g, T*M)

 

  rho = QQ.(v2)//2 + QQ.(terms[2])//2
  sigma = QQ.(v2)//2 + QQ.(terms[3])//2

  #a = aronhold_system(g, azygetic_system_flip(g))
  a = [QQ.(lift.(Ref(ZZ), av))/2 for av in a]
  a0 = sum(a)

  l = Vector{QQFieldElem}[]
  for p in (1:g-3)
    push!(l, a[2*p+6] + a[2*p+7])
  end

  lambda = Vector{QQFieldElem}[]
  l_M = matrix(l)
  V = Iterators.product(repeat([[QQ(0),QQ(1)]], g-3)...)
  for v in V 
    v = [v...]
    push!(lambda, v * l_M)
  end

  A = Vector{QQFieldElem}[]

  for lam in lambda
    for ai in [[a0] ; a[1:7]]
      push!(A, lam+ai)
    end
  end

  L = sum(a[i] for i in (8:2:2*g))
  if mod(g, 2) == 1
    L += a0
  end

  new_v1 = L + lambda[1]

  CC = parent(thetas[zeros(Int, 2*g)...])
  R, X = polynomial_ring(CC, 2^(2*g))


  D = thetas

  theta_indices = Hecke.theta_characteristics_indices(g)
  Dv = Dict([(theta_indices[i+1], X[i]) for i in (1:2^(2*g)-1)])
  Dv[zeros(Int, 2*g)...] = X[2^(2*g)]


  factor = (-1)^(half_char_inner_prod(L, a[2*g]) + half_char_inner_prod(a[2*g], L) )
    terms = zeros(CC, 2^(g-3) +2^(g-1))
    term_tup = Vector{Int}[]
    i = 1
  
    for h in (1:2^(g-3)) 
      v1 = L + lambda[h]
      v2 = v1 + rho
      v3 = v1 + sigma 
      v4 = v3 + rho
      terms[i] = factor * (-1)^(half_char_inner_prod(lambda[h], lambda[h]) + 
      half_char_inner_prod(v1 +a0 + a[2*g], v1 + a0 + a[2*g])+half_char_inner_prod(rho+sigma, v1)) * 
      mod(half_char_inner_prod(v2) - 1, 2) *
      theta_HI(D, v1) * theta_HI(D, v2) *
      theta_HI(D, v3) * theta_HI(D, v4)
      push!(term_tup, sort(char_to_index.([v1,v2,v3,v4])))
      i+=1
    end

    for a_rho in [[a0] ; a[1:7]]
      for j in (1:2^(g-4))
        v1 = L + lambda[j] + a_rho + a[2*g]
        v2 = v1 + rho
        v3 = v1 + sigma 
        v4 = v3 + rho
        terms[i] = - (-1)^((half_char_inner_prod(lambda[j] + a_rho, L)  + half_char_inner_prod(L, lambda[j] +a_rho) + half_char_inner_prod(rho + sigma, v1))) *
        mod(half_char_inner_prod(v2) - 1, 2) * 
        theta_HI(D, v1) * theta_HI(D, v2) *
        theta_HI(D, v3) * theta_HI(D, v4)
        push!(term_tup, sort(char_to_index.([v1,v2,v3,v4])))
        i+=1
      end
    end

  sol = integral_left_kernel(matrix(terms))[1][end,:]
  result = filter(x->x[2]!=0, collect(zip(term_tup, sol)))
  nonsquare = true
  for t in term_tup
    if !allunique(t)
      nonsquare = false
    end
  end
  if length(result) > 2 &&  nonsquare 
    return true, sort!(result), T*M
  else 
    return false, [(Vector{Int64}[],ZZ(0))], T*M
  end
end
