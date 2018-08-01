export overorders, isbass, isgorenstein, prime_ideals_over

function overorders_naive(O::NfOrd, M::NfOrd = maximal_order(nf(O)))
  M = maximal_order(nf(O))
  d = degree(O)
  K = nf(O)
  B = zero_matrix(FlintZZ, d, d)
  for i in 1:d
    v = elem_in_basis(M(elem_in_nf(basis(O)[i])))
    for j in 1:d
      B[i, j] = v[j]
    end
  end
  S, U, V = snf_with_transform(B, true, true)
  Vinv = inv(V)
  basis_O = basis(O)
  basis_M = basis(M)
  new_basis_O = Vector{nf_elem}(d)
  new_basis_M = Vector{nf_elem}(d)
  for i in 1:d
    new_basis_O[i] = elem_in_nf(sum(U[i, j] * basis_O[j] for j in 1:d))
  end
  
  for i in 1:d
    new_basis_M[i] = elem_in_nf(sum(Vinv[i, j] * basis_M[j] for j in 1:d))
  end

  A = AbelianGroup(S)

  if order(A) == 1
    return typeof(O)[O]
  end

  subs = subgroups(A)
  potential_basis = Vector{nf_elem}(d)
  oorders = typeof(O)[]
  for s in subs
    T = image(s[2])
    G = domain(T[2])
    for i in 1:d
      v = T[2](G[i]).coeff
      if iszero(v)
        potential_basis[i] = new_basis_O[i]
      else
        potential_basis[i] = sum(v[1, j] * new_basis_M[j] for j in 1:d)
      end
    end
    b, bmat = defines_order(K, potential_basis)
    if b 
      push!(oorders, Order(K, bmat))
    end
  end
  return oorders
end

function poverorders_meataxe(O::NfOrd, p::Integer)
  return poverorders_meataxe(O, fmpz(p))
end

function minimal_poverorders_naive(O::NfOrd, p::fmpz)
  orders = poverorders_meataxe(O, p)
  res = Vector{typeof(O)}()
  for S in orders
    if length(overorders_meataxe(O, S)) == 2
      push!(res, S)
    end
  end
  return res
end

function poverorders_from_multipliers(O::NfOrd, p::fmpz)
  M = maximal_order(nf(O))
  lP = prime_ideals_over(O, p)
  orders = typeof(O)[]
  for P in lP
    E = ring_of_multipliers(P)
    if index(E) != index(O)
      append!(orders, _overorders_meataxe(O, E))
    end
  end
  if length(orders) == 0
    push!(orders, O)
  end
  return orders
end

#function poverorders(O::NfOrd, p::fmpz)
#  to_enlarge = typeof(O)[O]
#  current = Dict{fmpz, Vector{typeof(O)}}
#  while length(to_enlarge) > 0
#    N = pop!(to_enlarge)
#    new = poverorders_from_multipliers(N, p)
#    for S in N
#      H = hnf(basis_mat(S, Val{false}))
#      ind = index(S)
#      if haskey(current, ind)
#        if
#        end
#      end
#    end
#  end
#end

function _overorders_meataxe(O::NfOrd, M::NfOrd)
  K = nf(O)
  d = degree(O)
  B = zero_matrix(FlintZZ, d, d)
  orders = Vector{typeof(O)}()
  for i in 1:d
    v = elem_in_basis(M(elem_in_nf(basis(O)[i])))
    for j in 1:d
      B[i, j] = v[j]
    end
  end
  S::fmpz_mat, U::fmpz_mat, V::fmpz_mat = snf_with_transform(B, true, true)
  Vinv = inv(V)
  basis_O = basis(O)
  basis_M = basis(M)
  new_basis_O = Vector{nf_elem}(d)
  new_basis_M = Vector{nf_elem}(d)
  for i in 1:d
    new_basis_O[i] = elem_in_nf(sum(U[i, j] * basis_O[j] for j in 1:d))
  end

  for i in 1:d
    new_basis_M[i] = elem_in_nf(sum(Vinv[i, j] * basis_M[j] for j in 1:d))
  end

  new_basis_mat_M_inv = inv(basis_mat(new_basis_M))

  autos = GrpAbFinGenMap[]

  A = DiagonalGroup(fmpz[ S[i, i] for i in 1:d])

  for i in 1:d
    b = new_basis_O[i]
    m = zero_matrix(FlintZZ, d, d)
    for j in 1:d
      v = elem_in_nf(M(b* new_basis_M[j]))
      t = O.tcontain
      elem_to_mat_row!(t.num, 1, t.den, v)
      t = mul!(t, t, new_basis_mat_M_inv)
      # I need the representation with respect to new_basis_M
      for k in 1:d
        m[j, k] = t.num[1, k]
      end
    end
    push!(autos, hom(A, A, m))
  end
    
  potential_basis = Vector{nf_elem}(d)

  subs = stable_subgroups(A, autos)
  for s in subs
    T = image(s[2])
    G = domain(T[2])
    for i in 1:d
      v = T[2](G[i]).coeff
      if iszero(v)
        potential_basis[i] = new_basis_O[i]
      else
        potential_basis[i] = sum(v[1, j] * new_basis_M[j] for j in 1:d)
      end
    end
    b, bmat = defines_order(K, deepcopy(potential_basis))
    if b 
      push!(orders, Order(K, bmat))
    end
  end
  return orders
end


function poverorders_meataxe(O::NfOrd, p::fmpz, N::NfOrd = pmaximal_overorder(O, p))
  K = nf(O)
  d = degree(O)
  M = intersection(N, pmaximal_overorder(O, p))
  B = zero_matrix(FlintZZ, d, d)
  orders = Vector{typeof(O)}()
  for i in 1:d
    v = elem_in_basis(M(elem_in_nf(basis(O)[i])))
    for j in 1:d
      B[i, j] = v[j]
    end
  end
  S::fmpz_mat, U::fmpz_mat, V::fmpz_mat = snf_with_transform(B, true, true)
  Vinv = inv(V)
  basis_O = basis(O)
  basis_M = basis(M)
  new_basis_O = Vector{nf_elem}(d)
  new_basis_M = Vector{nf_elem}(d)
  for i in 1:d
    new_basis_O[i] = elem_in_nf(sum(U[i, j] * basis_O[j] for j in 1:d))
  end

  for i in 1:d
    new_basis_M[i] = elem_in_nf(sum(Vinv[i, j] * basis_M[j] for j in 1:d))
  end

  new_basis_mat_M_inv = inv(basis_mat(new_basis_M))

  autos = GrpAbFinGenMap[]

  A = DiagonalGroup(fmpz[ S[i, i] for i in 1:d])

  for i in 1:d
    b = new_basis_O[i]
    m = zero_matrix(FlintZZ, d, d)
    for j in 1:d
      v = elem_in_nf(M(b* new_basis_M[j]))
      t = O.tcontain
      elem_to_mat_row!(t.num, 1, t.den, v)
      t = mul!(t, t, new_basis_mat_M_inv)
      # I need the representation with respect to new_basis_M
      for k in 1:d
        m[j, k] = t.num[1, k]
      end
    end
    push!(autos, hom(A, A, m))
  end
    
  potential_basis = Vector{nf_elem}(d)

  subs = stable_subgroups(A, autos)
  for s in subs
    T = image(s[2])
    G = domain(T[2])
    for i in 1:d
      v = T[2](G[i]).coeff
      if iszero(v)
        potential_basis[i] = new_basis_O[i]
      else
        potential_basis[i] = sum(v[1, j] * new_basis_M[j] for j in 1:d)
      end
    end
    b, bmat = defines_order(K, deepcopy(potential_basis))
    if b 
      push!(orders, Order(K, bmat))
    end
  end
  return orders
end

function overorders_meataxe(O::NfOrd, M::NfOrd = maximal_order(O))
  orders = Vector{typeof(O)}[]

  k = 1

  for (p, ) in factor(div(index(M), index(O)))
    push!(orders, poverorders_meataxe(O, p, M))
  end

  if length(orders) == 0
    return typeof(O)[O]
  end

  res = Vector{typeof(O)}(prod(length(orders[i]) for i in 1:length(orders)))

  if length(orders) == 1
    return orders[1]
  else
    I = Iterators.product(orders...)
    for (j, i) in enumerate(I)
      res[j] = sum(i)
    end
    return res
  end
end

doc"""
    overorders(O::NfOrd)

Returns all overorders of $\mathcal O$.
"""
function overorders(O::NfOrd)
  return overorders_meataxe(O)
end

prime_ideals_over(O::NfOrd, p::Integer) = prime_ideals_over(O, fmpz(p))

function prime_ideals_over(O::NfOrd, p::fmpz)
  M = maximal_order(O)
  p_critical_primes = Vector{ideal_type(O)}()
  lp = prime_decomposition(M, p)
  for (P, e) in lp
    push!(p_critical_primes, contract(P, O))
  end
  return unique(p_critical_primes)
end

function isbass(O::NfOrd, p::fmpz)
  M = maximal_order(O)
  p_critical_primes = Set{ideal_type(O)}()
  lp = prime_decomposition(M, p)
  for (P, e) in lp
    push!(p_critical_primes, contract(P, O))
  end
  for Q in p_critical_primes
    resfield_dim = valuation(norm(Q), p)
    ext_dim = valuation(norm(Q * M), p)
    @assert mod(ext_dim, resfield_dim) == 0
    if div(ext_dim, resfield_dim) > 2
      return false
    end
  end
  return true
end

function isbass(O::NfOrd)
  f = minimum(conductor(O))
  M = maximal_order(nf(O))
  for (p, ) in factor(f)
    if !isbass(O, p)
      return false
    end
  end
  return true
end

function isgorenstein(O)
  codiff = codifferent(O)
  R = simplify(simplify(colon(1*O, codiff.num) * codiff) * codiff.den)
  return isone(norm(R))
end

function isgorenstein(O::NfOrd, p::Int)
  return isgorenstein(O, fmpz(p))
end

function isgorenstein(O::NfOrd, p::fmpz)
  codiff = codifferent(O)
  R = simplify(simplify(colon(1*O, codiff.num) * codiff) * codiff.den)
  v = valuation(norm(R), p)
  return v == 0
end

# This is very slow!
function intersection(x::NfOrd, y::NfOrd)
  d = degree(x)
  g = lcm(denominator(basis_mat(x)), denominator(basis_mat(y)))
  H = vcat(divexact(g * basis_mat(x).num, basis_mat(x).den), divexact(g * basis_mat(y).num, basis_mat(y).den))
  K = _kernel(H)
  return Order(nf(x), FakeFmpqMat(_hnf(sub(K, 1:d, 1:d)*divexact(g * basis_mat(x).num, basis_mat(x).den), :lowerleft), g))
end

