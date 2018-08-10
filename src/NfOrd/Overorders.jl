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

function poverorders_from_multipliers(O, p::fmpz)
  M = MaximalOrder(O)
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

function poverorders(O, p::fmpz)
  to_enlarge = typeof(O)[O]
  current = Dict{fmpq, Dict{FakeFmpqMat, typeof(O)}}()
  while length(to_enlarge) > 0
    N = pop!(to_enlarge)
    new = poverorders_from_multipliers(N, p)
    for S in new
      H = hnf(basis_mat(S, Val{false}))
      ind = prod(H.num[i, i] for i in 1:degree(O))//H.den
      if haskey(current, ind)
        c = current[ind]
        if haskey(c, H)
          continue
        else
          c[H] = S
          push!(to_enlarge, S)
        end
      else
        c = Dict{FakeFmpqMat, typeof(O)}()
        current[ind] = c
        c[H] = S
        push!(to_enlarge, S)
      end
    end
  end
  for d in values(current)
    for e in values(d)
      push!(to_enlarge, e)
    end
  end
  return to_enlarge
end

function _overorders_meataxe(O::AlgAssAbsOrd, M::AlgAssAbsOrd)
  K = O.algebra
  d = degree(O)
  B = zero_matrix(FlintZZ, d, d)
  orders = Vector{typeof(O)}()
  for i in 1:d
    v = elem_in_basis(M(elem_in_algebra(basis(O)[i])))
    for j in 1:d
      B[i, j] = v[j]
    end
  end
  S::fmpz_mat, U::fmpz_mat, V::fmpz_mat = snf_with_transform(B, true, true)
  Vinv = inv(V)
  basis_O = basis(O)
  basis_M = basis(M)
  new_basis_O = Vector{AlgAssElem{fmpq}}(d)
  new_basis_M = Vector{AlgAssElem{fmpq}}(d)
  for i in 1:d
    new_basis_O[i] = elem_in_algebra(sum(U[i, j] * basis_O[j] for j in 1:d))
  end

  for i in 1:d
    new_basis_M[i] = elem_in_algebra(sum(Vinv[i, j] * basis_M[j] for j in 1:d))
  end

  new_basis_mat_M_inv = inv(basis_mat(new_basis_M))

  autos = GrpAbFinGenMap[]

  A = DiagonalGroup(fmpz[ S[i, i] for i in 1:d])

  for i in 1:d
    b = new_basis_O[i]
    m = zero_matrix(FlintZZ, d, d)
    for j in 1:d
      v = elem_in_algebra(M(b* new_basis_M[j]))
      t = FakeFmpqMat(matrix(FlintQQ, 1, degree(O), v.coeffs)) * new_basis_mat_M_inv
      # I need the representation with respect to new_basis_M
      for k in 1:d
        m[j, k] = t.num[1, k]
      end
    end
    push!(autos, hom(A, A, m))
  end
    
  potential_basis = Vector{AlgAssElem{fmpq}}(d)

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

# Overorders in case O is Bass
# This is currently broken
function poverorders_bass(O::NfOrd, p::fmpz)
  lP = prime_decomposition(maximal_order(nf(O)), p)
  M = basis_mat(O)
  n = degree(O)
  for (P, e) in lP
    pi = uniformizer(P)
    a = pi
    for k in 1:2 
      N, d = representation_matrix_q(a.elem_in_nf)
      NN = FakeFmpqMat(vcat(M.num * d, N * M.den), d * M.den)
      EE = Order(nf(O), sub(hnf(NN, :lowerleft), n + 1:2*n, 1:n))
      @show EE
      a = a * pi
    end
  end
end

################################################################################
#
#  Goursat
#
################################################################################

function ideals_with_norm(O::NfOrd, p::fmpz, n::Int)
  pn = p^n
  pInt = Int(p)
  K = nf(O)
  d = degree(O)
  ideals = []
  B = basis(O)

  autos = GrpAbFinGenMap[]

  A = DiagonalGroup(fmpz[pn for i in 1:d])

  for i in 1:d
    m = representation_matrix(B[i])
    push!(autos, hom(A, A, m))
  end

  potential_basis = Vector{elem_type(O)}(d)
  ideals = Vector{Tuple{Vector{Int}, ideal_type(O)}}()

  for par in AllParts(n)
    ppar = Vector(par)

    subs = stable_subgroups(A, autos, quotype=[pInt^y for y in ppar])

    for s in subs
      new_basis_mat = zero_matrix(FlintZZ, d, d)
      T = image(s[2])
      G = domain(T[2])
      for i in 1:d
        v = T[2](G[i]).coeff
        if iszero(v)
          new_basis_mat[i, i] = pn
        else
          for j in 1:d
            new_basis_mat[i, j] = v[1, j]
          end
        end
      end
      push!(ideals, ([pInt^y for y in ppar], ideal(O, new_basis_mat)))
    end
  end
  return ideals
end

function index(R::NfOrd, S::NfOrd)
  r = gen_index(R)
  s = gen_index(S)
  i = r^-1 * s
  @assert isinteger(i)
  return FlintZZ(i)
end

function poverorders_goursat(O1::NfOrd, O2::NfOrd, p::fmpz)
  l1 = poverorders(O1, p)
  l2 = poverorders(O2, p)
  data_from_l2 = Dict{Vector{Int}, Vector{Tuple{typeof(O1), ideal_type(O1)}}}()
  d = degree(O2)
  for O in l2
    i = index(O2, O)
    e, _ = ispower(i)
    for k in 1:e
      ideals = ideals_with_norm(O, p, k)
      for (typ, I) in ideals
        if haskey(data_from_l2, typ)
          push!(data_from_l2[typ], (O, I))
        else
          data_from_l2[typ] = [(O, I)]
        end
      end
    end
  end

  return data_from_l2
end

function abelian_group(Q::NfOrdQuoRing)
  A = AbelianGroup(Q.basis_mat)
  S, mS = snf(A)
  B = basis(Q.base_ring, Val{false})
  f = a -> begin aa = mS(a); Q(sum(aa.coeff[i] * B[i] for i in 1:degree(Q.base_ring))) end
  g = b -> mS\A(elem_in_basis(b.elem))
  return S, f, g
end

function isisomorphic(Q1::NfOrdQuoRing, Q2::NfOrdQuoRing)
  Q1_A, Q1_mA, Q1_mA_inv = abelian_group(Q1)
  Q2_A, Q2_mA, Q2_mA_inv = abelian_group(Q2)

  if Q1_A.snf != Q2_A.snf
    return false
  end

  Q1_U, Q1_mU = multiplicative_group(Q1)
  Q2_U, Q2_mU = multiplicative_group(Q2)

  if Q1_U.snf != Q2_U.snf
    return false
  end

  Q1_gens = [ Q1_mA(g) for g in gens(Q1_A) ]

  orders = [ order(g) for g in gens(Q1_A) ]

  l = length(Q1_A.snf)

  elements_with_correct_order = Dict{fmpz, Vector{GrpAbFinGenElem}}()

  @show orders

  for g in Q2_A
    o = order(g)
    if o in orders
      #elem_g = Q2_mA(g)
      if !haskey(elements_with_correct_order, o)
        elements_with_correct_order[o] = GrpAbFinGenElem[g]
      else
        push!(elements_with_correct_order[o], g)
      end
    end
  end

  isos = []
 
  genQ1A = gens(Q1_A)

  O1 = base_ring(Q1)
  O2 = base_ring(Q2)

  basis_O1 = basis(O1)

  for poss in Iterators.product([ elements_with_correct_order[o] for o in orders]...)
    #@show poss
    h = hom(Q1_A, collect(poss))
    if !isbijective(h)
      continue
    end
    if h(Q1_mA_inv(one(Q1))) != Q2_mA_inv(one(Q2))
      continue
    end
    multiplicative = true
    for i in 1:l
      for j in i:l
        @assert h(genQ1A[i]) == poss[i]
        @assert h(genQ1A[j]) == poss[j]
        if h(Q1_mA_inv(Q1_mA(genQ1A[i]) * Q1_mA(genQ1A[j]))) != Q2_mA_inv(Q2_mA(poss[i]) * Q2_mA(poss[j]))
          multiplicative = false
          break
        end
      end
      if !multiplicative
        break
      end
    end
    if multiplicative
      M = Array{fmpz}(degree(O1), degree(O2))
      for i in 1:degree(O1)
        v = elem_in_basis(Q2_mA(h(Q1_mA_inv(Q1(basis_O1[i])))).elem)
        for j in 1:degree(O2)
          M[i, j] = v[j]
        end
      end
      push!(isos, M)
    end
  end
  return isos
end

