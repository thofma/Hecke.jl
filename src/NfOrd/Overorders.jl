export overorders

function overorders_naive(O::NfOrd)
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

function overorders_meataxe(O::NfOrd)
  MO = maximal_order(nf(O))
  d = degree(O)
  K = nf(O)
  oorders = Tuple{fmpz, Vector{typeof(O)}}[]
  for (p, ) in factor(index(MO))
    M = pmaximal_overorder(O, p)
    B = zero_matrix(FlintZZ, d, d)
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

    autos = GrpAbFinGenMap[]

    A = DiagonalGroup(fmpz[ S[i, i] for i in 1:d])

    for i in 1:d
      b = new_basis_O[i]
      m = zero_matrix(FlintZZ, d, d)
      for j in 1:d
        v = elem_in_basis(M(b* new_basis_M[j]))
        for k in 1:d
          m[j, k] = v[k]
        end
      end
      push!(autos, hom(A, A, m))
    end
      # get p-type
    ptype = sort(Int[ valuation(A.snf[k], p) for k in 1:d if valuation(A.snf[k], p) > 0], rev = true)
    l = _subpartitions(ptype)
    new_orders = typeof(O)[]
    potential_basis = Vector{nf_elem}(d)
    for par in l
      if sum(par) == 0
        push!(new_orders, M)
      else
        subs = stable_subgroups(A, Int[p^par[k] for k in 1:length(par) if par[k] > 0], autos)
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
            push!(new_orders, Order(K, bmat))
          end
        end
      end
    end
    push!(oorders, (p, new_orders))
  end

  only_orders = Vector{typeof(O)}[oorders[i][2] for i in 1:length(oorders)]

  res = Vector{typeof(O)}()

  return only_orders

  if length(only_orders) == 1
    return only_orders[1]
  else
    I = Iterators.product(only_orders...)
    for i in I
      push!(res, sum(i))
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
