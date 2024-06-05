################################################################################
#
#  The algorithm of Husert
#
################################################################################

function _issimilar_husert(A::ZZMatrix, B::ZZMatrix)
  QA = change_base_ring(FlintQQ, A)
  QB = change_base_ring(FlintQQ, B)
  fl, QC = _issimilar_husert_generic(QA, QB)
  return fl, change_base_ring(FlintZZ, QC)
end

# If successful, returns X such that X * A * X^-1 == B
function _issimilar_husert_generic(A, B)
  @assert is_squarefree(minpoly(A))
  m = nrows(A)
  f = charpoly(A)
  fac = factor(f)
  mus = typeof(f)[]
  ns = Int[]
  ds = Int[]
  for (p, n) in fac
    push!(mus, p)
    push!(ns, n)
    push!(ds, degree(p))
  end

  s = length(mus)
  Ks = AbsSimpleNumField[]
  vecsA = Matrix{AbsSimpleNumFieldElem}(undef, m, sum(ns))
  vecsB = Matrix{AbsSimpleNumFieldElem}(undef, m, sum(ns))
  k = 1
  for i in 1:s
    K, _ = number_field(mus[i], "a", cached = false)
    EA = eigenspace(change_base_ring(K, A), gen(K), side = :left)
    EB = eigenspace(change_base_ring(K, B), gen(K), side = :left)
    push!(Ks, K)
    if nrows(EA) != nrows(EB)
      return false, zero_matrix(FlintQQ, 0, 0)
    end
    @assert nrows(EA) == nrows(EB)
    for j in 1:nrows(EA)
      for l in 1:m
        vecsA[l, k] = EA[j, l]
        vecsB[l, k] = EB[j, l]
      end
      k += 1
    end
  end

  absolute_basis_vec_A = Vector{Vector{QQFieldElem}}()
  absolute_basis_vec_B = Vector{Vector{QQFieldElem}}()
  absolute_basis_A = zero_matrix(FlintQQ, m, m)
  absolute_basis_B = zero_matrix(FlintQQ, m, m)
  for i in 1:m
    vA = _to_absolute_basis(view(vecsA, i, :), m, ns, Ks)
    vB = _to_absolute_basis(view(vecsB, i, :), m, ns, Ks)
    push!(absolute_basis_vec_A, vA)
    push!(absolute_basis_vec_B, vB)
    for j in 1:m
      absolute_basis_A[i, j] = vA[j]
      absolute_basis_B[i, j] = vB[j]
    end
  end

  # Now construct the colon ideal
  # First the Q-basis of \prod Mat(n_i, K_i)
  actions = Vector{QQMatrix}()
  another_basis_of_actions = Vector{Vector{dense_matrix_type(AbsSimpleNumFieldElem)}}()

  for i in 1:s
    ni = ns[i]
    for i1 in 1:ni
      for i2 in 1:ni
        for j in 1:degree(Ks[i])
          V = Vector{dense_matrix_type(AbsSimpleNumFieldElem)}(undef, s)
          M = representation_matrix(gen(Ks[i])^(j - 1))
          z = zero_matrix(Ks[i], ni, ni)
          z[i1, i2] = gen(Ks[i])^(j-1)
          V[i] = z
          for j in 1:s
            if j != i
              V[j] = zero_matrix(Ks[j], ns[j], ns[j])
            end
          end
          push!(another_basis_of_actions, V)
          # I need to construct the block matrix, where M is at block (i1, i2)
          # and all the other ones are zero
          # The overall matrix must have size ni * degree(Ks[i])
          Z1 = zero_matrix(FlintQQ, (i1 - 1) * ds[i], ni * ds[i])
          Z2 = zero_matrix(FlintQQ, ds[i], (i2 - 1) * ds[i])
          Z3 = hcat(Z2, M)
          Z3 = hcat(Z3, zero_matrix(FlintQQ, ds[i], (ni - i2) * ds[i]))
          Z4 = zero_matrix(FlintQQ, (ni - i1) * ds[i], ni * ds[i])
          MM = vcat(Z1, Z3, Z4)
          blocklengthbefore = sum(Int[ns[o] * ds[o] for o in 1:(i - 1)])
          blocklengthafter = sum(Int[ns[o] * ds[o] for o in (i + 1):s])
          D = diagonal_matrix(
                zero_matrix(FlintQQ, blocklengthbefore, blocklengthbefore),
                MM,
                zero_matrix(FlintQQ, blocklengthafter, blocklengthafter))
          push!(actions, D)
        end
      end
    end
  end

  absolute_basis_B_inv = inv(absolute_basis_B)
  absolute_basis_A_inv = inv(absolute_basis_A)

  # So D is a Q-basis of Mat_n(K)

  # Now determine the colon ideal

  la = length(actions)

  M = zero_matrix(FlintQQ, la, 0)

  for a in absolute_basis_vec_A
    _M = zero_matrix(FlintQQ, la, m)
    for i in 1:length(actions)
      D = actions[i]
      v = matrix(FlintQQ, 1, m, a) * D * absolute_basis_B_inv
      for j in 1:m
        _M[i, j] = v[1, j]
      end
    end
    M = hcat(M, _M)
  end

  M = sub(hnf(FakeFmpqMat(transpose(M)), :upperright), 1:la, 1:la)
  N = inv(M)

  SS = N

  M = zero_matrix(FlintQQ, length(actions), 0)

  for a in absolute_basis_vec_B
    _M = zero_matrix(FlintQQ, length(actions), m)
    for i in 1:length(actions)
      D = actions[i]
      v = matrix(FlintQQ, 1, m, a) * D * absolute_basis_B_inv
      for j in 1:m
        _M[i, j] = v[j]
      end
    end
    M = hcat(M, _M)
  end
  M = sub(hnf(FakeFmpqMat(transpose(M)), :upperright), 1:la, 1:la)
  N = inv(M)

  bcolonb = N

  basis_of_colon_ideal = QQMatrix[sum(SS[i, j] * actions[i]
                                      for i in 1:length(actions))
                                      for j in 1:nrows(SS)]

  basis_of_colon_idealAA = QQMatrix[sum(bcolonb[i, j] * actions[i]
                                      for i in 1:length(actions))
                                      for j in 1:nrows(bcolonb)]

  other_basis_of_colon_ideal = Vector{dense_matrix_type(AbsSimpleNumFieldElem)}[]
  other_basis_of_colon_idealAA = Vector{dense_matrix_type(AbsSimpleNumFieldElem)}[]

  for j in 1:nrows(SS)
    ob = foldl((x, y) -> x .+ y,
               [SS[i, j] .* another_basis_of_actions[i] for i in 1:nrows(SS)])
    push!(other_basis_of_colon_ideal, ob)
  end

  for j in 1:nrows(bcolonb)
    ob = foldl((x, y) -> x .+ y,
               [bcolonb[i, j] .* another_basis_of_actions[i] for i in 1:nrows(bcolonb)])
    push!(other_basis_of_colon_idealAA, ob)
  end

  for a in absolute_basis_vec_A
    for i in 1:length(basis_of_colon_ideal)
      @assert denominator(matrix(FlintQQ, 1, m, a) *
                            basis_of_colon_ideal[i] * absolute_basis_B_inv) == 1
    end
  end

  A = _matrix_algebra(Ks, ns)

  idealAgens = elem_type(A)[]

  ordergens = elem_type(A)[]

  dec = decompose(A)

  for b in other_basis_of_colon_ideal
    z = zero(A)
    @assert length(dec) == length(b)
    for i in 1:length(dec)
      B, mB = dec[i]
      C, BtoC = B.isomorphic_full_matrix_algebra
      z = z + mB(preimage(BtoC, C(b[i]))::elem_type(B))
    end
    push!(idealAgens, z)
  end

  for b in other_basis_of_colon_idealAA
    z = zero(A)
    @assert length(dec) == length(b)
    for i in 1:length(dec)
      B, mB = dec[i]
      local C::MatAlgebra{AbsSimpleNumFieldElem, Generic.MatSpaceElem{AbsSimpleNumFieldElem}}
      C, BtoC = B.isomorphic_full_matrix_algebra
      z = z + mB(preimage(BtoC, C(b[i]))::elem_type(B))
    end
    push!(ordergens, z)
  end

  ide = ideal_from_lattice_gens(A, idealAgens)
  ideO = Order(A, ordergens)

  @assert ideO == right_order(ide)

  #@assert right_order(ide) == ideO

  fl, y = _is_principal_with_data_bhj(ide, ideO, side = :right)

  if fl
    dec = decompose(A)
    D = Vector{Generic.MatSpaceElem{AbsSimpleNumFieldElem}}(undef, length(dec))
    for i in 1:length(dec)
      B, mB = dec[i]
      local C::MatAlgebra{AbsSimpleNumFieldElem, Generic.MatSpaceElem{AbsSimpleNumFieldElem}}
      C, BtoC = B.isomorphic_full_matrix_algebra
      z = BtoC(mB\y)::elem_type(C)
      D[i] = matrix(z)
    end
    DD = diagonal_matrix(QQMatrix[_explode(D[i]) for i in 1:length(D)])
    return fl, transpose(absolute_basis_A * DD * absolute_basis_B_inv)
  else
    return false, zero_matrix(FlintQQ, 0, 0)
  end
end

function _explode(x::Generic.MatSpaceElem{AbsSimpleNumFieldElem})
  K = base_ring(x)
  d = degree(K)
  n = nrows(x)
  m = ncols(x)
  z = zero_matrix(FlintQQ, 0, n * d)
  for i in 1:n
    zz = zero_matrix(FlintQQ, d, 0)
    for j in 1:m
      M = representation_matrix(x[i, j])
      zz = hcat(zz, M)
    end
    z = vcat(z, zz)
  end
  return z
end

function _to_absolute_basis(v, m, ns, Ks)
  w = Vector{QQFieldElem}(undef, m)
  k = 1
  for i in 1:sum(ns)
    vi = v[i]
    K = parent(vi)
    for j in 1:degree(K)
      w[k] = coeff(vi, j - 1)
      k += 1
    end
  end
  return w
end

function _to_relative_basis(v, m, ns, Ks)
  w = Vector{AbsSimpleNumFieldElem}(undef, sum(ns))
  k = 1
  l = 1
  for i in 1:length(ns)
    a = gen(Ks[i])
    for j in 1:ns[i]
      w[k] = zero(Ks[i])
      for n in 1:degree(Ks[i])
        w[k] = w[k] + a^(n - 1) * v[l]
        l += 1
      end
      k += 1
    end
  end
  return w
end

function _matrix_algebra(Ks, ns)
  s = length(Ks)
  algs = StructureConstantAlgebra{QQFieldElem}[]
  for i in 1:s
    A = matrix_algebra(Ks[i], ns[i])
    B, BtoA = StructureConstantAlgebra(A)
    C, CtoB = restrict_scalars(B, FlintQQ)
    C.isomorphic_full_matrix_algebra = (A, CtoB * BtoA)
    push!(algs, C)
  end
  return _my_direct_product(algs)
end

