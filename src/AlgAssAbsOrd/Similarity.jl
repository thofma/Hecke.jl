# If successful, returns X such that X * A * X^-1 == B 
function _issimilar_husert_generic(A, B)
  @assert issquarefree(minpoly(A))
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
  Ks = AnticNumberField[]
  vecsA = Matrix{nf_elem}(undef, m, sum(ns))
  vecsB = Matrix{nf_elem}(undef, m, sum(ns))
  k = 1
  for i in 1:s
    K, _ = NumberField(mus[i], "a", cached = false)
    EA = eigenspace(change_base_ring(K, A), gen(K))
    EB = eigenspace(change_base_ring(K, B), gen(K))
    push!(Ks, K)
    if length(EA) != length(EB)
      return false, zero_matrix(FlintQQ, 0, 0)
    end
    @assert length(EA) == length(EB)
    for j in 1:length(EA)
      for l in 1:m
        vecsA[l, k] = EA[j][l]
        vecsB[l, k] = EB[j][l]
      end
      k += 1
    end
  end

  @show Ks, ns
#  for i in 1:m
#    @show view(vecsA, i, :)
#    @show _to_relative_basis(_to_absolute_basis(view(vecsA, i, :), m, ns, Ks), m, ns, Ks)
#  end

  absolute_basis_vec_A = Vector{Vector{fmpq}}()
  absolute_basis_vec_B = Vector{Vector{fmpq}}()
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

  #@show "asds"

  # Now construct the colon ideal
  # First the Q-basis of \prod Mat(n_i, K_i) 
  actions = Vector{fmpq_mat}()
  another_basis_of_actions = Vector{Vector{dense_matrix_type(nf_elem)}}()

  for i in 1:s
    ni = ns[i]
    for i1 in 1:ni
      for i2 in 1:ni
        for j in 1:degree(Ks[i])
          V = Vector{dense_matrix_type(nf_elem)}(undef, s)
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
          D = diagonal_matrix(zero_matrix(FlintQQ, blocklengthbefore, blocklengthbefore), MM, zero_matrix(FlintQQ, blocklengthafter, blocklengthafter))
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

  basis_of_colon_ideal = fmpq_mat[sum(SS[i, j] * actions[i] for i in 1:length(actions)) for j in 1:nrows(SS)]

  basis_of_colon_idealAA = fmpq_mat[sum(bcolonb[i, j] * actions[i] for i in 1:length(actions)) for j in 1:nrows(bcolonb)]

  other_basis_of_colon_ideal = Vector{dense_matrix_type(nf_elem)}[]
  other_basis_of_colon_idealAA = Vector{dense_matrix_type(nf_elem)}[]

  for j in 1:nrows(SS)
    push!(other_basis_of_colon_ideal, foldl((x, y) -> x .+ y, [SS[i, j] .* another_basis_of_actions[i] for i in 1:nrows(SS)]))
  end

  for j in 1:nrows(bcolonb)
    push!(other_basis_of_colon_idealAA, foldl((x, y) -> x .+ y, [bcolonb[i, j] .* another_basis_of_actions[i] for i in 1:nrows(bcolonb)]))
  end

  for a in absolute_basis_vec_A
    for i in 1:length(basis_of_colon_ideal)
      @assert denominator(matrix(FlintQQ, 1, m, a)  * basis_of_colon_ideal[i] * absolute_basis_B_inv) == 1
      #@assert denominator(matrix(FlintQQ, 1, m, a)  * basis_of_colon_idealAA[i] * absolute_basis_A_inv) == 1
    end
  end

  A = _create_algebra_husert(Ks, ns)

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
      local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
      C, BtoC = B.isomorphic_full_matrix_algebra
      z = z + mB(preimage(BtoC, C(b[i]))::elem_type(B))
    end
    push!(ordergens, z)
  end

  ide = ideal_from_lattice_gens(A, idealAgens)
  ideO = Order(A, ordergens)

  @assert ideO == right_order(ide)

  #@assert right_order(ide) == ideO

  fl, y = _isprincipal(ide, ideO, :right)

  if fl
    dec = decompose(A)
    D = Vector{Generic.MatSpaceElem{nf_elem}}(undef, length(dec))
    for i in 1:length(dec)
      B, mB = dec[i]
      local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
      C, BtoC = B.isomorphic_full_matrix_algebra
      z = BtoC(mB\y)::elem_type(C)
      D[i] = matrix(z)
    end
    DD = diagonal_matrix(fmpq_mat[_explode(D[i]) for i in 1:length(D)])
    return fl, transpose(absolute_basis_A * DD * absolute_basis_B_inv)
  else
    return false, zero_matrix(FlintQQ, 0, 0)
  end
end

function _explode(x::Generic.MatSpaceElem{nf_elem})
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

Base.:(*)(x::fmpq, y::AbstractAlgebra.Generic.MatSpaceElem{nf_elem}) = base_ring(y)(x) * y

function _to_absolute_basis(v, m, ns, Ks)
  w = Vector{fmpq}(undef, m)
  k = 1
  for i in 1:sum(ns)
    vi = v[i]
    #@show i, vi
    #@assert parent(vi) == Ks[i]
    K = parent(vi)
    for j in 1:degree(K)
      w[k] = coeff(vi, j - 1)
      k += 1
    end
  end
  return w
end

function _to_relative_basis(v, m, ns, Ks)
  w = Vector{nf_elem}(undef, sum(ns))
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

function _create_algebra_husert(Ks, ns)
  s = length(Ks)
  algs = AlgAss{fmpq}[]
  for i in 1:s
    A = matrix_algebra(Ks[i], ns[i])
    B, BtoA = AlgAss(A)
    C, CtoB = restrict_scalars(B, FlintQQ)
    C.isomorphic_full_matrix_algebra = (A, CtoB * BtoA)
    push!(algs, C)
  end
  return _my_direct_product(algs)
end

function _issimilar_husert(A::fmpz_mat, B::fmpz_mat)
  QA = change_base_ring(FlintQQ, A)
  QB = change_base_ring(FlintQQ, B)
  fl, QC = _issimilar_husert_generic(QA, QB)
  return fl, change_base_ring(FlintZZ, QC)
end

################################################################################
#
#  General approach
#
################################################################################

mutable struct CommutatorAlgebra
  A# matrix
  K# number fields of the minpoly
  Jblocks # Jordanblocks
  Eig# Eigenbases over K
  EigAbs# absolute bases of Eigenspaces

  CommutatorAlgebra() = new()
end

function _issimilar_new(A::fmpz_mat, B::fmpz_mat)
  AQ = change_base_ring(FlintQQ, A)
  BQ = change_base_ring(FlintQQ, B)
  return _issimilar_new(AQ, BQ)
end

function _issimilar_new(A, B)
  Z = Hecke.CommutatorAlgebra3(A)
  _compute_decomposition!(Z)
  Ks, ns = _decomposition_type(Z)
  @show defining_polynomial.(Ks)
  @show ns
  AA = _create_algebra_husert(Ks, ns)
  O = _basis_of_integral_commutator_algebra_saturate(A, A)
  #@show O
  I = _basis_of_integral_commutator_algebra_saturate(A, B)
  #@show I
  ordergens = elem_type(AA)[]
  idealgens = elem_type(AA)[]
  dec = decompose(AA)

  CA, TA = rational_canonical_form(A)
  CB, TB = rational_canonical_form(B)

  #@show "HEREREHRE"
  if CA != CB
    return false, zero_matrix(FlintQQ, 0, 0)
  end

  _C = inv(TB) * TA

#  @show denominator(_C)
#
#  @show _C

  @assert _C * A == B * _C

  invC = inv(_C)

#  @show length(O)
#
#  @show _A = matrix_algebra(FlintQQ, map(x -> change_base_ring(FlintQQ, x), O))
#  println(A)

#  for bb in O
#    for bbb in O
#      @show bb, bbb
#      @show _induce_action_mod(Z, bb)[1] * _induce_action_mod(Z, bbb)[1]
#      @show _induce_action_mod(Z, bb)[1]
#      @show _induce_action_mod(Z, bbb)[1]
#      @show _induce_action_mod(Z, bb * bbb)
#      @show _induce_action(Z, bb * bbb)
#      @show _induce_action(Z, bb)
#      @show _induce_action(Z, bbb)
#      @show _induce_action(Z, bb)[1] * _induce_action(Z, bbb)[1] - _induce_action(Z, bb * bbb)[1]
#      #@assert [_induce_action_mod(Z, bb)[1] * _induce_action_mod(Z, bbb)[1]] == _induce_action_mod(Z, bb * bbb)
#    end
#  end

  for bb in O
    #@show bb
    b = _induce_action_mod(Z, bb)
    #@show _induce_action(Z, bb^2)
    #@show map(x -> x^2, _induce_action(Z, bb))
    #@assert _induce_action_mod(Z, bb^2) == map(x -> x^2, _induce_action_mod(Z, bb))
    #println(sprint(show, "text/plain", b))
    z = zero(AA)
    @assert length(dec) == length(b)
    for i in 1:length(dec)
      BB, mB = dec[i]::Tuple{AlgAss{fmpq},Hecke.AbsAlgAssMor{AlgAss{fmpq},AlgAss{fmpq},fmpq_mat}}
      local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
      C, BtoC = BB.isomorphic_full_matrix_algebra
      z = z + mB(preimage(BtoC, C(b[i]))::elem_type(BB))
    end
    push!(ordergens, z)
  end

  #println(sprint(show, "text/plain", basis_matrix(ordergens)))

  for bb in I
    b = _induce_action_mod(Z, invC * bb)
    z = zero(AA)
    @assert length(dec) == length(b)
    for i in 1:length(dec)
      BB, mB = dec[i]::Tuple{AlgAss{fmpq},Hecke.AbsAlgAssMor{AlgAss{fmpq},AlgAss{fmpq},fmpq_mat}}
      local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
      C, BtoC = BB.isomorphic_full_matrix_algebra
      z = z + mB(preimage(BtoC, C(b[i]))::elem_type(BB))
    end
    push!(idealgens, z)
  end

  #@show dim(AA)

  #@show ordergens

  #@show "HEREREHRE2"
  OO = Order(AA, ordergens)
  OI = ideal_from_lattice_gens(AA, idealgens)
  #println(sprint(show, "text/plain", numerator(basis_matrix(right_order(OI)))))
  #println(sprint(show, "text/plain", denominator(basis_matrix(right_order(OI)))))
  #println(sprint(show, "text/plain", numerator(basis_matrix(OO))))
  #println(sprint(show, "text/plain", denominator(basis_matrix(OO))))
  @assert OO == right_order(OI)
  fl, y = _isprincipal(OI, OO, :right)::Tuple{Bool, AlgAssElem{fmpq,AlgAss{fmpq}}}

  if !fl
    return false, zero_matrix(FlintQQ, 0, 0)
  end

  @assert y * OO == OI

  #@show y in OI
 
  # I have to transport this back to an element of M_n(Q)

  z = Generic.MatSpaceElem{nf_elem}[]
  for i in 1:length(dec)
    BB, mB = dec[i]::Tuple{AlgAss{fmpq},Hecke.AbsAlgAssMor{AlgAss{fmpq},AlgAss{fmpq},fmpq_mat}}
    local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    C, BtoC = BB.isomorphic_full_matrix_algebra
    push!(z, matrix(BtoC(mB\y)))
  end

  # I know invC * I maps surjectively onto OI
  # Let's let the generator y

  d = denominator(OI, OO)

  Y = zero_matrix(FlintZZ, length(idealgens), dim(AA))
  for i in 1:length(idealgens)
    cc = coordinates(OO(d * idealgens[i]))
    @assert length(cc) == dim(AA)
    for j in 1:length(cc)
      Y[i, j] = cc[j]
    end
  end

  YY = matrix(FlintZZ, 1, dim(AA), coordinates(OO(d * y)))

  fl, vv = can_solve(Y, YY, side = :left)
  @assert fl
  yy = zero_matrix(FlintQQ, nrows(A), nrows(A))
  for i in 1:length(vv)
    yy = yy + vv[1, i] * (invC * I[i])
  end

  T = _C * yy

#  @show T
#  @show det(T)

  @assert abs(denominator(T)) == 1
  @assert T * A == B * T
  @assert abs(det(T)) == 1

  return fl, T, TB, TA, yy
end


function _create_com_alg(A)
  f = factor(charpoly(A))
  Ks = []
  z = CommutatorAlgebra()
  z.A = A
  z.Jblocks = []
  z.Eig = []
  z.EigAbs = []
  z.K = Ks
  for (p, e) in f
    K, a = NumberField(p, cached = false)
    push!(Ks, K)
    res = _extract_bases_of_jordan_blocks(A, K)
    push!(z.Jblocks, res)
    zz = []
    zzz = []
    for i in 1:length(res)
      v = matrix(K, 1, length(res[i][end]), res[i][end])
      push!(zz, v)
      for j in 0:(degree(K) - 1)
        push!(zzz, a^j * v)
      end
    end
    push!(z.Eig, zz)
    push!(z.EigAbs, zzz)
  end
  return z
end

function _basis_of_commutator_algebra(A)
  linind = transpose(LinearIndices(size(A)))
  cartind = cartesian_product_iterator([1:x for x in size(A)], inplace = true)
  n = nrows(A)
  z = zero_matrix(base_ring(A), n^2, n^2)
  for i in 1:n
    for j in 1:n
      for k in 1:n
        z[linind[i, j], linind[i, k]] = z[linind[i, j], linind[i, k]] + A[k, j]
        z[linind[i, j], linind[k, j]] = z[linind[i, j], linind[k, j]] - A[i, k]
      end
    end
  end
  r, K = right_kernel(z)
  res = typeof(A)[]
  for k in 1:ncols(K)
    M = zero_matrix(base_ring(A), nrows(A), ncols(A))
    for (l, v) in enumerate(cartind)
      M[v[2], v[1]] = K[l, k]
    end
    push!(res, M)
  end
  return res
end

function _basis_of_commutator_algebra(As::Vector)
  linind = transpose(LinearIndices(size(As[1])))
  cartind = cartesian_product_iterator([1:x for x in size(As[1])], inplace = true)
  n = nrows(As[1])
  zz = zero_matrix(base_ring(As[1]), 0, n^2)
  for A in As
    z = zero_matrix(base_ring(A), n^2, n^2)
    for i in 1:n
      for j in 1:n
        for k in 1:n
          z[linind[i, j], linind[i, k]] = z[linind[i, j], linind[i, k]] + A[k, j]
          z[linind[i, j], linind[k, j]] = z[linind[i, j], linind[k, j]] - A[i, k]
        end
      end
    end
    zz = vcat(zz, z)
  end
  r, K = right_kernel(zz)
  res = eltype(As)[]
  for k in 1:ncols(K)
    M = zero_matrix(base_ring(As[1]), nrows(As[1]), ncols(As[1]))
    for (l, v) in enumerate(cartind)
      M[v[2], v[1]] = K[l, k]
    end
    push!(res, M)
  end
  return res
end

function _basis_of_integral_commutator_algebra_saturate(A, B)
  linind = transpose(LinearIndices(size(A)))
  cartind = CartesianIndices(size(A))
  n = nrows(A)
  z = zero_matrix(FlintQQ, n^2, n^2)
  for i in 1:n
    for j in 1:n
      for k in 1:n
        z[linind[i, j], linind[i, k]] = FlintZZ(z[linind[i, j], linind[i, k]] + A[k, j])
        z[linind[i, j], linind[k, j]] = FlintZZ(z[linind[i, j], linind[k, j]] - B[i, k])
      end
    end
  end
  r, K = right_kernel(z)
  KK = change_base_ring(FlintZZ, denominator(K) * K)
  KK = transpose(saturate(transpose(KK)))
  res = typeof(A)[]
  for k in 1:ncols(K)
    M = zero_matrix(base_ring(A), nrows(A), ncols(A))
    for l in 1:n^2
      i1, j1 = cartind[l].I
      M[j1, i1] = KK[l, k]
    end
    @assert M * A == B * M
    push!(res, M)
  end
  return res
end

function _basis_of_integral_commutator_algebra(A, B)
  linind = transpose(LinearIndices(size(A)))
  cartind = cartesian_product_iterator([1:x for x in size(A)], inplace = true)
  n = nrows(A)
  z = zero_matrix(FlintZZ, n^2, n^2)
  for i in 1:n
    for j in 1:n
      for k in 1:n
        z[linind[i, j], linind[i, k]] = FlintZZ(z[linind[i, j], linind[i, k]] + A[k, j])
        z[linind[i, j], linind[k, j]] = FlintZZ(z[linind[i, j], linind[k, j]] - B[i, k])
      end
    end
  end
  r, K = right_kernel(z)
  res = typeof(A)[]
  for k in 1:ncols(K)
    M = zero_matrix(base_ring(A), nrows(A), ncols(A))
    for (l, v) in enumerate(cartind)
      M[v[2], v[1]] = K[l, k]
    end
    @assert M * A == B * M
    push!(res, M)
  end
  return res
end

function _induce_action(M, z::CommutatorAlgebra)
  res = []
  for i in 1:length(z.K)
    K = z.K[i]
    @show z.Eig[i]
    MEig = reduce(vcat, identity.(z.Eig[i]))
    @show MEig, M
    m = MEig * change_base_ring(K, M)
    @show m
    fl, x = can_solve_with_solution(MEig, m, side = :left)
    @assert fl
    push!(res, x)
  end
  return identity.(res)
end

function _extract_bases_of_jordan_blocks(a, K, c = gen(K))
  aK = change_base_ring(K, a)
  J, B = jordan_normal_form(aK)
  @show J
  blocks = []
  d = degree(K)
  i = 1
  while i <= nrows(a)
    b, ro, i = _get_next_jordan_block(J, i)
    @show b, ro, i
    if b != c
      continue
    end

    if degree(b) == d
      push!(blocks, (b, ro))
    end
  end
  @show blocks
  res = []
  for b in blocks
    if length(b[2]) == 0
      continue
    end
    ro = b[2]
    v = [[B[ro[r], j] for j in 1:ncols(B)] for r in 1:length(ro)]
    @assert matrix(K, 1, ncols(B), v[end]) * aK == b[1] * matrix(K, 1, ncols(B), v[end])
    push!(res, v)
  end
  
  return res
end

function _get_next_jordan_block(A, i)
  @show A, i
  i0 = i
  bad = false
  while i < nrows(A)
    if !iszero(A[i0:i, (i + 1):nrows(A)]) || !iszero(A[(i + 1):nrows(A), i0:i])
      bad = true
      i += 1
    else
      break
    end
  end

  @show i

  for j in i0:(i-1)
    for k in i0:(j-1)
      if !iszero(A[j, k])
        return A[i0, i0], [], i + 1
      end
    end
  end

  @show i

  for j in i0:i
    if A[i0, i0] != A[j, j]
      return A[i0, i0], [], i + 1
    end
  end

  @show "here2"

  for j in i0:(i-1)
    if !isone(A[j, j + 1])
      return A[i0, i0], [], i + 1
    end
  end

  @show "here"
  for j in i0:i
    for j in (i0+1):(i-1)
      @show i, j, A[i, j]
      if !iszero(A[i, j])
        return A[i0, i0], [], i + 1
      end
    end
  end

  #@show i

  i = i0
  res = [i]
  b = A[i, i]
  while i < nrows(A) && A[i, i + 1] == 1
    i += 1
    push!(res, i)
  end
  #@show res
  return b, res, i + 1
end

function _get_next_jordan_block2(A)
  # first collect the pivot entries
  pivots = Int[]
  for j in 1:nrows(A)
    k = 1
    while iszero(A[j, k])
      k += 1
    end
    push!(pivots, k)
  end

  k = 1


  #@show pivots
end

################################################################################
#
#  Lifting again
#
################################################################################

mutable struct Emat
  R
  n
  i
  j
  a
end

function matrix(e::Emat)
  z = identity_matrix(e.R, e.n)
  z[e.i, e.j] = e.a
  return z
end

inv(e::Emat) = Emat(e.R, e.n, e.i, e.j, -e.a)

function elementary_matrix(R, n, i, j, a)
  M = identity_matrix(R, n)
  M[i, j] = a
  return M
end

function _lift2(MM)
  M = deepcopy(MM)
  R = base_ring(M)
  S = _base_ring(R)
  @assert det(M) == 1
  k = 1
  n = nrows(M)
  left = []
  left2 = []
  while k < ncols(M)
    @assert det(M) == 1
    # scan the first column for a unit
    v = Int[euclid(M[i, k]) for i in k:n]
    #@show v
    if isone(minimum(abs.(v)))
      l = findfirst(isone, v) + (k - 1)
      #@show k, M
      #@show isunit(M[l, k])
      #@show M[l, k]
      if l != k
        @assert l isa Int
        #@show l
        b = M[l, k]
        #@show b
        @assert det(M) == 1
        E1 = elementary_matrix(R, n, k, l, one(R))
        E2 = elementary_matrix(R, n, l, k, -one(R))
        E3 = elementary_matrix(R, n, k, l, one(R))
        M = (E1 * E2 * E3) * M
        @assert det(M) == 1
        # push first E3
        push!(left, elementary_matrix(S, n, k, l, one(S)))
        @assert map_entries(R, left[end]) == E3
        push!(left2, Emat(S, n, k, l, one(S)))
        push!(left, elementary_matrix(S, n, l, k, -one(S)))
        push!(left2, Emat(S, n, l, k, -one(S)))
        @assert map_entries(R, left[end]) == E2
        push!(left, elementary_matrix(S, n, k, l, one(S)))
        push!(left2, Emat(S, n, k, l, one(S)))
        @assert map_entries(R, left[end]) == E1
      end
      @assert det(M) == 1
      @assert isunit(M[k, k])
      for j in (k+1):n
        if !iszero(M[j, n])
          N = deepcopy(M)
          q = divexact(M[j, k], M[k, k])
          E = elementary_matrix(R, n, j, k, -q)
          push!(left, elementary_matrix(S, n, j, k, lift(-q)))
          push!(left2, Emat(S, n, j, k, lift(-q)))
          @assert map_entries(R, left[end]) == E
          for o in 1:n
            M[j, o] = M[j, o] - q * M[k, o]
          end
          @assert E * N == M
        end
      end
      k += 1
      #@show M
    else # no unit there # I could do this in one go by putting a unit in the first position
      _, l = findmin(abs.(v)) 
      l = l + (k - 1)
      #@show l
      #@show euclid(M[l, k])
      #@show v
      for j in k:n
        if j == l
          continue
        end
        fl, _ = divides(M[j, k], M[l, k])
        if !fl
          #@show M[j, k], M[l, k]
          N = deepcopy(M)
          #@show euclid(M[j, k])
          q, r = divrem(M[j, k], M[l, k])
          #@show euclid(r)
          E = elementary_matrix(R, n, j, l, -q)
          for o in 1:n
            M[j, o] = M[j, o] - q * M[l, o]
          end
          push!(left, elementary_matrix(S, n, j, l, lift(-q)))
          push!(left2, Emat(S, n, j, l, lift(-q)))
          @assert map_entries(R, left[end]) == E
          @assert E * N == M
          break
        end
      end
    end
    @assert det(M) == 1
  end
  #println("M should now be lower triangular")
  #@show M
  @assert det(M) == 1
  # Now M is lower triangular with units on the diagonal
  #@show "here"
  for i in n:-1:2
    for j in (i - 1):-1:1
      # set jth row to jth row - M[k, j]/M[k, k] * jth row
      #@show isunit(M[i, i])
      #@show M[i, i]
      q = -divexact(M[j, i], M[i, i])
      @assert (-q) * M[i, i] == M[j, i]
      E = elementary_matrix(R, n, j, i, q)
      push!(left, elementary_matrix(S, n, j, i, lift(q)))
      push!(left2, Emat(S, n, j, i, lift(q)))
      @assert map_entries(R, left[end]) == E
      N = deepcopy(M)
      M[j, i] = M[j, i] + q * M[i, i]
      @assert E * N == M
    end
  end
  @assert det(M) == 1
  # Now sort the diagonal
  # We use this neat trick of Rosenberg, p. 60
  for i in 1:(n - 1)
    a = inv(M[i, i])
    ainv = M[i, i]
    # we multiply with (1,...1,a,a^-1,1,...1)
    E1 = elementary_matrix(R, n, i, i + 1, a)
    E2 = elementary_matrix(R, n, i + 1, i, -ainv)
    E3 = E1
    #E4 = identity_matrix(R, n)
    #E4[i, i] = 0
    #E4[i, i + 1] = -1
    #E4[i + 1, i + 1] = 0
    #E4[i + 1, i] = 1
    E5 = elementary_matrix(R, n, i, i + 1, -one(R))
    E6 = elementary_matrix(R, n, i + 1, i, one(R))
    E4 = E6

    #E4S = identity_matrix(S, n)
    #E4S[i, i] = 0
    #E4S[i, i + 1] = -1
    #E4S[i + 1, i + 1] = 0
    #E4S[i + 1, i] = 1
    E1S = elementary_matrix(S, n, i, i + 1, lift(a))
    E1SS = Emat(S, n, i, i + 1, lift(a))
    E2S = elementary_matrix(S, n, i + 1, i, lift(-ainv))
    E2SS = Emat(S, n, i + 1, i, lift(-ainv))
    E3S = E1S
    E3SS = E1SS
    E5S = elementary_matrix(S, n, i, i + 1, -one(S))
    E5SS = Emat(S, n, i, i + 1, -one(S))
    E6S = elementary_matrix(S, n, i + 1, i, one(S))
    E6SS = Emat(S, n, i + 1, i, one(S))
    E4S = E6S
    E4SS = E6SS
    push!(left, E6S)
    push!(left, E5S)
    push!(left, E4S)
    push!(left, E3S)
    push!(left, E2S)
    push!(left, E1S)
    push!(left2, E6SS)
    push!(left2, E5SS)
    push!(left2, E4SS)
    push!(left2, E3SS)
    push!(left2, E2SS)
    push!(left2, E1SS)

    M = (E1 * E2 * E3 * E4 * E5 * E6) * M
    @assert det(M) == 1
  end

  @assert isone(M)

  for i in 1:length(left)
    @assert matrix(left2[i]) == left[i]
  end

  return prod(matrix.(inv.(left2)))

  @assert map(R, prod(reverse(left))) * MM == 1

  return M, left
end

euclid(n::nmod) = gcd(n.data, modulus(parent(n)))
euclid(n::Nemo.fmpz_mod) = gcd(n.data, modulus(parent(n)))

function Base.divrem(n::T, m::T) where T <: Union{nmod,Nemo.fmpz_mod}
  @assert !iszero(m)
  R = parent(n)
  e = euclid(m)

  cp = coprime_base(fmpz[n.data, m.data, modulus(R)])::Array{fmpz, 1}

  q = Array{Tuple{fmpz, fmpz}, 1}()
  for i=1:length(cp)
    v = valuation(modulus(R), cp[i])::Int
    if v != 0
      pk = cp[i]^v
      nv = valuation(n.data % pk, cp[i])::Int
      mv = valuation(m.data % pk, cp[i])::Int
      if nv < mv
        push!(q, (pk, 0))
      else
        push!(q, (pk, divexact(n.data % pk, cp[i]^nv)))
      end
    end
  end
  qq =  R(crt([x[2] for x = q], [x[1] for x = q])::fmpz)::T
  rr = n-qq*m
  @assert n == qq*m+rr
  @assert rr == 0 || euclid(rr) < e
  return (qq,rr)::Tuple{T, T}
end

################################################################################
#
#  Generate interesting examples
#
################################################################################

function _jordan_block(R, n::Int, a)
  z = a * identity_matrix(R, n)
  for i in 1:(n - 1)
    z[i + 1, i] = 1
  end
  return z
end

function _rand_block(R, n::Int, l::Int)
  Rx, x = PolynomialRing(R, "x", cached = false)
  f = rand(Rx, n:n, -100:100)
  if !iszero(f)
    setcoeff!(f, degree(f), one(R))
  end
  while !isirreducible(f) || degree(f) != n
    f = rand(Rx, n:n, -100:100)
    if !iszero(f)
      setcoeff!(f, degree(f), one(R))
    end
  end
  return companion_matrix(f^l)
end

function _random_elementary_operations!(a; type = :rows)
  tr = type == :columns
  @assert issquare(a)
  n = nrows(a)
  d = det(a)
  if n == 1
    return a
  end
  i = rand(1:n)
  j = rand(1:n)
  while j == i
    j = rand(1:n)
  end

  r = rand(base_ring(a), -10:10)
  for k in 1:n
    if tr
      a[k, i] = a[k, i] + r * a[k, j]
    else
      a[i, k] = a[i, k] + r * a[j, k]
    end
  end
  @assert d == det(a)
  return a
end

function _random_sln(R, n; num_op = 10)
  a = identity_matrix(R, n)
  for i in 1:num_op
    _random_elementary_operations!(a; type = rand() < 0.5 ? :rows : :columns)
  end
  return a
end

function _random_matrix(R, block_shape)
  matrices = dense_matrix_type(R)[]
  for (r, l, ll) in block_shape
    B = _rand_block(R, r, l)
    for j in 1:ll
      push!(matrices, B)
    end
  end
  return diagonal_matrix(matrices)
end

function _similarity_test_setup(R, n; max_block = 4)
  block_shape = Tuple{Int, Int, Int}[]
  nn = n
  while !iszero(nn)
    #@show nn
    r = min(rand(1:nn), max_block)
    #@show r
    l = max(Int(floor(nn/r)), 1)
    nbl = rand(1:l)
    #@show nbl
    nnn = nn - r * nbl
    ll = max(Int(floor(nnn/(r * nbl))), 1)
    nbll = rand(1:ll)
    #@show nbll
    push!(block_shape, (r, nbl, nbll))
    nn = nn - r * nbl *  nbll
  end
  b = block_shape
  #@show block_shape
  A = _random_matrix(R, block_shape)
  z = _random_sln(R, n)
  @assert isone(det(z))
  zinv = inv(z)
  B = z * A * zinv
  return A, B
end

################################################################################
#
#  Redoing the Jordan decomposition thing
#
################################################################################

function _get_morphism(A::fmpq_mat)
  Qx = Hecke.Globals.Qx
  x = gen(Qx)
  Ax = x - change_base_ring(Qx, A)
  S, _, T = snf_with_transform(Ax)
  return T, diagonal(S)
end

mutable struct CommutatorAlgebra2
  A::fmpq_mat
  T::Generic.MatSpaceElem{fmpq_poly}
  Tinv::Generic.MatSpaceElem{fmpq_poly}
  el::Vector{fmpq_poly}
  invariant_factors::Vector{Vector{fmpq_poly}}
  invariant_factors_squarefree::Vector{Vector{fmpq_poly}}
  invariant_factors_grouped::Vector{Tuple{fmpq_poly, AnticNumberField, Vector{Tuple{Int, Int}}}}
  irreducible_factors::Vector{Tuple{fmpq_poly, AnticNumberField, Vector{Tuple{Int, Int}}}}

  function CommutatorAlgebra2(A)
    z = new()
    z.A = A
    return z
  end
end

matrix(C::CommutatorAlgebra2) = C.A

dim(C::CommutatorAlgebra2) = nrows(matrix(C))

function _compute_decomposition!(C::CommutatorAlgebra2)
  A = matrix(C)
  Qx = Hecke.Globals.Qx
  x = gen(Qx)
  Ax = x - change_base_ring(Qx, A)
  S, _ , T = snf_with_transform(Ax)
  n = nrows(A)
  el = diagonal(S)
  Tinv = inv(T)
  C.el = el
  C.T = T
  C.Tinv = Tinv

  # Consistency check
  for i in 1:10
    _w = [rand(Qx, 1:5, 1:5) % C.el[i] for i in 1:n]
    v = Hecke._first_map_backward(_w, C)
    @assert Hecke._first_map_forward(v, C) == _w

    v = matrix(Hecke.Globals.QQ, 1, n, [rand(-10:10) for i in 1:n])
    w = Hecke._first_map_forward(v, C)
    @assert Hecke._first_map_backward(w, C) == v
  end

  invariant_factors = Vector{Vector{fmpq_poly}}()

  invariant_factors_squarefree = Vector{Vector{fmpq_poly}}()

  irreducible_factors = Tuple{fmpq_poly, AnticNumberField, Vector{Tuple{Int, Int}}}[]

  for i in 1:length(C.el)
    fac = factor(C.el[i])
    @show fac
    inv_fac = Vector{fmpq_poly}()
    sqf = Vector{fmpq_poly}()
    j = 1
    for (p, e) in fac
      push!(sqf, inv(leading_coefficient(p)) * p)
      g = sqf[end]

      k = findfirst(x -> isequal(x[1], g), irreducible_factors)
      if k isa Int
        push!(irreducible_factors[k][3], (i, j))
      else
        K,  = NumberField(g, cached = false)
        push!(irreducible_factors, (g, K, Tuple{Int, Int}[(i, j)]))
      end

      push!(inv_fac, (inv(leading_coefficient(p)) * p)^e)
      j += 1
    end
    push!(invariant_factors, inv_fac)
    push!(invariant_factors_squarefree, sqf)
  end

  C.invariant_factors = invariant_factors

  C.invariant_factors_squarefree = invariant_factors_squarefree

  C.irreducible_factors = irreducible_factors

  for i in 1:10
    _w = [rand(Qx, 1:5, 1:5) % C.el[i] for i in 1:n]
    v = Hecke._second_map_forward(_w, C)
    @assert Hecke._second_map_backward(v, C) == _w
  end

  for i in 1:10
    _w = [[rand(Qx, 1:5, 1:5) % C.invariant_factors_squarefree[i][j] for j in 1:length(C.invariant_factors[i])] for i in 1:dim(C)]
    _v = Hecke._third_map_forward(_w, C)
    @assert Hecke._third_map_backward(_v, C) == _w
  end

  for i in 1:10
    _w = [[rand(Qx, 1:5, 1:5) % C.invariant_factors_squarefree[i][j] for j in 1:length(C.invariant_factors[i])] for i in 1:dim(C)]
    _v = Hecke._fourth_map_forward(_w, C)
    @assert Hecke._fourth_map_backward(_v, C) == _w
  end
end

function _first_map_forward(w::fmpq_mat, C::CommutatorAlgebra2)
  v = change_base_ring(Hecke.Globals.Qx, w) * C.T
  return elem_type(base_ring(v))[v[1, i] % C.el[i] for i in 1:dim(C)]
end

function _first_map_backward(v::Vector{fmpq_poly}, C::CommutatorAlgebra2)
  A = matrix(C)
  n = dim(C)
  _w = matrix(Hecke.Globals.Qx, 1, n, v)
  w = _w * C.Tinv
  z = zero_matrix(Hecke.Globals.QQ, 1, n)
  for i in 1:n
    B = w[i](A)
    for j in 1:n
      z[1, j] += B[i, j]
    end
  end
  return z
end

function _second_map_forward(v::Vector{fmpq_poly}, C::CommutatorAlgebra2)
  z = Vector{Vector{fmpq_poly}}()
  for i in 1:length(v)
    if length(C.invariant_factors[i]) == 0
      push!(z, fmpq_poly[])
    else
      push!(z, fmpq_poly[v[i] % C.invariant_factors[i][j] for j in 1:length(C.invariant_factors[i])])
    end
  end
  return z
end

function _second_map_backward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra2)
  n = dim(C)
  w = Vector{fmpq_poly}()
  for i in 1:n
    if length(C.invariant_factors[i]) == 0
      push!(w, zero(Hecke.Globals.Qx))
    else
      push!(w, crt(v[i], C.invariant_factors[i]))
    end
  end
  return w
end

function _third_map_forward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra2)
  w = Vector{Vector{fmpq_poly}}(undef, length(v))
  for i in 1:length(v)
    w[i] = fmpq_poly[]
  end

  for i in 1:length(v)
    w[i] = Vector{fmpq_poly}(undef, length(v[i]))
    @assert length(v[i]) == length(C.invariant_factors_squarefree[i])
    for j in 1:length(v[i])
      w[i][j] = v[i][j] % C.invariant_factors_squarefree[i][j]
    end
  end

  return w
end

function _third_map_backward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra2)
  return deepcopy(v)
end

function _fourth_map_forward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra2)
  z = Vector{Vector{nf_elem}}(undef, length(C.irreducible_factors))
  for l in 1:length(C.irreducible_factors)
    K = C.irreducible_factors[l][2]
    zz = nf_elem[]
    for (i, j) in C.irreducible_factors[l][3]
      push!(zz, K(v[i][j]))
    end
    z[l] = zz
  end
  return z
end

function _fourth_map_backward(v::Vector{Vector{nf_elem}}, C::CommutatorAlgebra2)
  z = Vector{Vector{fmpq_poly}}(undef, dim(C))
  for i in 1:dim(C)
    z[i] = Vector{fmpq_poly}(undef, length(C.invariant_factors_squarefree[i]))
  end

  for l in 1:length(C.irreducible_factors)
    K = C.irreducible_factors[l][2]
    k = 1
    for (i, j) in C.irreducible_factors[l][3]
      z[i][j] = Hecke.Globals.Qx(v[l][k])
      k += 1
    end
  end
  return z
end

function _std_basis_vector(C::CommutatorAlgebra2, i::Int, j::Int)
  z = Vector{Vector{nf_elem}}()
  @assert 1 <= i <= length(C.irreducible_factors)
  @assert 1 <= j <= length(C.irreducible_factors[i][3])
  for k in 1:length(C.irreducible_factors)
    push!(z, zeros(C.irreducible_factors[k][2], length(C.irreducible_factors[k][3])))
  end
  z[i][j] = one(C.irreducible_factors[i][2])
  return z
end

function _from_number_fields(v::Vector{Vector{nf_elem}}, C::CommutatorAlgebra2)
  return _first_map_backward(_second_map_backward(_third_map_backward(_fourth_map_backward(v, C), C), C), C)
end

function _to_number_fields(v::fmpq_mat, C::CommutatorAlgebra2)
  return _fourth_map_forward(_third_map_forward(_second_map_forward(_first_map_forward(v, C), C), C), C)
end

function _decomposition_type(C::CommutatorAlgebra2)
  l = length(C.irreducible_factors)
  return AnticNumberField[C.irreducible_factors[i][2] for i in 1:l],
         Int[length(C.irreducible_factors[i][3]) for i in 1:l]
end

function _induce_action(C::CommutatorAlgebra2, M)
  res = dense_matrix_type(nf_elem)[]
  for i in 1:length(C.irreducible_factors)
    n = length(C.irreducible_factors[i][3])
    z = zero_matrix(C.irreducible_factors[i][2], n, n)
    for j in 1:length(C.irreducible_factors[i][3])
      s = _std_basis_vector(C, i, j)
      #@show s
      v = _from_number_fields(s, C)
      #@show v
      w = v * M
      ww = _to_number_fields(w, C)
      #@show ww
      for k in 1:n
        z[j, k] = ww[i][k]
      end
    end
    push!(res, z)
  end
  return res
end

# Third try

mutable struct CommutatorAlgebra3
  A::fmpq_mat
  T::Generic.MatSpaceElem{fmpq_poly}
  Tinv::Generic.MatSpaceElem{fmpq_poly}
  el::Vector{fmpq_poly}
  invariant_factors::Vector{Vector{fmpq_poly}}
  invariant_factors_factored::Vector{Vector{fmpq_poly}}
  invariant_factors_grouped::Vector{Tuple{fmpq_poly, AnticNumberField, Vector{Tuple{Int, Int, Int}}}}
  invariant_factors_grouped_grouped::Vector{Vector{Tuple{Int, Vector{Tuple{Int, Int}}}}}
  irreducible_factors::Vector{Tuple{fmpq_poly, AnticNumberField, Vector{Tuple{Int, Int}}}}

  function CommutatorAlgebra3(A)
    z = new()
    z.A = A
    return z
  end
end

matrix(C::CommutatorAlgebra3) = C.A

dim(C::CommutatorAlgebra3) = nrows(matrix(C))

function _compute_decomposition!(C::CommutatorAlgebra3)
  A = matrix(C)
  Qx = Hecke.Globals.Qx
  x = gen(Qx)
  Ax = x - change_base_ring(Qx, A)
  S, _ , T = snf_with_transform(Ax)
  n = nrows(A)
  el = diagonal(S)
  Tinv = inv(T)
  C.el = el
  C.T = T
  C.Tinv = Tinv

  # Consistency check
  for i in 1:10
    _w = [rand(Qx, 1:5, 1:5) % C.el[i] for i in 1:n]
    v = Hecke._first_map_backward(_w, C)
    @assert Hecke._first_map_forward(v, C) == _w

    v = matrix(Hecke.Globals.QQ, 1, n, [rand(-10:10) for i in 1:n])
    w = Hecke._first_map_forward(v, C)
    @assert Hecke._first_map_backward(w, C) == v
  end

  invariant_factors = Vector{Vector{fmpq_poly}}()

  invariant_factors_factored = Vector{Vector{fmpq_poly}}()

  invariant_factors_grouped = Vector{Tuple{fmpq_poly, AnticNumberField, Vector{Tuple{Int, Int, Int}}}}()

  invariant_factors_grouped_grouped = Vector{Tuple{Int, Vector{Tuple{Int, Int}}}}[]

  for i in 1:length(C.el)
    fac = factor(C.el[i])
    #@show fac
    inv_fac = Vector{fmpq_poly}()
    factored = Vector{fmpq_poly}()
    j = 1
    for (p, e) in fac
      push!(factored, inv(leading_coefficient(p)) * p^e)

      k = findfirst(x -> isequal(x[1], p), invariant_factors_grouped)
      if k isa Int
        push!(invariant_factors_grouped[k][3], (i, j, e))
      else
        K,  = NumberField(p, cached = false)
        push!(invariant_factors_grouped, (p, K, Tuple{Int, Int, Int}[(i, j, e)]))
      end

      push!(inv_fac, (inv(leading_coefficient(p)) * p)^e)
      j += 1
    end
    push!(invariant_factors_factored, factored)
  end

  for l in 1:length(invariant_factors_grouped)
    D = Tuple{Int, Vector{Tuple{Int, Int}}}[]
    M = invariant_factors_grouped[l][3]
    for (i, j, e) in M
      o = findfirst(x -> x[1] == e, D)
      if o == nothing
        push!(D, (e, Tuple{Int, Int}[(i, j)]))
      else
        push!(D[o][2], (i, j))
      end
    end
    push!(invariant_factors_grouped_grouped, D)
  end

  #@show invariant_factors_grouped_grouped

  C.invariant_factors_factored = invariant_factors_factored

  C.invariant_factors_grouped = invariant_factors_grouped

  C.invariant_factors_grouped_grouped = invariant_factors_grouped_grouped

  for i in 1:10
    _w = [rand(Qx, 1:5, 1:5) % C.el[i] for i in 1:n]
    v = Hecke._second_map_forward(_w, C)
    @assert Hecke._second_map_backward(v, C) == _w
  end

  for i in 1:10
    _w = [[rand(Qx, 1:5, 1:5) % C.invariant_factors_factored[i][j] for j in 1:length(C.invariant_factors_factored[i])] for i in 1:dim(C)]
    _v = Hecke._third_map_forward(_w, C)
    @assert Hecke._third_map_backward(_v, C) == _w
  end

  #for i in 1:10
  #  _w = [[rand(Qx, 1:5, 1:5) % C.invariant_factors_squarefree[i][j] for j in 1:length(C.invariant_factors[i])] for i in 1:dim(C)]
  #  _v = Hecke._fourth_map_forward(_w, C)
  #  @assert Hecke._fourth_map_backward(_v, C) == _w
  #end
end

function _first_map_forward(w::fmpq_mat, C::CommutatorAlgebra3)
  v = change_base_ring(Hecke.Globals.Qx, w) * C.T
  return elem_type(base_ring(v))[v[1, i] % C.el[i] for i in 1:dim(C)]
end

function _first_map_backward(v::Vector{fmpq_poly}, C::CommutatorAlgebra3)
  A = matrix(C)
  n = dim(C)
  _w = matrix(Hecke.Globals.Qx, 1, n, v)
  w = _w * C.Tinv
  z = zero_matrix(Hecke.Globals.QQ, 1, n)
  for i in 1:n
    B = w[i](A)
    for j in 1:n
      z[1, j] += B[i, j]
    end
  end
  return z
end

function _second_map_forward(v::Vector{fmpq_poly}, C::CommutatorAlgebra3)
  z = Vector{Vector{fmpq_poly}}()
  for i in 1:length(v)
    if length(C.invariant_factors_factored[i]) == 0
      push!(z, fmpq_poly[])
    else
      push!(z, fmpq_poly[v[i] % C.invariant_factors_factored[i][j] for j in 1:length(C.invariant_factors_factored[i])])
    end
  end
  return z
end

function _second_map_backward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra3)
  n = dim(C)
  w = Vector{fmpq_poly}()
  for i in 1:n
    if length(C.invariant_factors_factored[i]) == 0
      push!(w, zero(Hecke.Globals.Qx))
    else
      push!(w, crt(v[i], C.invariant_factors_factored[i]))
    end
  end
  return w
end

#function _third_map_forward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra3)
#  w = Vector{Vector{fmpq_poly}}(undef, length(v))
#  for i in 1:length(v)
#    w[i] = fmpq_poly[]
#  end
#
#  for i in 1:length(v)
#    w[i] = Vector{fmpq_poly}(undef, length(v[i]))
#    @assert length(v[i]) == length(C.invariant_factors_squarefree[i])
#    for j in 1:length(v[i])
#      w[i][j] = v[i][j] % C.invariant_factors_squarefree[i][j]
#    end
#  end
#
#  return w
#end
#
#function _third_map_backward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra3)
#  return deepcopy(v)
#end
#
function _third_map_forward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra3)
  z = Vector{Vector{fmpq_poly}}(undef, length(C.invariant_factors_grouped))
  for l in 1:length(C.invariant_factors_grouped)
    zz = fmpq_poly[]
    for (i, j) in C.invariant_factors_grouped[l][3]
      push!(zz, v[i][j])
    end
    z[l] = zz
  end
  return z
end

function _third_map_backward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra3)
  z = Vector{Vector{fmpq_poly}}(undef, dim(C))
  for i in 1:dim(C)
    z[i] = Vector{fmpq_poly}(undef, length(C.invariant_factors_factored[i]))
  end

  for l in 1:length(C.invariant_factors_grouped)
    k = 1
    for (i, j) in C.invariant_factors_grouped[l][3]
      z[i][j] = v[l][k]
      k += 1
    end
  end
  return z
end

function _std_basis_vector(C::CommutatorAlgebra3, i::Int, j::Int)
  z = Vector{Vector{fmpq_poly}}()
  @assert 1 <= i <= length(C.invariant_factors_grouped)
  @assert 1 <= j <= length(C.invariant_factors_grouped[i][3])
  for k in 1:length(C.invariant_factors_grouped)
    push!(z, zeros(Hecke.Globals.Qx, length(C.invariant_factors_grouped[k][3])))
  end
  z[i][j] = one(Hecke.Globals.Qx)
  return z
end

function _from_std_basis(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra3)
  return _first_map_backward(_second_map_backward(_third_map_backward(v, C), C), C)
end

function _to_std_basis(v::fmpq_mat, C::CommutatorAlgebra3)
  return _third_map_forward(_second_map_forward(_first_map_forward(v, C), C), C)
end

function _decomposition_type(C::CommutatorAlgebra3)
  l = length(C.invariant_factors_grouped)
  fields = AnticNumberField[]
  degs = Int[]
  for i in 1:l
    for (e, inds) in C.invariant_factors_grouped_grouped[i]
      push!(fields, C.invariant_factors_grouped[i][2])
      push!(degs, length(inds))
    end
  end

  return fields, degs
end

function _induce_action(C::CommutatorAlgebra3, M)
  res = dense_matrix_type(fmpq_poly)[]
  @assert M * C.A == C.A * M
  for i in 1:length(C.invariant_factors_grouped)
    n = length(C.invariant_factors_grouped[i][3])
    z = zero_matrix(Hecke.Globals.Qx, n, n)
    for j in 1:length(C.invariant_factors_grouped[i][3])
      s = _std_basis_vector(C, i, j)
      v = _from_std_basis(s, C)
      w = v * M
      ww = _to_std_basis(w, C)
      for k in 1:n
        z[j, k] = ww[i][k]
      end
    end
    push!(res, z)
  end
  return res
end

function _induce_action_mod(C::CommutatorAlgebra3, N)
  res = dense_matrix_type(nf_elem)[]
  ac = _induce_action(C, N)
  for i in 1:length(C.invariant_factors_grouped)
    z = ac[i]
    #@show z
    #for k in 1:length(C.invariant_factors_grouped[i][3])
    #  for l in 1:length(C.invariant_factors_grouped[i][3])
    #    @assert iszero(z[k, l]) || valuation(z[k, l], C.invariant_factors_grouped[i][1]) >= C.invariant_factors_grouped[i][3][l][3] - min(C.invariant_factors_grouped[i][3][l][3], C.invariant_factors_grouped[i][3][k][3])
    #    z[k, l] = divexact(z[k, l], C.invariant_factors_grouped[i][1]^(C.invariant_factors_grouped[i][3][l][3] - min(C.invariant_factors_grouped[i][3][l][3], C.invariant_factors_grouped[i][3][k][3])))
    #  end
    #end
    k = 1
    for (e, inds) in C.invariant_factors_grouped_grouped[i]
      #@show e, inds
      l = length(inds)
      zz = sub(z, (k):(k + l - 1), (k):(k + l - 1))
      k = k + l
      push!(res, map_entries(C.invariant_factors_grouped[i][2], zz))
    end
  end
  return res
end

# Element which is failing:
# A = matrix(FlintQQ, 10, 10, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -49, 0, -42, 14, -9, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])
#
#
# A = matrix(FlintQQ, 10, 10, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 9, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 9, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, -7, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6])
#
# This gives the right_order assertion:
#
# A = matrix(FlintQQ, 6, 6, [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -125, -75, -15, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, -5])
# B = matrix(FlintQQ, 6, 6, [-22910, 2266, 45832, 2658, 1285, -226465, -16600, 1660, 33621, 17622, 350, -168655, -11375, 1125, 22750, 1080, 625, -112400, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 7, 0, -150, 15, 303, 126, 0, -1520])
#
# A = matrix(FlintQQ, 5, 5, [0, 1, 0, 0, 0, -81, -18, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, -9]])
#
# B = matrix(FlintQQ, 5, 5, 15054, 1, -105441, -149944, -5019, 21417, -15, -149919, -212937, -7151, 1254, 0, -8787, -12480, -418, 627, 0, -4389, -6249, -209, 108, 3, -756, -1179, -39])
#
# julia> Hecke._eltseq(A) |> print
# fmpz[0, 1, 0, 0, 0, 0, 1, 0, -343, -147, -21, 0, 0, 0, 0, -7]
# julia> Hecke._eltseq(B) |> print
# fmpz[-39277, -17864, -773376, 225560, -2841374, -1292556, -55957655, 16320401, -405524, -184499, -7988112, 2329751, -1622301, -738076, -31955520, 9319917]
#
# A = matrix(FlintQQ, 3, 3, [0, 1, 0, -1, 2, 0, 0, 0, 1])
#
# B = matrix(FlintQQ, 3, 3, [-2959757959, -15202918, 41804175660, -153800, -789, 2172300, -209552500, -1076375, 2959758751])
#
# B = matrix(FlintQQ, 3, 3, [-1, 2, 2, -1, 2, 1, -1, 1, 2])
