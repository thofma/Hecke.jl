################################################################################
#
#  Commutator algebra
#
################################################################################

export is_GLZ_conjugate

# Given a square matrix A, determine the algebra C_A = {X | XA = AX }
# and its semisimple reduction
#
# This is mainly for dealing with the isomorphism C_A \cong \End_Q[x](Q^n)
# and the surjection to the semisimplification.
mutable struct CommutatorAlgebra
  A::fmpq_mat
  T::Generic.MatSpaceElem{fmpq_poly}
  Tinv::Generic.MatSpaceElem{fmpq_poly}
  el::Vector{fmpq_poly}
  invariant_factors::Vector{Vector{fmpq_poly}}
  invariant_factors_factored::Vector{Vector{fmpq_poly}}
  invariant_factors_grouped::Vector{Tuple{fmpq_poly,
                                          AnticNumberField,
                                          Vector{Tuple{Int, Int, Int}}}}
  invariant_factors_grouped_grouped::Vector{Vector{Tuple{Int, Vector{Tuple{Int, Int}}}}}
  irreducible_factors::Vector{Tuple{fmpq_poly,
                                    AnticNumberField,
                                    Vector{Tuple{Int, Int}}}}

  function CommutatorAlgebra(A)
    z = new()
    z.A = A
    return z
  end
end

matrix(C::CommutatorAlgebra) = C.A

dim(C::CommutatorAlgebra) = nrows(matrix(C))

function _compute_decomposition!(C::CommutatorAlgebra)
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
  @hassert :Conjugacy 1 begin
    for i in 1:10
      _w = [rand(Qx, 1:5, 1:5) % C.el[i] for i in 1:n]
      v = Hecke._first_map_backward(_w, C)
      @assert Hecke._first_map_forward(v, C) == _w

      v = matrix(Hecke.Globals.QQ, 1, n, [rand(-10:10) for i in 1:n])
      w = Hecke._first_map_forward(v, C)
      @assert Hecke._first_map_backward(w, C) == v
    end
    true
  end

  invariant_factors = Vector{Vector{fmpq_poly}}()

  invariant_factors_factored = Vector{Vector{fmpq_poly}}()

  invariant_factors_grouped = Vector{Tuple{fmpq_poly,
                                           AnticNumberField,
                                           Vector{Tuple{Int, Int, Int}}}}()

  invariant_factors_grouped_grouped = Vector{Tuple{Int,
                                                   Vector{Tuple{Int, Int}}}}[]

  for i in 1:length(C.el)
    fac = factor(C.el[i])::Fac{fmpq_poly}
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

  C.invariant_factors_factored = invariant_factors_factored

  C.invariant_factors_grouped = invariant_factors_grouped

  C.invariant_factors_grouped_grouped = invariant_factors_grouped_grouped

  @hassert :Conjugacy 1 begin
    for i in 1:10
      _w = fmpq_poly[rand(Qx, 1:5, 1:5) % C.el[i] for i in 1:n]
      v = Hecke._second_map_forward(_w, C)
      @assert Hecke._second_map_backward(v, C) == _w
    end

    for i in 1:10
      _w = [fmpq_poly[rand(Qx, 1:5, 1:5) % C.invariant_factors_factored[i][j]
               for j in 1:length(C.invariant_factors_factored[i])]
               for i in 1:dim(C)]
      _v = Hecke._third_map_forward(_w, C)
      @assert Hecke._third_map_backward(_v, C) == _w
    end
    true
  end

  return C
end

function _first_map_forward(w::fmpq_mat, C::CommutatorAlgebra)
  v = change_base_ring(Hecke.Globals.Qx, w) * C.T
  return elem_type(base_ring(v))[v[1, i] % C.el[i] for i in 1:dim(C)]
end

function _first_map_backward(v::Vector{fmpq_poly}, C::CommutatorAlgebra)
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

function _second_map_forward(v::Vector{fmpq_poly}, C::CommutatorAlgebra)
  z = Vector{Vector{fmpq_poly}}()
  for i in 1:length(v)
    if length(C.invariant_factors_factored[i]) == 0
      push!(z, fmpq_poly[])
    else
      push!(z, fmpq_poly[v[i] % C.invariant_factors_factored[i][j]
                           for j in 1:length(C.invariant_factors_factored[i])])
    end
  end
  return z
end

function _second_map_backward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra)
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

function _third_map_forward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra)
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

function _third_map_backward(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra)
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

function _std_basis_vector(C::CommutatorAlgebra, i::Int, j::Int)
  z = Vector{Vector{fmpq_poly}}()
  @assert 1 <= i <= length(C.invariant_factors_grouped)
  @assert 1 <= j <= length(C.invariant_factors_grouped[i][3])
  for k in 1:length(C.invariant_factors_grouped)
    push!(z, zeros(Hecke.Globals.Qx, length(C.invariant_factors_grouped[k][3])))
  end
  z[i][j] = one(Hecke.Globals.Qx)
  return z
end

function _from_std_basis(v::Vector{Vector{fmpq_poly}}, C::CommutatorAlgebra)
  return _first_map_backward(
            _second_map_backward(_third_map_backward(v, C), C), C)
end

function _to_std_basis(v::fmpq_mat, C::CommutatorAlgebra)
  return _third_map_forward(_second_map_forward(_first_map_forward(v, C), C), C)
end

function _decomposition_type(C::CommutatorAlgebra)
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

function _induce_action(C::CommutatorAlgebra, M)
  res = dense_matrix_type(fmpq_poly)[]
  @hassert :Conjugacy 1 M * matrix(C) == matrix(C) * M
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

function _induce_action_mod(C::CommutatorAlgebra, N)
  res = dense_matrix_type(nf_elem)[]
  ac = _induce_action(C, N)
  for i in 1:length(C.invariant_factors_grouped)
    z = ac[i]
    k = 1
    for (e, inds) in C.invariant_factors_grouped_grouped[i]
      l = length(inds)
      zz = sub(z, (k):(k + l - 1), (k):(k + l - 1))
      k = k + l
      push!(res, map_entries(C.invariant_factors_grouped[i][2], zz))
    end
  end
  return res
end

################################################################################
#
#  General approach
#
################################################################################

@doc doc"""
    is_GLZ_conjugate(A::MatElem, B::MatElem) -> Bool, MatElem

Given two integral or rational matrices, determine whether there exists an
invertible integral matrix $T$ with $TA = BT$. If true, the second argument
is such a matrix $T$. Otherwise, the second argument is unspecified.

```jldoctest
julia> A = matrix(ZZ, 4, 4, [ 0, 1,  0, 0,
                             -4, 0,  0, 0,
                              0, 0,  0, 1,
                              0, 0, -4, 0]);

julia> B = matrix(ZZ, 4, 4,  [ 0, 1,  4,  0,
                              -4, 0,  0, -4,
                               0, 0,  0,  1,
                               0, 0, -4,  0]);

julia> fl, T = is_GLZ_conjugate(A, B);

julia> isone(abs(det(T))) && T * A == B * T
true
```
"""
is_GLZ_conjugate(A::Union{fmpz_mat, fmpq_mat}, B::Union{fmpz_mat, fmpq_mat})

function is_GLZ_conjugate(A::fmpz_mat, B::fmpz_mat)
  AQ = change_base_ring(FlintQQ, A)
  BQ = change_base_ring(FlintQQ, B)
  return _isGLZ_conjugate_integral(AQ, BQ)
end

function is_GLZ_conjugate(A::fmpq_mat, B::fmpq_mat)
  d = lcm(denominator(A), denominator(B))
  return _isGLZ_conjugate_integral(d*A, d*B)
end

function _isGLZ_conjugate_integral(A::fmpq_mat, B::fmpq_mat)
  if nrows(A) != nrows(B)
    return false, zero_matrix(FlintZZ, 0, 0)
  end

  if A == B
    return true, identity_matrix(FlintZZ, nrows(A))
  end

  CA, TA = rational_canonical_form(A)
  CB, TB = rational_canonical_form(B)

  if CA != CB
    return false, zero_matrix(FlintZZ, 0, 0)
  end

  Z = CommutatorAlgebra(A)
  _compute_decomposition!(Z)
  Ks, ns = _decomposition_type(Z)
  AA = _matrix_algebra(Ks, ns)
  O = _basis_of_integral_commutator_algebra(A, A)
  I = _basis_of_integral_commutator_algebra(A, B)
  @vprint :Conjugacy 1 "Algebra has dimension $(length(O))\n"
  @vprint :Conjugacy 1 "Semisimple quotient has dimension $(dim(AA))\n"
  ordergens = elem_type(AA)[]
  idealgens = elem_type(AA)[]
  dec = decompose(AA)

  _C = inv(TB) * TA

  @assert _C * A == B * _C

  invC = inv(_C)

  for bb in O
    b = _induce_action_mod(Z, bb)
    z = zero(AA)
    @assert length(dec) == length(b)
    for i in 1:length(dec)
      BB, mB = dec[i]::Tuple{AlgAss{fmpq},
                             AbsAlgAssMor{AlgAss{fmpq},AlgAss{fmpq},fmpq_mat}}
      local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
      C, BtoC = BB.isomorphic_full_matrix_algebra
      z = z + mB(preimage(BtoC, C(b[i]))::elem_type(BB))
    end
    push!(ordergens, z)
  end

  for bb in I
    b = _induce_action_mod(Z, invC * bb)
    z = zero(AA)
    @assert length(dec) == length(b)
    for i in 1:length(dec)
      BB, mB = dec[i]::Tuple{AlgAss{fmpq},
                             AbsAlgAssMor{AlgAss{fmpq},AlgAss{fmpq},fmpq_mat}}
      local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
      C, BtoC = BB.isomorphic_full_matrix_algebra
      z = z + mB(preimage(BtoC, C(b[i]))::elem_type(BB))
    end
    push!(idealgens, z)
  end

  OO = Order(AA, ordergens)
  OI = ideal_from_lattice_gens(AA, idealgens)
  @hassert :Conjugacy 1 OO == right_order(OI)
  @vprint :Conjugacy 1 "Testing if ideal is principal...\n"
  fl, y = _isprincipal(OI, OO, :right)::Tuple{Bool,
                                              AlgAssElem{fmpq,AlgAss{fmpq}}}

  if !fl
    return false, zero_matrix(FlintZZ, 0, 0)
  end

  @hassert :Conjugacy 1 y * OO == OI

  # I know invC * I maps surjectively onto OI
  # Let's lift the generator y

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

  fl, vv = can_solve_with_solution(Y, YY, side = :left)
  @assert fl
  yy = zero_matrix(FlintQQ, nrows(A), nrows(A))
  for i in 1:length(vv)
    yy = yy + vv[1, i] * (invC * I[i])
  end

  T = _C * yy

  @assert abs(denominator(T)) == 1
  @assert T * A == B * T

  # this is the second step
  if abs(det(T)) != 1
    return false, zero_matrix(ZZ, 0, 0)
  end

  return fl, map_entries(FlintZZ, T)
end

################################################################################
#
#  Computation of commutator algebras
#
################################################################################

_basis_of_commutator_algebra(A) = _basis_of_commutator_algebra(A, A)

_basis_of_commutator_algebra(As::Vector) = _basis_of_commutator_algebra(A, A)

function _basis_of_integral_commutator_algebra(A::fmpq_mat, B::fmpq_mat)
  # Compute using saturation
  @assert isone(denominator(A))
  @assert isone(denominator(A))
  linind = transpose(LinearIndices(size(A)))
  n = nrows(A)
  z = zero_matrix(FlintQQ, n^2, n^2)
  for i in 1:n
    for j in 1:n
      for k in 1:n
        z[linind[i, j], linind[i, k]] = FlintZZ(z[linind[i, j], linind[i, k]] +
                                                                        A[k, j])
        z[linind[i, j], linind[k, j]] = FlintZZ(z[linind[i, j], linind[k, j]] -
                                                                        B[i, k])
      end
    end
  end
  r, K = right_kernel(z)
  KK = change_base_ring(FlintZZ, denominator(K) * K)
  KK = transpose(saturate(transpose(KK)))
  res = typeof(A)[]
  for k in 1:ncols(K)
    cartind = CartesianIndices(size(A))
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

function _basis_of_commutator_algebra(A::MatElem, B::MatElem)
  linind = transpose(LinearIndices(size(A)))
  n = nrows(A)
  z = zero_matrix(base_ring(A), n^2, n^2)
  for i in 1:n
    for j in 1:n
      for k in 1:n
        z[linind[i, j], linind[i, k]] = FlintZZ(z[linind[i, j], linind[i, k]] +
                                                                        A[k, j])
        z[linind[i, j], linind[k, j]] = FlintZZ(z[linind[i, j], linind[k, j]] -
                                                                        B[i, k])
      end
    end
  end
  r, K = right_kernel(z)
  res = typeof(A)[]
  for k in 1:ncols(K)
    cartind = cartesian_product_iterator([1:x for x in size(A)], inplace = true)
    M = zero_matrix(base_ring(A), nrows(A), ncols(A))
    for (l, v) in enumerate(cartind)
      M[v[2], v[1]] = K[l, k]
    end
    @assert M * A == B * M
    push!(res, M)
  end
  return res
end

function _basis_of_commutator_algebra(As::Vector, Bs::Vector)
  linind = transpose(LinearIndices(size(As[1])))
  n = nrows(As[1])
  zz = zero_matrix(base_ring(As[1]), 0, n^2)
  for (A, B) in zip(As, Bs)
    z = zero_matrix(base_ring(A), n^2, n^2)
    for i in 1:n
      for j in 1:n
        for k in 1:n
          z[linind[i, j], linind[i, k]] = z[linind[i, j], linind[i, k]] +
                                                                        A[k, j]
          z[linind[i, j], linind[k, j]] = z[linind[i, j], linind[k, j]] -
                                                                        B[i, k]
        end
      end
    end
    zz = vcat(zz, z)
  end
  r, K = right_kernel(zz)
  res = eltype(As)[]
  for k in 1:ncols(K)
    cartind = cartesian_product_iterator([1:x for x in size(As[1])],
                                         inplace = true)
    M = zero_matrix(base_ring(As[1]), nrows(As[1]), ncols(As[1]))
    for (l, v) in enumerate(cartind)
      M[v[2], v[1]] = K[l, k]
    end
    push!(res, M)
  end
  return res
end

function _basis_of_integral_commutator_algebra(As::Vector{fmpq_mat},
                                               Bs::Vector{fmpq_mat})
  # Compute using saturation
  @assert all(x -> isone(denominator(x)), As)
  @assert all(x -> isone(denominator(x)), Bs)
  linind = transpose(LinearIndices(size(As[1])))
  n = nrows(As[1])
  zz = zero_matrix(base_ring(As[1]), 0, n^2)
  for (A, B) in zip(As, Bs)
    z = zero_matrix(FlintQQ, n^2, n^2)
    for i in 1:n
      for j in 1:n
        for k in 1:n
          z[linind[i, j], linind[i, k]] = z[linind[i, j], linind[i, k]] + A[k, j]
          z[linind[i, j], linind[k, j]] = z[linind[i, j], linind[k, j]] - B[i, k]
        end
      end
    end
    zz = vcat(zz, z)
  end
  r, K = right_kernel(zz)
  KK = change_base_ring(FlintZZ, denominator(K) * K)
  KK = transpose(saturate(transpose(KK)))
  res = typeof(As[1])[]
  for k in 1:ncols(K)
    cartind = CartesianIndices(size(As[1]))
    M = zero_matrix(base_ring(As[1]), n, n)
    for l in 1:n^2
      i1, j1 = cartind[l].I
      M[j1, i1] = KK[l, k]
    end
    for i in 1:length(As)
      M * As[i] == Bs[i] * M
    end
    push!(res, M)
  end
  return res
end

################################################################################
#
#  Simultaneous conjugacy
#
################################################################################

#function _isconjugated_probabilistic(a::Vector{fmpz_mat}, b::Vector{fmpz_mat})
#  return isconjugated_probabilistic(map(x -> map(QQ, x), a),
#                                    map(x -> map(QQ, x), b))
#end
#
#function _isconjugated_probabilistic(a::Vector{fmpq_mat}, b::Vector{fmpq_mat})
#  B = _basis_of_commutator_algebra(a, b)
#  l = length(B)
#  for i in 1:50
#    c = sum(c * b for (c, b) in zip(rand(-1:1, l), B))
#    if !iszero(det(c))
#      return true, c
#    end
#  end
#  return false, zero_matrix(FlintQQ, 0, 0)
#end
#
#function _isGLZ_conjugate(A::Vector{fmpz_mat}, B::Vector{fmpz_mat})
#  return __isGLZ_conjugate(map(x -> change_base_ring(FlintQQ, x), A),
#                          map(x -> change_base_ring(FlintQQ, x), B))
#end
#
#function _isGLZ_conjugate(A::Vector{fmpq_mat}, B::Vector{fmpq_mat})
#  d1 = lcm(fmpz[denominator(x) for x in A])
#  d2 = lcm(fmpz[denominator(x) for x in B])
#  d = lcm(d1, d2)
#  return __isGLZ_conjugate(d .* A, d .* B)
#end
#
#function __isGLZ_conjugate(A::Vector{fmpq_mat}, B::Vector{fmpq_mat})
#
#  if A == B
#    return true, identity_matrix(FlintQQ, nrows(A[1]))
#  end
#  O = _basis_of_integral_commutator_algebra(A, A)
#  I = _basis_of_integral_commutator_algebra(A, B)
#  AA = matrix_algebra(FlintQQ, map(x -> map(FlintQQ, x), O))
#  ordergens = elem_type(AA)[]
#  idealgens = elem_type(AA)[]
#
#  fl, _C = _isconjugated_probabilistic(A, B)
#  if !fl
#    return false, zero_matrix(FlintQQ, 0, 0)
#  end
#
#  @assert all(_C * map(QQ, A[i]) == map(QQ, B[i]) * _C for i in 1:length(A))
#
#  invC = inv(_C)
#
#  @info "Dimension of the commutator algebra: $(dim(AA))"
#
#  OO = Order(AA, map(x -> AA(map(QQ, x)), O))
#  OI = ideal_from_lattice_gens(AA, map(x -> AA(invC * map(QQ, x)), I))
#  @assert OO == right_order(OI)
#
#  J = radical(AA)
#
#  # Now lets do this
#  if iszero(J)
#    # Semisimple case
#    if dim(AA) == nrows(A[1])^2
#      # this is a full matrix algebra
#      dec = decompose(AA)
#      B, mB = dec[1]
#      A.isomorphic_full_matrix_algebra = A, inv(mB)
#      fl, y = _isprincipal(OI, OO, :right)::Tuple{Bool, AlgAssElem{fmpq,typeof(AA)}}
#      yy = elem_in_algebra(y)
#    elseif is_commutative(AA)
#      @info "Algebra is commutative"
#      OI.order = OO
#      d = denominator(OI, OO)
#      # Fix this upstream!
#      fl, y = is_principal(d * OI)
#      if !fl
#        return false, zero_matrix(QQ, 0, 0)
#      end
#      yy = inv(QQ(d)) * elem_in_algebra(y)
#    else
#      error("Not implemented")
#    end
#  else
#    # Pass to the semisimple quotient
#    J = radical(AA)
#    S, AtoS = quo(AA, J)
#    @info "Semisimple quotient has dimension $(dim(S))"
#    !is_commutative(S) && error("Semisimple quotient must be commutative")
#    IS = ideal_from_lattice_gens(S, [AtoS(b) for b in basis(OI)])
#    OS = Order(S, [AtoS(elem_in_algebra(b)) for b in basis(OO)])
#    @info "Algebra is commutative"
#    IS.order = OS
#    d = denominator(IS, OS)
#    # Fix this upstream!
#    fl, yy = is_principal(d * IS)
#    if !fl
#      return false, zero_matrix(QQ, 0, 0)
#    end
#    yyy = inv(QQ(d)) * elem_in_algebra(yy)
#    # Now I have to lift this
#    # I cannot just lift, I need a preimage in OI
#    d = denominator(OI, OO)
#
#    Y = zero_matrix(FlintQQ, dim(AA), dim(S))
#    OIbasis = basis(OI)
#    for i in 1:dim(AA)
#      cc = coefficients(AtoS(OIbasis[i]))
#      for j in 1:length(cc)
#        Y[i, j] = cc[j]
#      end
#    end
#
#    YY = matrix(FlintQQ, 1, dim(S), coefficients(yyy))
#    # I look for a integral solution, but the matrices are rational ..
#    d = lcm(denominator(Y), denominator(YY))
#    fl, vv = can_solve_with_solution(map(ZZ, d*Y), map(ZZ, d*YY), side = :left)
#    @assert fl
#    yy = sum(vv[i] * OIbasis[i] for i in 1:dim(AA))
#  end
#
#  if !fl
#    return false, zero_matrix(FlintQQ, 0, 0)
#  end
#
#  @assert yy * OO == OI
#
#  D = _C * matrix(yy)
#  @assert all(D * map(QQ, A[i]) == map(QQ, B[i]) * D for i in 1:length(A))
#  @assert abs(det(D)) == 1
#
#  return fl, _C * matrix(yy)
#
#  ## I know invC * I maps surjectively onto OI
#  ## Let's let the generator y
#
#  #d = denominator(OI, OO)
#
#  #Y = zero_matrix(FlintZZ, length(idealgens), dim(AA))
#  #for i in 1:length(idealgens)
#  #  cc = coordinates(OO(d * idealgens[i]))
#  #  @assert length(cc) == dim(AA)
#  #  for j in 1:length(cc)
#  #    Y[i, j] = cc[j]
#  #  end
#  #end
#
#  #YY = matrix(FlintZZ, 1, dim(AA), coordinates(OO(d * y)))
#
#  #fl, vv = can_solve_with_solution(Y, YY, side = :left)
#  #@assert fl
#  #yy = zero_matrix(FlintQQ, nrows(A), nrows(A))
#  #for i in 1:length(vv)
#  #  yy = yy + vv[1, i] * (invC * I[i])
#  #end
#
#  #T = _C * yy
#
#  #@assert abs(denominator(T)) == 1
#  #@assert T * A == B * T
#  #@assert abs(det(T)) == 1
#
#  #return fl, T
#end
