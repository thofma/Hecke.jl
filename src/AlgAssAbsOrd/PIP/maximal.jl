################################################################################
#
#  Is principal for maximal orders
#
################################################################################

# Here is the strategy for testing if a in M \subseteq A is principal.
# Decompose A = A_1 x ... x A_n and M = M_1 x ... M_n
# The A_i must know their full matrix algebra isomorphism
function _isprincipal_maximal(a::AlgAssAbsOrdIdl, M, side = :right)
  @assert side == :right
  @hassert :PIP 1 _test_ideal_sidedness(a, M, :right)
  @hassert :PIP 1 is_maximal(M)

  dena = denominator(a, M)
  aorig = a
  a = dena * a

  A = algebra(M)
  res = decompose(A)
  abas = basis(a)
  Mbas = basis(M)

  @hassert :PIP 1 all(b in M for b in abas)
  gens = elem_type(A)[]
  #@show A
  #@show group(A)
  for i in 1:length(res)
    B, mB = res[i]
    #@show isdefined(B, :isomorphic_full_matrix_algebra)
    MinB = order(B, elem_type(B)[(mB\(mB(one(B)) * elem_in_algebra(b))) for b in Mbas])
    #@show is_maximal(MinC)
    #@show hnf(basis_matrix(MinC))
    ainB = ideal_from_lattice_gens(B, elem_type(B)[(mB\(mB(one(B))* b)) for b in abas])
    @hassert :PIP 1 all(b in MinB for b in basis(ainB))
    fl, gen = _is_principal_maximal_simple_component(ainB, MinB, side)
    #@show "not simple for component", B
    if !fl
      @vprintln :PIP "Not maximal over component of dimension $(dim(B))"
      return false, zero(A)
    end
    push!(gens, mB(gen))
  end
  gen = inv(base_ring(A)(dena)) * sum(gens)
  @assert gen * M == aorig
  @hassert :PIP 1 gen * M == aorig
  return true, gen
end

function _is_principal_maximal_simple_component(a, M, side = :right)
  A = algebra(M)
  ZA, ZAtoA = _as_algebra_over_center(A)

  if !isdefined(A, :isomorphic_full_matrix_algebra) && dim(ZA) == 1
    _rewrite_algebra_which_is_center(A, ZAtoA)
    #@assert base_ring(ZA) isa NumField{QQFieldElem}
    #B = matrix_algebra(base_ring(ZA), 1)
    #img = [preimage(ZAtoA, x) for x in basis(A)]
    #i = findfirst(!iszero, one(A).coeffs)
    #@assert !isnothing(i)
    #m = matrix(base_ring(B), dim(A), dim(B), [(x.coeffs[1])/(one(A).coeffs[i]) for x in img])
    #B1 = basis(B)[1]
    #minv = matrix([ZAtoA(B1[1, 1] * (x * one(ZA))).coeffs for x in absolute_basis(base_ring(ZA))])
    #AtoB = AbsAlgAssMorGen(A, B, m, minv)
    #@info AtoB(one(A))
    #@assert is_one(AtoB(one(A))) && is_one(AtoB\(one(B)))
    #A.isomorphic_full_matrix_algebra = B, AtoB
  end

  if isdefined(A, :isomorphic_full_matrix_algebra)
    local B::MatAlgebra{AbsSimpleNumFieldElem, Generic.MatSpaceElem{AbsSimpleNumFieldElem}}
    B, AtoB = A.isomorphic_full_matrix_algebra
    OB = _get_order_from_gens(B, elem_type(B)[AtoB(elem_in_algebra(b)) for b in absolute_basis(M)])
    #@show OB
    ainOB = ideal_from_lattice_gens(B, elem_type(B)[(AtoB(b)) for b in absolute_basis(a)])
    #@show ainOB
    #@show is_maximal(OB)
    fl, gen = _is_principal_maximal_full_matrix_algebra(ainOB, OB, side)
    gentr = (AtoB\gen)::elem_type(A)
    @hassert :PIP 1 gentr * M == a
    return fl, gentr
  elseif base_ring(A) isa QQField && dim(A) == 4 && is_split(A, inf) &&
      !is_split(A)
    return _is_principal_maximal_quaternion_indefinite(a, M, side)
  elseif base_ring(A) isa QQField && dim(A) == 4 && !is_split(A)
    return _is_principal_maximal_quaternion(a, M, side)
  elseif dim(ZA) == 4 && !isdefined(A, :isomorphic_full_matrix_algebra)
    if is_split(ZA)
      error("Isomorphism test not implemented for this case")
    end
    @assert is_totally_real(base_ring(ZA))
    @assert all(!is_split(ZA, v) for v in real_places(base_ring(ZA)))
    return _is_principal_maximal_quaternion_generic(a, M, side)
  else
    error("Isomorphism test not implemented for this case")
  end
end

function _rewrite_algebra_which_is_center(A, ZAtoA)
  ZA = domain(ZAtoA)
  @assert base_ring(ZA) isa NumField{QQFieldElem}
  B = matrix_algebra(base_ring(ZA), 1)
  img = [preimage(ZAtoA, x) for x in basis(A)]
  i = findfirst(!iszero, one(A).coeffs)
  @assert !isnothing(i)
  m = matrix(base_ring(B), dim(A), dim(B), [(x.coeffs[1])/(one(ZA).coeffs[1]) for x in img])
  B1 = basis(B)[1]
  minv = matrix([ZAtoA(B1[1, 1] * (x * one(ZA))).coeffs for x in absolute_basis(base_ring(ZA))])
  AtoB = AbsAlgAssMorGen(A, B, m, minv)
  @assert is_one(AtoB(one(A))) && is_one(AtoB\(one(B)))
  @assert is_zero(AtoB(zero(A))) && is_zero(AtoB\(zero(B)))
  A.isomorphic_full_matrix_algebra = B, AtoB
end

function _is_principal_maximal_quaternion_generic(a, M, side = :right)
  A = algebra(M)
  B, BtoA = _as_algebra_over_center(A)
  OB = _get_order_from_gens(B, elem_type(B)[BtoA\(elem_in_algebra(b)) for b in absolute_basis(M)])
  @assert right_order(a) == M
  b = ideal_from_lattice_gens(B, OB, elem_type(B)[BtoA\(b) for b in absolute_basis(a)])
  fl, xi = _is_principal_with_data_definite_quaternion(b, OB, side)
  fl || return false, zero(A)
  xii = BtoA(xi)
  @hassert :PIP 1 xii * M == a
  return true, xii
end

# check if there is a unit u such that c * u is totally positive
# and return representatives for totally positive units modulo squares
function _reps_for_totally_positive(c::AbsSimpleNumFieldElem, K::AbsSimpleNumField)
  # TODO: just use the sign_map
  OK = maximal_order(K)
  U, mU = unit_group(OK)
  Q, mQ = quo(U, 2)
  r, s = signature(K)
  S = abelian_group([2 for i in 1:r])
  rpls = real_embeddings(K)
  h = hom(Q, S, [S([ sign(mU(mQ\Q[i]), sigma) == -1 ? 1 : 0 for sigma in rpls ]) for i in 1:ngens(Q)])
  # this is U/U^2 -> (Z/2Z)^r
  tar = S([ sign(c, sigma) == -1 ? 1 : 0 for sigma in rpls ])
  if is_totally_positive(c)
    el = one(K)
  else
    fl, q = has_preimage_with_preimage(h, tar)
    if !fl
      return false, zero(K), AbsSimpleNumFieldElem[]
    end
    el = mU(mQ\q)
  end
  K, mK = kernel(h)
  res = AbsSimpleNumFieldElem[]
  for k in K
    push!(res, elem_in_nf(mU(mQ\mK(k))))
  end

  return true, el, res
end

function _is_principal_maximal_quaternion(a, M, side = :right)
  @assert side == :right
  A = algebra(M)
  !(base_ring(A) isa QQField) && error("Only implemented for rational quaterion algebras")
  a.isright = 1
  a.order = right_order(a)
  if !is_split(A, inf)
    return _is_principal_with_data_definite_quaternion(a, M, side)
  end
  nrr = ZZ(normred(a))
  B = basis(a)
  G = zero_matrix(QQ, 4, 4)
  f = standard_involution(A)
  for i in 1:4
    for j in 1:4
      G[i, j] = ZZ(trred(B[i] * f(B[j])))//2
    end
  end
  # TODO: Replace this by short_vectors_gram(M, nrr) once it works
  min, v = _shortest_vectors_gram(G)

  if min == nrr
    y = sum(v[1][i] * B[i] for i in 1:4)
    if side == :right
      @assert y * M == a
    else
      @assert M * y == a
    end
    return true, y
  elseif min > nrr
    false, zero(A)
  else
    error("Something wrong here")
  end
end

# A generator of the right ideal a of the maximal order M of an indefinite
# quaternion algebra over QQ. Every such ideal is principal (Eichler's theorem,
# Voight, Quaternion Algebras, Theorem 17.8.3), but the norm form is
# indefinite, so a generator is not a short vector for it; this is
# Kirschmer-Voight, SIAM J. Comput. 39 (2010), Algorithm 4.10. With the norm
# form diagonalised as x^2 - a y^2 - b z^2 + ab w^2, the absolute reduced norm
# Q = x^2 + |a| y^2 + |b| z^2 + |ab| w^2 is positive definite with
# |nrd(x)| <= Q(x). While c = nrd(I) > 1, an element g of I with
# 0 < |nrd(g)| < c^2 exists (a generator of I has |nrd| = c), and every g with
# Q(g) < c^2 is one; then nrd(g) = cd with |d| < c, and
# I' = d g^-1 I = conj(g) I / c is an integral right ideal of M of reduced
# norm |d| with I = (g / d) I'. So the reduced norm falls at every step, and
# at 1 the ideal is M.
# As in the algorithm, g is the first vector of an LLL-reduced basis of I for
# Q when |nrd| < c^2 there (Kirschmer-Voight, Lemma 4.11: |nrd| of that vector
# is at most a constant times c). Since det Q on I is (c^2 D / 4)^2, D the
# discriminant of M, the LLL bound fails this only when c^2 < D, and only then
# are short vectors enumerated, from the bound c^2 - 1 < D. Their reduced
# norms are read off the norm form on the reduced basis, without forming
# elements of A.
function _is_principal_maximal_quaternion_indefinite(a, M, side = :right)
  @assert side == :right
  A = algebra(M)
  f = standard_involution(A)
  B = basis(A)
  G = matrix(QQ, 4, 4, [trred(B[i] * f(B[j]))//2 for i in 1:4, j in 1:4])
  F, S = _gram_schmidt(G, identity)
  Sinv = inv(S)
  P = Sinv * diagonal_matrix([abs(F[i, i]) for i in 1:4]) * transpose(Sinv)
  beta = one(A)
  I = a
  c = ZZ(normred(I, M))
  while !isone(c)
    BI = basis_matrix(I)
    bas = basis(I)
    L = lll(integer_lattice(; gram = BI * P * transpose(BI), check = false))
    # the reduced basis of I, as rows of coordinates on the basis of A, and
    # the norm form on it
    R = basis_matrix(L) * BI
    GR = R * G * transpose(R)
    w = ZZRingElem[1, 0, 0, 0]
    if abs(GR[1, 1]) >= c^2
      # nrd(v) = v GR v^t < c^2 in absolute value, as v GRz v^t < c^2 dR,
      # accumulated in place: there may be many vectors
      GRz, dR = integral_split(GR, ZZ)
      Gv = [GRz[i, j] for i in 1:4, j in 1:4]
      bd = c^2 * dR
      s = zero(ZZ)
      t = zero(ZZ)
      found = false
      lb = zero(ZZ)
      ub = c^2 - 1
      while !found
        for (v, _) in short_vectors_iterator(L, lb, ub; check = false)
          zero!(s)
          for i in 1:4, j in 1:4
            mul!(t, v[i], v[j])
            addmul!(s, Gv[i, j], t)
          end
          if cmpabs(s, bd) < 0
            w = v
            found = true
            break
          end
        end
        lb = ub
        ub = 2 * ub
      end
    end
    g = A(collect(matrix(QQ, 1, 4, w) * R)[1, :])
    d = divexact(ZZ(normred(g)), c)
    beta = QQ(1, d) * beta * g
    N = zero_matrix(QQ, 4, 4)
    for i in 1:4
      elem_to_mat_row!(N, i, QQ(1, c) * f(g) * bas[i])
    end
    I = ideal(A, M, N; side = :right)
    c = abs(d)
  end
  @hassert :PIP 1 beta * M == a
  return true, beta
end

function _is_principal_maximal_full_matrix_algebra(a, M, side = :right)
  A = algebra(M)
  if _matdeg(A) == 1
    # I don't have _as_field_with_isomorphism for algebras over K
    AA, AAtoA = restrict_scalars(A, QQ)
    K, AAtoK = _as_field_with_isomorphism(AA)
    MK = maximal_order(K)
    I = sum(fractional_ideal_type(order_type(K))[AAtoK(AAtoA\(b)) * MK for b in absolute_basis(a)])
    fl, zK = is_principal_with_data(I)
    gen = AAtoA(AAtoK\(elem_in_nf(zK)))
    if fl
      @assert gen * M == a
    end
    return fl, AAtoA(AAtoK\(elem_in_nf(zK)))
  elseif degree(base_ring(A)) == 1
    B, BtoA = _as_full_matrix_algebra_over_Q(A)
    MB = order(B, elem_type(B)[BtoA\elem_in_algebra(b) for b in absolute_basis(M)])
    aB = ideal_from_lattice_gens(B, elem_type(B)[BtoA\b for b in absolute_basis(a)])
    fl, zK = _isprincipal_maximal_simple(aB, MB, side)::Tuple{Bool, elem_type(B)}
    gen = BtoA(zK)::elem_type(A)
    if fl
      @assert zK * MB == aB
      @assert (gen * M)::typeof(a) == a
    end
    return fl, gen
  else
    fl, gen = _isprincipal_maximal_simple(a, M)
    if fl
      @assert gen * M == a
    end
    return fl, gen
  end
end

function _isprincipal_maximal_simple_nice(I::AlgAssRelOrdIdl, M, side = :right)
  @assert side == :right
  @assert _test_ideal_sidedness(I, M, :right)
  @assert M.isnice
  a = Hecke.nice_order_ideal(M)
  #@show M
  #@show a
  #den = denominator(I, M)
  #a = I * den
  if !is_full_lattice(I)
    throw(NotImplemented())
  end
  #@show basis(a)
  #@show a
  #@show norm(a, M)
  d = _matdeg(algebra(M))
  e11 = zero(algebra(M))
  e11[1, 1] = 1
  O = base_ring(M)
  K = nf(O)
  z = zero_matrix(K, d, d^2)
  B = pseudo_basis(I)
  for j in 1:d^2
    b = B[j][1]
    v = b * e11
    for i in 1:d
      z[i, j] = v[i, 1]
    end
  end
  # so z contains the first columns
  pm = pseudo_matrix(transpose(z), fractional_ideal_type(O)[b[2] for b in B])
  pmh = sub(pseudo_hnf(pm, :upperright), 1:d, 1:d)
  #@show pmh
  st = steinitz_form(pmh)
  J = st.coeffs[end] * inv(a)
  #@show J
  #@show basis(J)
  fl, _alpha = is_principal_with_data(J)
  if !fl
    return false, zero(algebra(M))
  end
  @assert st.coeffs[end] == a * _alpha

  mul_row!(st.matrix, nrows(st.matrix), _alpha)

  #@show h
  #@show T
  alpha = zero_matrix(K, d, d)
  e1i = zero_matrix(K, d, d)
  z = zero_matrix(K, d, d)
  for i in 1:d
    for j in 1:d
      z[j, 1] = st.matrix[i, j]
    end
    #@show z
    e1i[1, i] = 1
    #@show e1i
    alpha = alpha + z * e1i
    e1i[1, i] = 0
    for j in 1:d
      z[j, 1] = 0
    end
  end
  #@show basis(M)
  #@show norm((algebra(M)(alpha) * M), M)
  @assert I == algebra(M)(alpha) * M
  return true, algebra(M)(alpha)
end

function _isprincipal_maximal_simple_nice(I::AlgAssAbsOrdIdl, M, side = :right)
  @assert side == :right
  @assert _test_ideal_sidedness(I, M, :right)
  @assert basis_matrix(M) == identity_matrix(ZZ, dim(algebra(M)))
  den = denominator(I, M)
  a = I * den
  if !is_full_lattice(a)
    return false, zero(algebra(M))
  end
  #@show basis(a)
  #@show a
  #@show norm(a, M)
  d = _matdeg(algebra(M))
  e11 = zero(algebra(M))
  e11[1, 1] = 1
  z = zero_matrix(QQ, d, d^2)
  B = basis(a)
  for j in 1:d^2
    v = B[j] * e11
    for i in 1:d
      z[i, j] = v[i, 1]
    end
  end
  #@show z
  h = transpose(_hnf_integral(transpose(FakeFmpqMat(z))))
  #@show h
  @assert all(i -> is_zero_column(h, i), 1:(d^2 - d))
  T = sub(h, 1:d, (d^2 - d + 1:d^2))
  #@show T
  alpha = zero_matrix(QQ, d, d)
  e1i = zero_matrix(QQ, d, d)
  z = zero_matrix(QQ, d, d)
  for i in 1:d
    for j in 1:d
      z[j, 1] = T[j, i]
    end
    #@show z
    e1i[1, i] = 1
    #@show e1i
    alpha = alpha + z * e1i
    e1i[1, i] = 0
    for j in 1:d
      z[j, 1] = 0
    end
  end
  #@show basis(M)
  #@show norm((algebra(M)(alpha) * M), M)
  @assert a == algebra(M)(alpha) * M
  @assert I == algebra(M)(divexact(alpha, den)) * M
  return true, algebra(M)(divexact(alpha, den))
end

function _isprincipal_maximal_simple(a::AlgAssRelOrdIdl, M, side = :right)
  @assert side == :right
  @assert _test_ideal_sidedness(a, M, :right)
  @assert all(b in M for b in absolute_basis(a))
  S, c = nice_order(M)
  ainS = a * inv(c)
  #@show basis(S)
  fl, alpha = _isprincipal_maximal_simple_nice(ainS, S, side)
  if !fl
    return false, zero(M)
  else
    @assert (alpha * c) * M == a
    return true, alpha * c
  end
end

function _isprincipal_maximal_simple(a::AlgAssAbsOrdIdl, M, side = :right)
  @assert side == :right
  @assert _test_ideal_sidedness(a, M, :right)
  @assert all(b in M for b in basis(a))
  S, c = nice_order(M)
  @assert order(algebra(M), [ c * elem_in_algebra(b) * inv(c) for b in basis(M)]) == S
  ainS = a * inv(c)
  #@show basis(S)
  fl, alpha = _isprincipal_maximal_simple_nice(ainS, S, side)
  if !fl
    return false, zero(algebra(M))
  else
    @assert (alpha * c) * M == a
    return true, alpha * c
  end
end


