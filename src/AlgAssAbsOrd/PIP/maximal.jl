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
    @assert base_ring(ZA) isa NumField{QQFieldElem}
    B = matrix_algebra(base_ring(ZA), 1)
    img = [preimage(ZAtoA, x) for x in basis(A)]
    m = matrix(base_ring(B), dim(A), dim(B), [(x.coeffs[1])/(one(A).coeffs[1]) for x in img])
    B1 = basis(B)[1]
    minv = matrix([ZAtoA(B1[1, 1] * (x * one(ZA))).coeffs for x in absolute_basis(base_ring(ZA))])
    AtoB = AbsAlgAssMorGen(A, B, m, minv)
    A.isomorphic_full_matrix_algebra = B, AtoB
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
  elseif base_ring(A) isa QQField && dim(A) == 4 && !is_split(A)
    return _is_principal_maximal_quaternion(a, M, side)
  elseif dim(ZA) == 4 && !isdefined(A, :isomorphic_full_matrix_algebra)
    #@show A
    return _is_principal_maximal_quaternion_generic(a, M, side)
  else
    error("Not implemented yet")
  end
end

function _is_principal_maximal_quaternion_generic(a, M, side = :right)
  A = algebra(M)
  B, BtoA = _as_algebra_over_center(A)
  OB = _get_order_from_gens(B, elem_type(B)[BtoA\(elem_in_algebra(b)) for b in absolute_basis(M)])
  f = standard_involution(B)
  K = base_ring(B)
  @assert right_order(a) == M
  b = ideal_from_lattice_gens(B, OB, elem_type(B)[BtoA\(b) for b in absolute_basis(a)])
  nr = normred(b)
  nr = simplify(nr)
  #@show nr
  fl, c = is_principal_with_data(nr)
  if !fl
    return false, zero(A)
  end
  #@show c
  fl, u, reps = _reps_for_totally_positive(c, K)
  if !fl
    return false, zero(A)
  end

  #@show u
  #@show is_totally_positive(u * c)

  Babs = absolute_basis(b)::Vector{elem_type(B)}
  d = length(Babs)
  G = zero_matrix(QQ, d, d)
  #@show reps
  for z in reps
    for i in 1:d
      for j in 1:d
        G[i, j] = absolute_tr(inv(u * c * z) * trred(Babs[i] * f(Babs[j]))//2)
      end
    end
    #@show G
    #@show det(G)
    #@show lll_gram(map_entries(x -> numerator(x), G))
    #@show Hecke._eltseq(G)

    min, v = _shortest_vectors_gram(Vector, G)

    if min == degree(base_ring(B))
      for w in v
        xi = sum(elem_type(B)[w[i] * Babs[i] for i in 1:length(Babs)])::elem_type(B)
        xii = BtoA(xi)
        @assert xii in a
        @assert xii * M == a
        return true, xii
      end
    end
  end
  # TODO: Replace this by short_vectors_gram(M, nrr) once it works
  return false, zero(A)
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


