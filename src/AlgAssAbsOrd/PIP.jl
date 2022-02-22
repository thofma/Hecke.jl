add_verbose_scope(:PIP)
add_assert_scope(:PIP)

################################################################################
#
#  Is principal for maximal orders
#
################################################################################

function _get_order_from_gens(A::AbsAlgAss{S}, B::Vector{ <: AbsAlgAssElem{S} }) where { S <: NumFieldElem }
  M = zero_matrix(base_ring(A), length(B), dim(A))
  for i = 1:length(B)
    elem_to_mat_row!(M, i, B[i])
  end
  pm = pseudo_hnf(pseudo_matrix(M), :lowerleft, true)
  return Order(A, sub(pm, (nrows(pm) - ncols(pm) + 1):nrows(pm), 1:ncols(pm)))
end

_get_order_from_gens(A::AbsAlgAss{fmpq}, B::Vector) = Order(A, B)

# Here is the strategy for testing if a in M \subseteq A is principal.
# Decompose A = A_1 x ... x A_n and M = M_1 x ... M_n
# The A_i must know their full matrix algebra isomorphism

function _isprincipal_maximal(a::AlgAssAbsOrdIdl, M, side = :right)
  @assert side == :right
  @hassert :PIP 1 _test_ideal_sidedness(a, M, :right)
  @hassert :PIP 1 ismaximal(M)

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
    MinB = Order(B, elem_type(B)[(mB\(mB(one(B)) * elem_in_algebra(b))) for b in Mbas])
    #@show ismaximal(MinC)
    #@show hnf(basis_matrix(MinC))
    ainB = ideal_from_lattice_gens(B, elem_type(B)[(mB\(mB(one(B))* b)) for b in abas])
    @hassert :PIP 1 all(b in MinB for b in basis(ainB))
    fl, gen = _is_principal_maximal_simple_component(ainB, MinB, side)
    #@show "not simple for component", B
    if !fl
      #@info "Not maximal over dimension $(dim(B))"
      return false, zero(A)
    end
    push!(gens, mB(gen))
  end
  gen = inv(base_ring(A)(dena)) * sum(gens)
  @hassert :PIP 1 gen * M == aorig
  return true, gen
end

function absolute_basis(M::AlgAssAbsOrd{<:AlgAss{fmpq}})
  return basis(M)
end

function _is_principal_maximal_simple_component(a, M, side = :right)
  A = algebra(M)
  ZA, _ = _as_algebra_over_center(A)
  if isdefined(A, :isomorphic_full_matrix_algebra)
    local B::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    B, AtoB = A.isomorphic_full_matrix_algebra
    #@show B
    OB = _get_order_from_gens(B, elem_type(B)[AtoB(elem_in_algebra(b)) for b in absolute_basis(M)])
    #@show OB
    ainOB = ideal_from_lattice_gens(B, elem_type(B)[(AtoB(b)) for b in absolute_basis(a)])
    #@show ainOB
    #@show ismaximal(OB)
    fl, gen = _is_principal_maximal_full_matrix_algebra(ainOB, OB, side)
    return fl, (AtoB\gen)::elem_type(A)
  elseif base_ring(A) isa FlintRationalField && dim(A) == 4 && !issplit(A)
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
  fl, c = isprincipal(nr)
  if !fl
    return false, zero(A)
  end
  #@show c
  fl, u, reps = _reps_for_totally_positive(c, K)
  if !fl
    return false, zero(A)
  end

  #@show u
  #@show istotally_positive(u * c)

  Babs = absolute_basis(b)::Vector{elem_type(B)}
  d = length(Babs)
  G = zero_matrix(FlintQQ, d, d)
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

    min, v = _shortest_vectors_gram(G)

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
function _reps_for_totally_positive(c::nf_elem, K::AnticNumberField)
  OK = maximal_order(K)
  U, mU = unit_group(OK)
  Q, mQ = quo(U, 2)
  r, s = signature(K)
  S = abelian_group([2 for i in 1:r])
  rpls = real_places(K)
  h = hom(Q, S, [S([ sign(mU(mQ\Q[i]), sigma) == -1 ? 1 : 0 for sigma in rpls ]) for i in 1:ngens(Q)])
  # this is U/U^2 -> (Z/2Z)^r
  tar = S([ sign(c, sigma) == -1 ? 1 : 0 for sigma in rpls ])
  if istotally_positive(c)
    el = one(K)
  else
    fl, q = haspreimage(h, tar)
    if !fl
      return false, zero(K), nf_elem[]
    end
    el = mU(mQ\q)
  end
  K, mK = kernel(h)
  res = nf_elem[]
  for k in K
    push!(res, elem_in_nf(mU(mQ\mK(k))))
  end

  return true, el, res
end

function _is_principal_maximal_quaternion(a, M, side = :right)
  @assert side == :right
  A = algebra(M)
  !(base_ring(A) isa FlintRationalField) && error("Only implemented for rational quaterion algebras")
  a.isright = 1
  a.order = right_order(a)
  nrr = FlintZZ(normred(a))
  B = basis(a)
  G = zero_matrix(FlintQQ, 4, 4)
  f = standard_involution(A)
  for i in 1:4
    for j in 1:4
      G[i, j] = FlintZZ(trred(B[i] * f(B[j])))//2
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
    throw(error("Something wrong here"))
  end
end

function _is_principal_maximal_full_matrix_algebra(a, M, side = :right)
  A = algebra(M)
  if degree(A) == 1
    # I don't have _as_field_with_isomorphism for algebras over K
    AA, AAtoA = restrict_scalars(A, FlintQQ)
    K, AAtoK = _as_field_with_isomorphism(AA)
    MK = maximal_order(K)
    I = sum(fractional_ideal_type(order_type(K))[AAtoK(AAtoA\(b)) * MK for b in absolute_basis(a)])
    fl, zK = isprincipal(I)
    gen = AAtoA(AAtoK\(elem_in_nf(zK)))
    if fl
      @assert gen * M == a
    end
    return fl, AAtoA(AAtoK\(elem_in_nf(zK)))
  elseif degree(base_ring(A)) == 1
    B, BtoA = _as_full_matrix_algebra_over_Q(A)
    MB = Order(B, elem_type(B)[BtoA\elem_in_algebra(b) for b in absolute_basis(M)])
    aB = ideal_from_lattice_gens(B, elem_type(B)[BtoA\b for b in absolute_basis(a)])
    fl, zK = _isprincipal_maximal_simple(aB, MB, side)::Tuple{Bool, elem_type(B)}
    gen = BtoA(zK)::elem_type(A)
    if fl
      @assert zK * MB == aB
      @assert (gen * M)::typeof(a) == a
    end
    return fl, gen
  else
    N, S = nice_order(M)
    #@show pseudo_basis(N)
    AM = algebra(M)
    aN = ideal_from_lattice_gens(algebra(M), elem_type(AM)[b * inv(S) for b in absolute_basis(a)])
    fl, _gen = _isprincipal_maximal_simple_nice(aN, N, side)
    gen = _gen * S
    #if fl
    #  @assert gen * M == a
    #end
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
  if !isfull_lattice(I)
    throw(NotImplemented())
  end
  #@show basis(a)
  #@show a
  #@show norm(a, M)
  d = degree(algebra(M))
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
  #@show st
  J = st.coeffs[end] * inv(a)
  #@show J
  #@show basis(J)
  fl, _alpha = isprincipal(J)
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
  @assert basis_matrix(M) == FakeFmpqMat(identity_matrix(FlintZZ, dim(algebra(M))))
  den = denominator(I, M)
  a = I * den
  if !isfull_lattice(a)
    return false, zero(algebra(M))
  end
  #@show basis(a)
  #@show a
  #@show norm(a, M)
  d = degree(algebra(M))
  e11 = zero(algebra(M))
  e11[1, 1] = 1
  z = zero_matrix(FlintQQ, d, d^2)
  B = basis(a)
  for j in 1:d^2
    v = B[j] * e11
    for i in 1:d
      z[i, j] = v[i, 1]
    end
  end
  #@show z
  h = transpose(hnf(transpose(FakeFmpqMat(z))))
  #@show h
  @assert all(i -> iszero_column(h, i), 1:(d^2 - d))
  T = sub(h, 1:d, (d^2 - d + 1:d^2))
  #@show T
  alpha = zero_matrix(FlintQQ, d, d)
  e1i = zero_matrix(FlintQQ, d, d)
  z = zero_matrix(FlintQQ, d, d)
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
  @assert all(b in M for b in basis(a))
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
  @assert Order(algebra(M), [ c * elem_in_algebra(b) * inv(c) for b in basis(M)]) == S
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

function _isprincipal(a::AlgAssAbsOrdIdl, O, side = :right)
  #@show "HEREREHRE3"
  if hnf(basis_matrix(O)) != hnf(basis_matrix(right_order(a)))
    return false, zero(algebra(O))
  end

  if ismaximal(O)
    #@show "ORDER IS MAXIMAL"
    return _isprincipal_maximal(a, O, side)
  end


  # So O is the right order of a

  n = dim(algebra(O))
  aa = denominator(a, O) * a
  aa.order = O
  for (p, ) in factor(discriminant(O))
    @vprint :PIP 1 "Testing local freeness at $p\n"
    if !islocally_free(O, aa, p, side = :right)[1]::Bool
      return false, zero(algebra(O))
    end
  end

  #@show "HEREREHRE4"

  # So a is locally free over O

  A = algebra(O)
  #@show [isdefined(B, :isomorphic_full_matrix_algebra) for (B, mB) in decompose(A)]
  OA = maximal_order(O)
  Z, ZtoA = center(A)
  Fl = conductor(O, OA, :left)

  FinZ = _as_ideal_of_smaller_algebra(ZtoA, Fl)
  # Compute FinZ*OA but as an ideal of O
  bOA = basis(OA, copy = false)
  bFinZ = basis(FinZ, copy = false)
  basis_F = Vector{elem_type(A)}()
  for x in bOA
    for y in bFinZ
      yy = ZtoA(y)
      t = yy * elem_in_algebra(x, copy = false)
      push!(basis_F, t)
    end
  end

  for b in basis_F
    @assert b in O
  end

  F = ideal_from_lattice_gens(A, O, basis_F, :twosided)

  #@show F == A(1) * O
  #@show F == A(1) * OA

  aorig = a

  # I shoul improve this
  a, sca = _coprime_integral_ideal_class_deterministic(a, F)
  #a, sca = _coprime_integral_ideal_class(a, F)
  @vprint :PIP 1 "Found coprime integral ideal class\n"

  @hassert :PIP 1 sca * aorig == a

  @hassert :PIP 1 a + F == one(A) * O

  # Compute K_1(O/F) and the subgroup of R generated by nr(a)*OZ for a in k1 where
  # nr is the reduced norm and OZ the maximal order in Z
  @vprint :PIP 1 "Lifting ideal to maximal order\n"
  aOA = a * OA #sum([b * OA for b in basis(a)])
  @vprint :PIP 1 "Testing if principal over maximal order\n"
  fl, beta = _isprincipal_maximal(aOA, OA, side)
  if !fl
    return false, zero(A)
  end
  @hassert :PIP 1 beta * OA == aOA

  @info "Computing K1..."
  #@show F, FinZ
  k1 = K1_order_mod_conductor(O, OA, F, FinZ)
  OZ = maximal_order(Z)
  Q, mQ = quo(OZ, FinZ)
  Quni, mQuni = unit_group(Q)
  U::GrpAbFinGen, mU::MapUnitGrp{Hecke.AlgAssAbsOrd{AlgAss{fmpq},AlgAssElem{fmpq,AlgAss{fmpq}}}} = unit_group(OZ)
  @vprint :PIP 1 "Solving principal ideal problem over maximal order...\n"

  #@show Q
  normbeta = OZ(normred_over_center(beta, ZtoA))

  #@show parent(normbeta) == domain(mQ)
  ttt = mQuni\(mQ(normbeta))
  imgofK1 = GrpAbFinGenElem[ mQuni\(mQ(OZ(normred_over_center(elem_in_algebra(b), ZtoA)))) for b in k1]
  imgofK1assub, m_imgofK1assub = sub(Quni, imgofK1)
  QbyK1, mQbyK1 = quo(Quni, imgofK1)

  SS, mSS = sub(Quni, imgofK1)

  # This is O_C^* in Q/K1
  S, mS = sub(QbyK1, elem_type(QbyK1)[ mQbyK1(mQuni\(mQ(mU(U[i])::elem_type(OZ)))) for i in 1:ngens(U)])
  fl, u = haspreimage(mS, mQbyK1(ttt))
  if !fl
    return false, zero(A)
  end

  @vprint :PIP 1 "Solving norm requation over center\n"
  #@show typeof(OA)
  #@show typeof(ZtoA(elem_in_algebra(mU(u)::elem_type(OZ))))
  _u = prod([ mU(U[i])^u.coeff[1, i] for i in 1:length(u.coeff)])
  UU = _solve_norm_equation_over_center(OA, ZtoA(elem_in_algebra(_u::elem_type(OZ))))

  fll, uu = haspreimage(mSS,  mQuni\(mQ(OZ(normred_over_center(elem_in_algebra(UU), ZtoA)))) - ttt)

  @assert fll

  elemA = one(A)
  for i in 1:length(uu.coeff)
    if !iszero(uu.coeff[1, i])
      elemA = elemA * elem_in_algebra(k1[i])^Int(uu.coeff[1, i])
    end
  end

  ##@show mQuni\(mQ(OZ(normred_over_center(elem_in_algebra(UU), ZtoA)))) ==  mQuni\(mQ(OZ(normred_over_center(beta * elemA, ZtoA))))

  @info "Lifting to norm one unit"
  V = lift_norm_one_unit( UU^(-1) * OA(elemA)  * OA(beta), F)

  gamma =  beta * inv(elem_in_algebra(UU) * V)
  @hassert :PIP 1 gamma * O == a
  gammaorig = inv(sca) * gamma
  @assert gammaorig * O == aorig

  return true, gammaorig
end

function _solve_norm_equation_over_center(M, x)
  A = algebra(M)
  dec = decompose(A)
  #@show x
  Mbas = basis(M)
  sol = zero(M)
  for i in 1:length(dec)
    Ai, mAi = dec[i]
    MinAi = Order(Ai, [ mAi\(mAi(one(Ai)) * elem_in_algebra(b)) for b in Mbas])
    si = _solve_norm_equation_over_center_simple(MinAi, preimage(mAi, x))
    sol += M(mAi(elem_in_algebra(si)))
  end
  ZA, ZAtoA = center(A)
  @assert ZAtoA(normred_over_center(elem_in_algebra(sol), ZAtoA)) == x
  return sol
end

function _solve_norm_equation_over_center_simple(M, x)
  A = algebra(M)
  if isdefined(A, :isomorphic_full_matrix_algebra)
    local B::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    @assert isdefined(A, :isomorphic_full_matrix_algebra)
    B, AtoB = A.isomorphic_full_matrix_algebra
    Mbas = absolute_basis(M)
    MinB = _get_order_from_gens(B, elem_type(B)[ AtoB(elem_in_algebra(b))::elem_type(B) for b in Mbas])
    y = Hecke._solve_norm_equation_over_center_full_matrix_algebra(MinB, AtoB(x)::elem_type(B))
    sol = M(AtoB\elem_in_algebra(y))
    ZA, ZAtoA = center(A)
    @assert ZAtoA(normred_over_center(elem_in_algebra(sol), ZAtoA)) == x
    return sol
  elseif degree(A) == 4 && !issplit(A)
    return _solve_norm_equation_over_center_quaternion(M, x)
  else
    throw(NotImplemented())
  end
end

function _solve_norm_equation_over_center_quaternion(M, x)
  A = algebra(M)
  !(base_ring(A) isa FlintRationalField) && error("Only implemented for rational quaterion algebras")
  B = basis_alg(M)
  G = zero_matrix(FlintQQ, 4, 4)
  f = standard_involution(A)
  for i in 1:4
    for j in 1:4
      G[i, j] = FlintZZ(trred(B[i] * f(B[j])))//2
    end
  end
  # TODO: Replace this by short_vectors_gram(M, nrr) once it works
  i = 0
  xalg = x
  local nrm
  for i in 1:dim(A)
    if !iszero(xalg.coeffs[i])
      nrm = FlintZZ(divexact(xalg.coeffs[i], one(A).coeffs[i]))
    end
  end
  #@show nrm
  V = _short_vectors_gram(G, nrm)
  for i in 1:length(V)
    if V[i][2] == nrm
      y = sum(V[i][1][j] * B[j] for j in 1:4)
      @assert normred(y) == nrm
      return M(y)
    end
  end
end

function _solve_norm_equation_over_center_full_matrix_algebra(M, x)
  A = algebra(M)
  ZA, ZAtoA = center(A)
  if degree(A) == 1
    @assert ZAtoA(normred_over_center(x, ZAtoA)) == x
    return M(x)
  elseif degree(base_ring(A)) == 1
    B, BtoA = _as_full_matrix_algebra_over_Q(A)
    MB = Order(B, [(BtoA\elem_in_algebra(b))::elem_type(B) for b in absolute_basis(M)])
    xinB = BtoA\x
    solB = _solve_norm_equation_over_center_full_rational_matrix_algebra(MB, xinB)
    sol = M(BtoA(elem_in_algebra(solB))::elem_type(A))
    @assert ZAtoA(normred_over_center(elem_in_algebra(sol), ZAtoA)) == x
    return sol
  else
    N, S = nice_order(M)
    xN = S * x * inv(S)
    solN = _solve_norm_equation_over_center_full_matrix_algebra_nice(N, xN)
    sol = inv(S) * elem_in_algebra(solN) * S
    @assert sol in M
    @assert ZAtoA(normred_over_center(sol, ZAtoA)) == x
    return M(sol)
  end
  throw(NotImplemented())
end

function _solve_norm_equation_over_center_full_rational_matrix_algebra(M, x)
  A = algebra(M)
  R, c = nice_order(M)
  e11 = elem_in_algebra(basis(R)[1])
  u = x
  sol = one(A)
  sol[1, 1] = u[1, 1]
  z = R(sol)
  ZA, ZAtoA = center(A)
  @assert ZAtoA(normred_over_center(elem_in_algebra(z), ZAtoA)) == u
  soladj = inv(c) * sol * c
  @assert soladj in M
  @assert ZAtoA(normred_over_center(soladj, ZAtoA)) == x
  return M(soladj)
end

function _solve_norm_equation_over_center_full_matrix_algebra_nice(M, x)
  A = algebra(M)
  e11 = basis(A)[1]
  u = x
  sol = one(A)
  sol[1, 1] = u[1, 1]
  ZA, ZAtoA = center(A)
  @assert ZAtoA(normred_over_center(sol, ZAtoA)) == x
  return M(sol)
end

function lift_norm_one_unit(x, F)
  # F must be central
  M = parent(x)
  A = algebra(M)
  res = decompose(A)
  Mbas = basis(M)
  z = zero(A)
  #@show F
  for i in 1:length(res)
    Ai, AitoA = res[i]
    MinAi = Order(Ai, elem_type(Ai)[ AitoA\(AitoA(one(Ai)) * elem_in_algebra(b)) for b in Mbas])
    xinAi = MinAi(preimage(AitoA, elem_in_algebra(x)))
    Fi = ideal_from_lattice_gens(Ai, MinAi, [ AitoA\b for b in basis(F) ], :twosided)
    #@show Fi
    y = _lift_norm_one_unit_simple(xinAi, Fi)
    z += AitoA(y)
  end
  FinM = ideal_from_lattice_gens(A, M, basis(F), :twosided)
  @assert _test_ideal_sidedness(FinM, M, :left)
  Q, mQ = quo(M, FinM)
  @assert mQ(M(z)) == mQ(x)
  #@show normred(z)
  return z
end

function _lift_norm_one_unit_simple(x, F)
  M = parent(x)
  A = algebra(M)
  # It may happen that the order is maximal in a simple component, that is,
  # F == M
  if F == one(A) * M
    return one(A)
  end
  if isdefined(A, :isomorphic_full_matrix_algebra)
    local B::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    @assert isdefined(A, :isomorphic_full_matrix_algebra)
    B, AtoB = A.isomorphic_full_matrix_algebra
    Mbas = basis(M)
    MinB = _get_order_from_gens(B, elem_type(B)[ AtoB(elem_in_algebra(b)) for b in Mbas])
    FinB = ideal_from_lattice_gens(B, MinB, elem_type(B)[ AtoB(b) for b in basis(F) ], :twosided)
    y = _lift_norm_one_unit_full_matrix_algebra(MinB(AtoB(elem_in_algebra(x))::elem_type(B)), FinB)
    return (AtoB\y)::elem_type(A)
  elseif degree(A) == 4 && !issplit(A)
    return _lift_norm_one_unit_quaternion(x, F)
  else
    error("Not implemented yet")
  end
end

function _lift_norm_one_unit_quaternion(x, F)
  M = parent(x)
  A = algebra(M)
  B = basis_alg(M)
  ZA, ZAtoA = center(A)
  FinZA = _as_ideal_of_smaller_algebra(ZAtoA, F)
  G = zero_matrix(FlintQQ, 4, 4)
  f = standard_involution(A)
  for i in 1:4
    for j in 1:4
      G[i, j] = FlintZZ(trred(B[i] * f(B[j])))//2
    end
  end

  #@show M
  #@show F

  #@show elem_in_algebra(x)

  #@show normred(elem_in_algebra(x))
  # TODO: Replace this by short_vectors_gram(M, nrr) once it works
  V = _short_vectors_gram(G, fmpz(1))
  for i in 1:length(V)
    y = sum(V[i][1][j] * B[j] for j in 1:4)
    @assert normred(y) == 1
    if y - x in F
      return y
      println("successs");
    end
    if -y - x in F
      return -y
      println("success");
    end
  end

  @assert false
end

function _lift_norm_one_unit_full_matrix_algebra(x, F)
  #@show F
  A = algebra(parent(x))
  if degree(A) == 1
    return elem_in_algebra(one(parent(x)))
  elseif degree(base_ring(A)) == 1
    M = parent(x)
    A = algebra(M)
    B, BtoA = _as_full_matrix_algebra_over_Q(A)
    MinB = _get_order_from_gens(B, elem_type(B)[BtoA\elem_in_algebra(b) for b in absolute_basis(M)])
    FinB = ideal_from_lattice_gens(B, MinB, elem_type(B)[ BtoA\(b) for b in absolute_basis(F) ], :twosided)
    yy = _lift_norm_one_unit_full_rational_matrix_algebra(MinB(BtoA\(elem_in_algebra(x))), FinB)
    return BtoA(yy)
  else
    M = parent(x)
    N, S = nice_order(M)
    xN = N(S * elem_in_algebra(x) * inv(S))
    y = _lift_norm_one_unit_full_matrix_algebra_nice(xN, F)
    return inv(S) * y * S
  end
  throw(NotImplemented())
end

function _lift_norm_one_unit_full_matrix_algebra_nice(x, F)
  M = parent(x)
  A = algebra(M)
  ZA, ZAtoA = center(A)
  FinZA = _as_ideal_of_smaller_algebra(ZAtoA, F)
  # the center is a number field
  #@show FinZA
  el, id = pseudo_basis(FinZA)[1]
  fl, el2 = isprincipal(id)
  if false fl
    @assert fl
    n = el.coeffs[1] * el2
    OK = base_ring(M)
    @assert basis_pmatrix(M).matrix == identity_matrix(base_ring(A), dim(A))
    R, mR = quo(OK, OK(n) * OK)
    #@show mR(FacElem(det(matrix(elem_in_algebra(x)))))
    #@show n
    #@show det(matrix(elem_in_algebra(x)))
    @assert isone(mR(FacElem(det(matrix(elem_in_algebra(x))))))
    li = _lift_unimodular_matrix(change_base_ring(OK, matrix(elem_in_algebra(x))), OK(n), R)
    #@show map_entries(R, li) == map_entries(R, change_base_ring(OK, matrix(elem_in_algebra(x))))
    @assert (M(A(change_base_ring(base_ring(A), li))) - x) in id * M
    return A(change_base_ring(base_ring(A), li))
  else
    a = nice_order_ideal(M)
    @assert isone(denominator(id))
    anu = numerator(a)
    idnu = numerator(id)
    b, zetainv = _coprime_integral_ideal_class(a, idnu)
    # zetainv * a == b
    @assert b + idnu == 1*order(b)
    zeta = inv(zetainv)
    n = degree(A)
    Phi1 = identity_matrix(base_ring(A), n)
    Phi1[n, n] = zetainv
    _belem, y = idempotents(b, idnu)
    belem = elem_in_nf(_belem)
    Phi2 = identity_matrix(base_ring(A), n)
    Phi2[n, n] = belem * zeta
    xtrans = matrix(Phi1 * elem_in_algebra(x) * Phi2)
    @assert all(x -> isintegral(x), xtrans)
    OK = base_ring(M)
    K = nf(OK)
    R, mR = quo(OK, idnu)
    @assert isone(det(map_entries(mR, change_base_ring(OK, xtrans))))
    el_matrices = _write_as_product_of_elementary_matrices(change_base_ring(OK, xtrans), R)
    lifted_el_matrices = elem_type(M)[]
    for E in el_matrices
      _E = _lift_and_adjust(E, zeta, belem)
      @assert A(_E) in M
      push!(lifted_el_matrices, M(A(_E)))
    end

    li = reduce(*, lifted_el_matrices)
    @assert isone(det(matrix(elem_in_algebra(li))))

    @assert li - x in id * M

    #@show (li - x) in id * M

    return elem_in_algebra(li)
  end
end

function _lift_norm_one_unit_full_rational_matrix_algebra(x, F)
  M = parent(x)
  B = algebra(M)
  Mbas = basis(M)
  ZB, ZBtoB = center(B)
  FinZB = _as_ideal_of_smaller_algebra(ZBtoB, F)
  bas = basis(FinZB)[1]
  n = bas.coeffs[1]
  @assert n * one(ZB) == bas
  @assert B(n) * M == F

  nn = FlintZZ(n)

  R, c = nice_order(M)

  xwrtR = c * elem_in_algebra(x) * inv(c)

  # Now x is in M_n(Z) and I want to lift from M_n(Z/nn)

  @assert mod(FlintZZ(det(matrix((xwrtR)))), nn) == 1

  R = ResidueRing(FlintZZ, nn, cached = false)
  li = _lift2(map_entries(u -> R(FlintZZ(u)), matrix(xwrtR)))
  #li = _lift_unimodular_matrix(change_base_ring(FlintZZ, matrix(xwrtR)), nn, ResidueRing(FlintZZ, nn))

  return (inv(c) * B(change_base_ring(FlintQQ, li)) * c)
end

################################################################################
#
#  Lifting unimodular matrix
#
################################################################################

function _lift_and_adjust(E, zeta, b)
  #@show E
  K = parent(zeta)
  n = nrows(E)
  res = identity_matrix(K, nrows(E))
  for i in 1:n
    for j in 1:n
      if i != j && !iszero(E[i, j])
        if j == n
          res[i, j] = lift(E[i, j]) * inv(zeta)
        elseif i == n
          res[i, j] = zeta * b * lift(E[i, j])
        else
          res[i, j] = lift(E[i, j])
        end
        return res
      end
    end
  end
  return res
end

function _write_as_product_of_elementary_matrices(N, R)
  OK = base_ring(N)
  Nred = change_base_ring(R, N)
  k = nrows(N)

  if !isone(det(Nred))
    throw(ArgumentError("Matrix must have determinant one"))
  end

  trafos = typeof(Nred)[]

  for i in 1:k
    Nred, tra = _normalize_column(Nred, i)
    append!(trafos, tra)
  end

  #println(sprint(show, "text/plain", Nred))

  Nred2 = change_base_ring(R, N)
  for T in trafos
    Nred2 = T * Nred2
  end
  @assert Nred2 == Nred

  Nredtr = transpose(Nred)

  trafos_tr = typeof(Nred)[]

  for i in 1:k
    Nredtr, tra = _normalize_column(Nredtr, i)
    append!(trafos_tr, tra)
  end

  #println(sprint(show, "text/plain", Nredtr))

  #Nred2 = change_base_ring(R, N)
  #for T in trafos
  #  Nred2 = T * Nred2
  #end

  #for T in trafos_tr
  #  Nred2 = Nred2 * transpose(T)
  #end

  # I need to normalize a diagonal matrix
  Nredtr, trafos3 = _normalize_diagonal(Nredtr)
  append!(trafos_tr, trafos3)
  @assert isone(Nredtr)

  res = typeof(Nred)[]

  for T in trafos
    push!(res, _inv_elementary_matrix(T))
  end

  for T in reverse(trafos_tr)
    push!(res, transpose(_inv_elementary_matrix(T)))
  end

  @assert reduce(*, res) == change_base_ring(R, N)
  return res
end

function _normalize_diagonal(N)
  n = nrows(N)
  trafos = typeof(N)[]
  R = base_ring(N)
  for i in n:-1:2
    a = N[i, i]
    inva = inv(a)
    E1 = elementary_matrix(R, n, i - 1, i, -one(R))
    E2 = elementary_matrix(R, n, i, i - 1,  one(R))
    E3 = elementary_matrix(R, n, i - 1, i, -one(R))
    E4 = elementary_matrix(R, n, i - 1, i, a)
    E5 = elementary_matrix(R, n, i, i - 1,  -inva)
    E6 = elementary_matrix(R, n, i - 1, i, a)
    N = E6 * E5 * E4 * E3 * E2 * E1 * N
    push!(trafos, E1)
    push!(trafos, E2)
    push!(trafos, E3)
    push!(trafos, E4)
    push!(trafos, E5)
    push!(trafos, E6)
  end
  @assert isone(N)
  return N, trafos
end

function _inv_elementary_matrix(M)
  n = nrows(M)
  N = identity_matrix(base_ring(M), n)
  for i in 1:n
    for j in 1:n
      if i != j && !iszero(M[i, j])
        N[i, j] = -M[i, j]
      end
    end
  end
  @assert isone(N * M)
  return N
end


function _normalize_column(N, i)
  n = nrows(N)
  R = base_ring(N)
  trafos = typeof(N)[]
  if isunit(N[i, i])
    ainv = inv(N[i, i])
    for j in n:-1:(i + 1)
      E = elementary_matrix(R, n, j, i, -ainv * N[j, i])
      #@show N
      N = mul!(N, E, N)
      #@show N
      push!(trafos, E)
    end
    return N, trafos
  else
    for j in (i + 1):n
      if isunit(N[j, i])
        E1 = elementary_matrix(R, n, i, j, one(R))
        N = mul!(N, E1, N)
        push!(trafos, E1)
        E2 = elementary_matrix(R, n, j, i, -one(R))
        N = mul!(N, E2, N)
        push!(trafos, E2)
        E3 = elementary_matrix(R, n, i, j, one(R))
        N = mul!(N, E3, N)
        push!(trafos, E3)
        @assert isunit(N[i, i])
        N, trafos2 = _normalize_column(N, i)
        append!(trafos, trafos2)
        return N, trafos
      end
    end
    # This is the complicated case
    while true
      euc_min = euclid(N[i, i])
      i0 = i
      local e
      for j in (i + 1):n
        e = euclid(N[j, i])
        if (euc_min == -1 && e != - 1) || (e < euc_min)
          i0 = j
          euc_min = e
        end
      end
      if euc_min == 1
        # We found a unit
        break
      end
      ai0 = N[i0, i]
      for j in i:n
        aj = N[j, i]
        if !divides(aj, ai0)[1]
          q, r = divrem(aj, ai0)
          @assert euclid(r) < euclid(ai0)
          E = elementary_matrix(R, n, j, i0, -q)
          N = mul!(N, E, N)
          push!(trafos, E)
        end
      end
    end
    N, trafos2 = _normalize_column(N, i)
    append!(trafos, trafos2)
    return N, trafos
  end
  error("Something went wrong")
end

function _lift_unimodular_matrix(N, n, R)
  OK = base_ring(N)
  M = change_base_ring(R, N)
  k = nrows(M)

  if !isone(det(M))
    throw(ArgumentError("Matrix must have determinant one"))
  end

  if k == 1
    return scalar_matrix(FlintZZ, 1, one(FlintZZ))
  end

  left_elementary = typeof(M)[]
  right_elementary = typeof(M)[]

  for l in 3:k
    r = nrows(M)
    _c = 0
    for i in 1:r
      if !iszero(M[i, 1])
        _c += 1
      end
    end
    if r != _c
      #@show "I am in case 1"
      i = 0
      x = one(R)
      #@show M
      #@show base_ring(M)
      while !iszero(x)
        i += 1
        x = M[i, 1]
      end
      @assert 1 <= i <= r
      #@show i
      if i != 1
        #@show i
        E1 = identity_matrix(R, r)
        E1[1, i] = one(R)
        E2 = identity_matrix(R, r)
        E2[i, 1] = -one(R)
        push!(left_elementary, E1)
        push!(left_elementary, E2)
        push!(left_elementary, E1)
        M = E1 * E2 * E1 * M
        @assert det(M) == 1
      end
      #@show "case1", M
    else
      v = push!(elem_type(OK)[lift(M[i, 1]) for i in 3:r], n)
      d, z = _gcdx(v)
      @assert d == sum(elem_type(OK)[z[i] * v[i] for i in 1:length(v)])
      if d == 1
        a = elem_type(R)[M[i, 1] for i in 1:r]
        a1 = a[1]
        a = elem_type(R)[a[j] for j in 3:r]
        I = identity_matrix(R, r)
        for j in 1:(length(z) - 1)
          I[1, j + 2] = -a1 * R(z[j])
        end
        M = I * M
        @assert det(M) == 1
        push!(left_elementary, I)
        #@show M[1, 1]
      else
        a = elem_type(R)[M[i, 1] for i in 1:r]
        a1 = lift(a[1])
        a2 = lift(a[2])
        ai = eltype(a)[a[i] for i in 3:length(a)]

        dI, z = _gcdx(push!(elem_type(OK)[lift(a[i]) for i in 3:length(a)], n))
        d, y = _gcdx(push!(elem_type(OK)[lift(a[i]) for i in 1:length(a)], n))
        # TODO: This will fail Tommy!
        if OK isa FlintIntegerRing
          RI = ResidueRing(OK, dI)
        else
          RI = ResidueRing(OK, dI * OK)
        end
        MatL = matrix(RI, 2, 2, [a1, a2, -y[2], y[1]])
        @assert det(MatL) == 1
        E = lift_two_by_two_matrix(MatL)
        x1 = E[2, 2]
        x2 = -E[2, 1]
        b1 = E[1, 1]
        b2 = E[1, 2]
        @assert x1 * b1 + x2 * b2 == 1

        x3n = vcat(elem_type(OK)[x1, x2], elem_type(OK)[y[i] + (OK(divexact(y[1] - x1, dI)) * M[1, 1] + R(divexact(y[2] - x2, dI)) * M[2, 1]) * z[i - 2] for i in 3:length(y)])
        I = identity_matrix(R, r)
        for j in 3:r
          I[1, j] = b1 * x3n[j]
          I[2, j] = b2 * x3n[j]
        end
        M = I * M
        @assert det(M) == 1
        push!(left_elementary, I)
#				// now M has a1 and a2 in the (1,1) und (2,1) slot, resp.
#				// and it holds x1a1+x2a2 = 1.
#				// delete the entry a_n1 via an1 + (-an1*x1*a11 - an1*x2*a22) and switch it in the (1,1) slot:
        I = identity_matrix(R, r)
        I[r, 1] = -M[r, 1] * x1
        I[r, 2] = -M[r, 1] * x2
        M = I * M
        @assert det(M) == 1
        push!(left_elementary, I)
        E1 = identity_matrix(R, r)
        E1[1, r] = one(R)
        E2 = identity_matrix(R, r)
        E2[r, 1] = -one(R)
        M = E1 * E2 * E1 * M
        @assert det(M) == 1
        push!(left_elementary, E1)
        push!(left_elementary, E2)
        push!(left_elementary, E1)
      end
    end
#		// Step Two, assuming m_11 is zero. We use Det(M) = 1 to get one in (1,1):
    I = identity_matrix(R, r)
    Mwithout1stcolumn = sub(M, 1:nrows(M), 2:ncols(M))
    for i in 2:r
      I[1, i] = (-1)^(i + 1) * det(remove_row(Mwithout1stcolumn, i))
    end
    #@show "asdsd", I
    M = I * M
    @assert det(M) == 1
    push!(left_elementary, I)

    I = identity_matrix(R, r)
    for i in 2:r
      I[i, 1] = -M[i, 1]
    end
    M = I * M
    @assert det(M) == 1
    push!(left_elementary, I)

    I = identity_matrix(R, r)
    for i in 2:r
      I[1, i] = -M[1, i]
    end
    M = M * I
    @assert det(M) == 1
    push!(right_elementary, I)
    #@show M
    M = sub(M, 2:r, 2:r)
    @assert det(M) == 1
  end

  if length(left_elementary) >= 1
    V1 = prod([lift_triangular_matrix(size_up(Z, k)) for Z in reverse(left_elementary)])
  else
    V1 = identity_matrix(OK, k)
  end

  if length(right_elementary) >= 1
    V2 = prod([lift_triangular_matrix(size_up(Z, k)) for Z in right_elementary])
  else
    V2 = identity_matrix(OK, k)
  end
  Q = lift_two_by_two_matrix(M)
  #@show det(Q)
  #@show det(size_up(Q, k))
  return inv(V1) * size_up(Q, k) * inv(V2)
end

_gcdx(x::fmpz, y::fmpz) = gcdx(x, y)

function _gcdx(v::AbstractVector{T}) where T
  if length(v) == 2
    g, a, b = _gcdx(v[1], v[2])
    return g, T[a, b]
  end

  w = @view v[2:end]
  gtail, bezouttail = _gcdx(w)
  g, a, b = _gcdx(v[1], gtail)
  for i in 1:length(bezouttail)
    mul!(bezouttail[i], bezouttail[i], b)
  end
  bezout = pushfirst!(bezouttail, a)
  @assert g == sum(bezout[i] * v[i] for i in 1:length(v))
  return g, bezout
end

function remove_row(M, r)
  N = zero_matrix(base_ring(M), nrows(M) - 1, ncols(M))
  n = nrows(M)
  m = ncols(M)
  l = 1
  for i in 1:n
    if i == r
      continue
    end
    for j in 1:m
      N[l, j] = M[i, j]
    end
    l += 1
  end
  return N
end

function size_up(T::MatElem, n::Int)
  s = nrows(T)
  t = ncols(T)
  S = identity_matrix(base_ring(T), n)
  for i in 1:s
    for j in 1:t
	    S[i+n-s, j+n-t] = T[i,j]
    end
  end
  #@show T, S
  return S
end

_lift(x::AbsOrdQuoRingElem) = lift(x)

_lift(x::RelOrdQuoRingElem) = lift(x)

_lift(x::Nemo.fmpz_mod) = lift(x)

function lift_triangular_matrix(E)
  #@show E
  z = map_entries(_lift, E)
  #@show matrix(base_ring(E), z)
  @assert map_entries(base_ring(E),  z) == E
  return z
end

function lift_two_by_two_matrix(M)
  #@show M
  left_elementary = typeof(M)[]
  right_elementary = typeof(M)[]
  A = base_ring(M)

  #@show det(M)
  #@show A
  @assert det(M) == 1

  if isunit(M[1, 1])
    E1 = identity_matrix(A, 2)
    B = deepcopy(M)
  elseif isunit(M[2, 1])
    E1 = identity_matrix(A, 2)
    E1[1, 2] = one(A)
    E2 = identity_matrix(A, 2)
    E2[2, 1] = -one(A)
    B = E1 * E2 * E1 * M
    @assert det(B) == 1
    push!(left_elementary, E1)
    push!(left_elementary, E2)
    push!(left_elementary, E1)
  else
    E = identity_matrix(A, 2)
    x = rand(A)
    while !isunit(M[1, 1] + x * M[2, 1])
      x = rand(A)
    end
    E[1,2] = x
    B = E*M
    @assert B[1, 1] == M[1, 1] + x * M[2, 1]
    @assert det(B) == 1
    push!(left_elementary, E)
	end

  #@show left_elementary

  a1 = inv(B[1,1])
  D1 = identity_matrix(A, 2)
  D1[1, 2] += a1
	D2 = identity_matrix(A, 2)
  D2[2, 1] -= B[1, 1]
	D3 = identity_matrix(A, 2)
  D3[1, 2] += a1
	D4 = zero_matrix(A, 2, 2)
  D4[2, 1] += 1
  D4[1, 2] -= 1
  B = D1*D2*D3*D4*B
  @assert det(B) == 1
  push!(left_elementary, D4)
  push!(left_elementary, D3)
  push!(left_elementary, D2)
  push!(left_elementary, D1)
  E3 = identity_matrix(A, 2)
  E3[2, 1] = -B[2, 1]
  #@show E3
	B = E3*B
  @assert det(B) == 1
  push!(left_elementary, E3)
  F1 = identity_matrix(A, 2)
  F1[1, 2] = -B[1, 2]
	B = B*F1
  @assert det(B) == 1
  push!(right_elementary, F1)
  #@show B
  #@show left_elementary
  #@show right_elementary
  U1 = prod([lift_two_by_two_elementary_matrix(Z) for Z in reverse(left_elementary)])
  #@show U1
  U2 = prod([lift_two_by_two_elementary_matrix(Z) for Z in reverse(right_elementary)])
  #@show U2
  @assert isone(det(U1))
  @assert isone(det(U2))
  res = inv(U1) * inv(U2);
  #@show res
  #@show matrix(base_ring(M), res)
  #@show M
  @assert map_entries(base_ring(M), res) == M
  return res
end

_base_ring(A::AbsOrdQuoRing) = base_ring(A)

function lift_two_by_two_elementary_matrix(E)
  R = base_ring(E)
  if iszero(E[1, 1]) && iszero(E[2, 2]) && E[1, 2] == -1 && E[2, 1] == 1
    z = matrix(_base_ring(R), 2, 2, [0, -1, 1, 0])
  elseif E[1, 1] == 1 && E[2, 2] == 1 && E[1, 2] == 0 && E[2, 1] == 0
    z = matrix(_base_ring(R), 2, 2, [1, 0, 0, 1])
  else
    z = map_entries(lift, E)
  end
  #@show E, z
  @assert matrix(base_ring(E), 2, 2, [z[1, 1], z[1, 2], z[2, 1], z[2, 2]]) == E
  return z
end

function _gcdx(a::NfOrdElem, b::NfOrdElem)
  OK = parent(a)
  d = degree(OK)
  #@show a * OK + b * OK
  fl, g = isprincipal(a * OK + b * OK)
  @assert fl
  Ma = representation_matrix(a)
  Mb = representation_matrix(b)
  M = vcat(Ma, Mb)
  onee = matrix(FlintZZ, 1, d, coordinates(g))
  fl, v = can_solve_with_solution(M, onee, side = :left)
  @assert fl
  u = OK([v[1, i] for i in 1:d])
  v = OK([v[1, d + i] for i in 1:d])
  @assert g == u * a + v * b
  return g, u, v
end

################################################################################
#
#  Missing base ring functions
#
################################################################################

_base_ring(::NmodRing) = FlintZZ

_base_ring(::Nemo.FmpzModRing) = FlintZZ

################################################################################
#
#  Splitting in good and bad part
#
################################################################################

function _split_in_good_and_bad
end

function _multiply_with_idempotent(A, e)
  dec = decompose(A)
  idems = Int[]
  for i in 1:length(dec)
    B, mB = dec[i]
    if !iszero(mB(one(B)) * e)
      push!(idems, i)
    end
  end
  idems
end

function _my_direct_product(algebras)
  d = sum(Int[dim(A) for A in algebras])
  K = base_ring(algebras[1])
  maps = dense_matrix_type(K)[]
  pre_maps = dense_matrix_type(K)[]
  mt = zeros(K, d, d, d)
  offset = 0
  for l in 1:length(algebras)
    B = algebras[l]
    Bmult = multiplication_table(B, copy = false)
    dd = dim(B)
    mtB = multiplication_table(B)
    BtoA = zero_matrix(K, dim(B), d)
    AtoB = zero_matrix(K, d, dim(B))
    for i = 1:dd
      BtoA[i, offset + i] = one(K)
      AtoB[offset + i, i] = one(K)
      for j = 1:dd
        for k = 1:dd
          mt[i + offset, j + offset, k + offset] = Bmult[i, j, k]
        end
      end
    end
    offset += dd
    push!(maps, BtoA)
    push!(pre_maps, AtoB)
  end
  A = AlgAss(K, mt)
  A.decomposition = [ (algebras[i], hom(algebras[i], A, maps[i], pre_maps[i])) for i in 1:length(algebras) ]
  return A
end

function norm_one_units(M)
  A = algebra(M)
  K = base_ring(A)
end

################################################################################
#
#  Unit group generators
#
################################################################################

function _unit_group_generators(O)
  M = maximal_order(O)
  gens = _unit_group_generators_maximal(M)
  _, Y = _orbit_stabilizer(gens, one(algebra(O)), O)
  return Y
end

function _unit_group_generators_maximal(M)
  res = decompose(algebra(M))
  Mbas = basis(M)
  idems = [mB(one(B)) for (B, mB) in res]
  gens = elem_type(algebra(M))[]
  for i in 1:length(res)
    B, mB = res[i]
    MinB = Order(B, [(mB\(mB(one(B)) * elem_in_algebra(b))) for b in Mbas])
    UB = _unit_group_generators_maximal_simple(MinB)
    e = sum(idems[j] for j in 1:length(res) if j != i)
    @assert isone(e + mB(one(B)))
    for u in UB
      push!(gens, mB(u) + e)
    end
  end
  @assert all(u in M for u in gens)
  @assert all(inv(u) in M for u in gens)
  return gens
end

function _unit_group_generators_maximal_simple(M)
  A = algebra(M)
  ZA, ZAtoA = _as_algebra_over_center(A)
  if isdefined(A, :isomorphic_full_matrix_algebra)
    #@info "Full matrix algebra unit group"
    B, AtoB = A.isomorphic_full_matrix_algebra
    OB = _get_order_from_gens(B, [AtoB(elem_in_algebra(b)) for b in absolute_basis(M)])
    N, S = nice_order(OB)
    @assert basis_matrix(N) == identity_matrix(base_ring(B), dim(B))
    gens = [ B(u) for u in _GLn_generators(base_ring(OB), degree(B))]
    @assert all(b in N for b in gens)
    gens_adjusted = [ inv(S) * u * S for u in gens]
    @assert all(b in OB for b in gens_adjusted)
    gens_in_M = [ AtoB\u for u in gens_adjusted]
    @assert all(b in M for b in gens_in_M)
    return gens_in_M
 elseif dim(ZA) == 4 && !isdefined(A, :isomorphic_full_matrix_algebra)
    #@show A
    #@info "Quaternion case unit group"
    Q, QtoZA = isquaternion_algebra(ZA)
    MQ = _get_order_from_gens(Q, [QtoZA\(ZAtoA\(elem_in_algebra(b))) for b in absolute_basis(M)])
    _gens =  _unit_group_generators_quaternion(MQ)
    gens_in_M = [ ZAtoA(QtoZA(elem_in_algebra(u))) for u in _gens]
    @assert all(b in M for b in gens_in_M)
    return gens_in_M
  else
    throw(NotImplemented())
  end
end

function _SLn_generators(OK, n)
  K = nf(OK)
  res = dense_matrix_type(K)[]

  if n == 1
    return dense_matrix_type(K)[identity_matrix(K, 1)]
  end

  if n == 2
    r = unit_group_rank(OK)
    if r > 0
      # https://mathoverflow.net/questions/105857/generators-for-sl-2r-for-rings-of-integers-r
      B = basis(OK)
      for b in B
        push!(res, matrix(K, 2, 2, [1, elem_in_nf(b), 0, 1]))
        push!(res, matrix(K, 2, 2, [1, 0, elem_in_nf(b), 1]))
      end
      return res
    else
      if degree(K) > 1
        throw(NotImplemented())
      else
        # This is the case K = Q
        # SL(2, Z) (the modular group) is generated by S, T
        push!(res, matrix(K, 2, 2, [0, -1, 1, 0]))
        push!(res, matrix(K, 2, 2, [1, 1, 1, 0]))
        return res
      end
    end
  else
    # This is the case n >= 3
    # Follows from Bass, "K-Theory and stable algebra", Corollary 1.5
    d = degree(K)
    #
    # We find a small generating set of OK as Z-algebra
    found = false
    for i in 1:d
      for j in 1:10
        G = [elem_in_nf(rand(OK, 2)) for k in 1:i]
        fl,_ = defines_order(K, G)
        if !fl
          continue
        end
        OO = order(K, G)
        if abs(discriminant(OO)) == abs(discriminant(OK))
          found = true
          break
        end
      end
      if found
        break
      end
    end

    if !found
      B = elem_in_nf.(basis(OK))
    else
      B = G
      if !(one(OK) in B)
        push!(B, one(OK))
      end
    end

    for i in 1:n
      for j in 1:n
        if j == i
          continue
        end
        for b in B
          M = identity_matrix(K, n)
          M[i, j] = b
          push!(res, M)
        end
      end
    end
    return res
  end
end

function _GLn_generators(OK, n)
  K = nf(OK)
  if degree(K) == 1
    if n == 0
      return dense_matrix_type(K)[]
    elseif n == 1
      return dense_matrix_type(K)[matrix(K, 1, 1, [-1])]
    else
      # https://mathoverflow.net/questions/181366/minimal-number-of-generators-for-gln-mathbbz
      # The number should be reduced once more
      s1 = zero_matrix(K, n, n)
      for i in 2:nrows(s1)
        s1[i, i - 1] = 1
      end
      s1[1, n] = 1

      s3 = identity_matrix(K, n)
      s3[1, 2] = 1

      s4 = identity_matrix(K, n)
      s4[1, 1] = -1
      return [s1, s3, s4]
    end
  end

  if n == 2 && unit_group_rank(OK) == 0 && degree(K) == 2
    return _GLn_generators_quadratic(OK, n)
  end

  res = _SLn_generators(OK, n)
  U, mU = unit_group(OK)
  if n == 0
    return dense_matrix_type(K)[]
  end

  for i in 1:ngens(U)
    I = identity_matrix(K, n)
    I[1, 1] = elem_in_nf(mU(U[i]))
    push!(res, I)
  end

  return res
end

function _GLn_generators_quadratic(OK, n)
  d = discriminant(OK)
  _v = findfirst(z -> z[1] == d, __GLn_generators_quadratic)
  if _v === nothing
    throw(NotImplemented())
  end
  v = __GLn_generators_quadratic[_v]
  dn = v[2]
  L, = quadratic_field(-dn, cached = false)
  K = number_field(OK)
  fl, i = isisomorphic(L, K)
  res = dense_matrix_type(K)[]
  for w in v[3]
    mat = matrix(K, 2, 2, [i(L(u)) for u in w])
    @assert isunit(det(mat))
    push!(res, mat)
  end
  return res
end

global __GLn_generators_quadratic = [(-4, 1, [[[ 1, 0 ],[ 0, 0 ],[ 0, -1 ],[ 1, 0 ]],[[ 1, 0 ],[ 0, 1 ],[ 0, 0 ],[ 0, 1 ]],[[ 0, -1 ],[ 0, 1 ],[ 1, 0 ],[ -1, 1 ]]]),
(-8, 2, [[[ -1, 0 ],[ 1, 1 ],[ -1, 2 ],[ 4, -1 ]],[[ -1, 1 ],[ 1, 0 ],[ 0, 2 ],[ 1, -1 ]],[[ -1, 0 ],[ 0, 0 ],[ -1, 1 ],[ 1, 0 ]],[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]]]),
(-3, 3, [[[ 1, 0 ],[ -1//2, 1//2 ],[ 1//2, -1//2 ],[ -1//2, 1//2 ]],[[ -1//2, 1//2 ],[ -1//2, -1//2 ],[ 0, 0 ],[ -1//2, -1//2 ]],[[ 1//2, -1//2 ],[ -1//2, 1//2 ],[ 1//2, -1//2 ],[ 0, 0 ]]]),
(-20, 5, [[[ 0, 1 ],[ -2, 0 ],[ -2, 0 ],[ 0, -1 ]],[[ 1, 0 ],[ 0, 0 ],[ 0, 1 ],[ -1, 0 ]],[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ 0, 2 ],[ -4, -1 ],[ -4, 1 ],[ 0, -2 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 2, 0 ],[ 0, 1 ],[ 0, 1 ],[ -2, 0 ]]]),
(-24, 6, [[[ -2, -2 ],[ 3, 0 ],[ 3, -2 ],[ 2, 1 ]],[[ 1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ -3, 4 ],[ -7, -3 ],[ -10, -1 ],[ 7, -3 ]],[[ -11, -2 ],[ 11, -2 ],[ 0, -6 ],[ 11, 4 ]],[[ -2, 1 ],[ -1, -1 ],[ -3, 0 ],[ 1, -1 ]]]),
(-7, 7, [[[ 1, 0 ],[ -1, 0 ],[ 0, 0 ],[ -1, 0 ]],[[ 1, 0 ],[ -1//2, 1//2 ],[ 0, 0 ],[ -1, 0 ]],[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -1//2, -1//2 ],[ 1, 0 ],[ 1//2, -1//2 ],[ 1//2, 1//2 ]]]),
(-40, 10, [[[ 9, -2 ],[ 0, 4 ],[ 9, 1 ],[ -9, 2 ]],[[ -2, 1 ],[ -3, -1 ],[ -3, 0 ],[ 1, -1 ]],[[ -1, 0 ],[ 2, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -11, -2 ],[ 11, -2 ],[ 0, -4 ],[ 11, 2 ]],[[ 3, 1 ],[ -6, 0 ],[ 0, 1 ],[ -3, -1 ]]]),
(-11, 11, [[[ 5//2, 1//2 ],[ 0, -1 ],[ 2, 0 ],[ -3//2, -1//2 ]],[[ -1, 0 ],[ 1//2, -1//2 ],[ -1//2, 1//2 ],[ -3//2, -1//2 ]],[[ -3//2, 1//2 ],[ 2, 0 ],[ 1//2, 1//2 ],[ 1//2, -1//2 ]]]),
(-52, 13, [[[ -4, 0 ],[ 2, -1 ],[ -2, -1 ],[ 4, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -12, -2 ],[ 12, -3 ],[ 0, -3 ],[ 12, 1 ]],[[ 4, -4 ],[ 13, 2 ],[ 13, 2 ],[ -10, 3 ]],[[ -4, -3 ],[ 11, -1 ],[ 7, -2 ],[ 7, 2 ]],[[ 0, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ 0, -1 ],[ 3, 0 ],[ 4, 0 ],[ 0, 1 ]]]),
(-56, 14, [[[ -8, 0 ],[ 3, -2 ],[ -3, -2 ],[ 8, 0 ]],[[ 12, -2 ],[ 1, 2 ],[ 11, 2 ],[ -6, 1 ]],[[ 7, 1 ],[ -4, 1 ],[ -2, 3 ],[ -7, -1 ]],[[ 1, -1 ],[ 4, 0 ],[ 4, 0 ],[ 1, 1 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 1 ],[ -1, 0 ]],[[ 0, 4 ],[ -13, -2 ],[ -13, 2 ],[ 0, -4 ]]]),
(-15, 15, [[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ 1//2, -1//2 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 7//2, 1//2 ],[ 0, -1 ],[ 7//2, -1//2 ],[ -7//2, -1//2 ]],[[ 0, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]]]),
(-68, 17, [[[ -8, -5 ],[ 20, 0 ],[ 18, -4 ],[ 8, 5 ]],[[ 5, 0 ],[ -1, 1 ],[ 2, 2 ],[ -7, 0 ]],[[ -11, 2 ],[ -4, -3 ],[ -12, -2 ],[ 11, -2 ]],[[ 24, -5 ],[ 12, 6 ],[ 30, 5 ],[ -24, 5 ]],[[ -5, 1 ],[ -3, -2 ],[ -8, -1 ],[ 9, -2 ]],[[ 11, -7 ],[ 21, 4 ],[ 35, 0 ],[ -9, 7 ]],[[ -19, 8 ],[ -19, -8 ],[ -31, 1 ],[ 12, -7 ]],[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 5, 0 ],[ -2, 1 ],[ 3, -1 ],[ 2, 1 ]]]),
(-19, 19, [[[ 2, 0 ],[ -3//2, 1//2 ],[ 1//2, -1//2 ],[ 3//2, 1//2 ]],[[ -3//2, 1//2 ],[ -3//2, -1//2 ],[ -2, 0 ],[ 1//2, -1//2 ]],[[ -3, 0 ],[ 3//2, -1//2 ],[ -3, -1 ],[ 5, 0 ]],[[ -3//2, 1//2 ],[ -1//2, -1//2 ],[ -3, 0 ],[ 3//2, -1//2 ]]]),
(-84, 21, [[[ 13, 1 ],[ -12, 3 ],[ -2, 3 ],[ -16, -2 ]],[[ -8, -1 ],[ 8, -1 ],[ 0, -2 ],[ 8, 1 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ 20, 3 ],[ -14, 3 ],[ -12, 6 ],[ -20, -3 ]],[[ 0, -1 ],[ 5, 0 ],[ 4, 0 ],[ 0, 1 ]],[[ -13, -2 ],[ 7, -2 ],[ 12, -4 ],[ 13, 2 ]],[[ 2, -1 ],[ 4, 1 ],[ 4, 0 ],[ -2, 1 ]],[[ 5, 8 ],[ -40, 0 ],[ -33, 2 ],[ -5, -8 ]],[[ 5, 0 ],[ 0, 1 ],[ 0, 1 ],[ -4, 0 ]],[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ -26, -5 ],[ 30, -5 ],[ 16, -6 ],[ 26, 5 ]]]),
(-88, 22, [[[ -13, 3 ],[ -3, -3 ],[ -23, 0 ],[ 10, -3 ]],[[ -8, 2 ],[ -1, -2 ],[ -17, 0 ],[ 9, -2 ]],[[ 5, -1 ],[ 1, 1 ],[ 8, 0 ],[ -3, 1 ]],[[ -25, 3 ],[ 6, -6 ],[ -27, -2 ],[ 25, -3 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 1, 0 ],[ -1, 0 ],[ 2, 0 ],[ -1, 0 ]],[[ -19, 5 ],[ -5, -5 ],[ -38, 0 ],[ 19, -5 ]]]),
(-23, 23, [[[ 3//2, 1//2 ],[ 3//2, -1//2 ],[ 3, 0 ],[ -3//2, -1//2 ]],[[ 1, 0 ],[ 1//2, -1//2 ],[ 1, 0 ],[ -1//2, -1//2 ]],[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 5//2, 1//2 ],[ 5//2, -1//2 ],[ 5//2, -1//2 ],[ -5//2, -1//2 ]],[[ 0, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]]]),
(-104, 26, [[[ 5, 0 ],[ 1, 1 ],[ 3, 2 ],[ -10, 1 ]],[[ 7, -1 ],[ 7, 1 ],[ 9, 1 ],[ -2, 2 ]],[[ 7, 0 ],[ -1, 1 ],[ 1, 1 ],[ -4, 0 ]],[[ 3, -1 ],[ 3, 1 ],[ 6, 0 ],[ -3, 1 ]],[[ 25, -3 ],[ 18, 6 ],[ 13, 4 ],[ -25, 3 ]],[[ -7, -2 ],[ 9, -2 ],[ 6, -1 ],[ 7, 1 ]],[[ 23, 1 ],[ -9, 5 ],[ -2, 4 ],[ -23, -1 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ -26, 0 ],[ -5, -5 ],[ 5, -5 ],[ 26, 0 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]]]),
(-116, 29, [[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ -28, -3 ],[ 28, -3 ],[ 0, -6 ],[ 28, 3 ]],[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ -11, -2 ],[ 16, -1 ],[ 11, -2 ],[ 5, 3 ]],[[ -34, 0 ],[ 10, -5 ],[ -14, -7 ],[ 34, 0 ]],[[ 2, 1 ],[ -4, 0 ],[ -6, 1 ],[ -2, -1 ]],[[ 3, 3 ],[ -18, -1 ],[ -21, 2 ],[ 0, -5 ]],[[ 21, -2 ],[ 2, 4 ],[ 17, 2 ],[ -15, 2 ]],[[ -20, -2 ],[ 15, -2 ],[ -1, -6 ],[ 24, 2 ]],[[ -5, 2 ],[ -9, -2 ],[ -10, 0 ],[ 5, -2 ]],[[ -18, 4 ],[ -11, -4 ],[ -25, -2 ],[ 17, -3 ]],[[ -13, 3 ],[ -7, -2 ],[ -20, -1 ],[ 7, -2 ]]]),
(-120, 30, [[[ 3, 1 ],[ -5, 0 ],[ -5, 1 ],[ -2, -1 ]],[[ 233, 83 ],[ -466, 0 ],[ -327, 83 ],[ -233, -83 ]],[[ 41, -4 ],[ 0, 8 ],[ 41, 5 ],[ -41, 4 ]],[[ 11, -1 ],[ 5, 2 ],[ 6, 2 ],[ -11, 1 ]],[[ 29, -3 ],[ 6, 6 ],[ 25, 4 ],[ -29, 3 ]],[[ 4, -1 ],[ 3, 1 ],[ 9, 1 ],[ -8, 1 ]],[[ 0, 4 ],[ -19, -2 ],[ -19, 2 ],[ 0, -4 ]],[[ 50, 18 ],[ -101, 0 ],[ -71, 18 ],[ -51, -18 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -97, 9 ],[ 0, -18 ],[ -100, -14 ],[ 103, -9 ]],[[ -23, 1 ],[ 4, -4 ],[ -16, -4 ],[ 25, -1 ]],[[ 5, 0 ],[ -1, 1 ],[ 1, 1 ],[ -6, 0 ]]]),
(-31, 31, [[[ -1//2, -1//2 ],[ 3, 0 ],[ 3, 0 ],[ -1//2, 1//2 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ -1//2, -1//2 ]],[[ 11//2, -1//2 ],[ 1//2, 3//2 ],[ 7//2, 1//2 ],[ -11//2, 1//2 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 3//2, -1//2 ],[ 3//2, 1//2 ],[ 3, 0 ],[ -3//2, 1//2 ]],[[ 3, 0 ],[ -3//2, 1//2 ],[ 3//2, 1//2 ],[ -3, 0 ]]]),
(-132, 33, [[[ 11, 0 ],[ -1, 2 ],[ 1, 2 ],[ -12, 0 ]],[[ 34, 0 ],[ 0, 5 ],[ 0, 7 ],[ -34, 0 ]],[[ -10, 0 ],[ 0, -1 ],[ 0, -3 ],[ 10, 0 ]],[[ 20, 1 ],[ -7, 3 ],[ -4, 4 ],[ -20, -1 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 0, 1 ],[ -4, 0 ],[ -8, 0 ],[ 0, -1 ]],[[ -55, 2 ],[ -2, -9 ],[ -17, -11 ],[ 60, -1 ]],[[ -33, 7 ],[ -31, -6 ],[ -50, -5 ],[ 32, -7 ]],[[ 0, 2 ],[ -10, -1 ],[ -10, 1 ],[ 0, -2 ]],[[ 1, 1 ],[ -5, 0 ],[ -7, 0 ],[ 1, -1 ]],[[ 0, 4 ],[ -23, 0 ],[ -23, 0 ],[ 0, -4 ]],[[ 7, 1 ],[ -6, 1 ],[ -5, 2 ],[ -10, -1 ]],[[ -32, 3 ],[ -12, -6 ],[ -22, -5 ],[ 32, -3 ]],[[ 100, 1 ],[ -20, 15 ],[ 0, 20 ],[ -100, -3 ]]]),
(-136, 34, [[[ 31, -3 ],[ 6, 6 ],[ 27, 4 ],[ -31, 3 ]],[[ 5, 2 ],[ -9, 0 ],[ -13, 2 ],[ -4, -2 ]],[[ -17, 5 ],[ -11, -6 ],[ -31, 1 ],[ 18, -5 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 13, -6 ],[ 32, 4 ],[ 31, -2 ],[ 3, 6 ]],[[ 5, 2 ],[ -10, 0 ],[ -11, 2 ],[ -5, -2 ]],[[ 29, -5 ],[ 15, 5 ],[ 46, 4 ],[ -29, 5 ]],[[ 11, 3 ],[ -16, 1 ],[ -18, 3 ],[ -11, -3 ]],[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ -1, -1 ],[ 6, 0 ],[ 6, 0 ],[ -1, 1 ]],[[ 7, 4 ],[ -26, 0 ],[ -29, 3 ],[ -9, -6 ]]]),
(-35, 35, [[[ -3, -1 ],[ 13//2, -1//2 ],[ 11//2, -1//2 ],[ 3, 1 ]],[[ 9//2, -1//2 ],[ 1//2, 1//2 ],[ 3//2, 1//2 ],[ -2, 0 ]],[[ 5//2, -1//2 ],[ 3//2, 1//2 ],[ 4, 0 ],[ -3//2, 1//2 ]],[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]]]),
(-148, 37, [[[ -7, 0 ],[ 2, -1 ],[ -2, -1 ],[ 6, 0 ]],[[ 25, -6 ],[ 25, 6 ],[ 48, 1 ],[ -23, 7 ]],[[ 19, -5 ],[ 14, 5 ],[ 39, 0 ],[ -20, 5 ]],[[ -36, 0 ],[ 0, -5 ],[ 0, -7 ],[ 36, 0 ]],[[ -7, 2 ],[ -7, -2 ],[ -14, 0 ],[ 7, -2 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -31, 2 ],[ 4, -5 ],[ -21, -4 ],[ 29, -1 ]],[[ 84, 1 ],[ -42, 11 ],[ 42, 13 ],[ -84, 0 ]],[[ -32, 0 ],[ 10, -5 ],[ -10, -5 ],[ 32, 0 ]],[[ 34, 3 ],[ -24, 5 ],[ -12, 6 ],[ -34, -3 ]]]),
(-152, 38, [[[ 1, 1 ],[ -5, 0 ],[ -7, 1 ],[ -4, -1 ]],[[ 18, 1 ],[ -15, 2 ],[ 1, 4 ],[ -22, -2 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ 3, 2 ],[ -13, 0 ],[ -17, 1 ],[ -2, -3 ]],[[ 39, 3 ],[ -39, 4 ],[ 0, 7 ],[ -39, -4 ]],[[ -30, -2 ],[ 27, -3 ],[ 9, -5 ],[ 21, 4 ]],[[ -11, 3 ],[ -10, -3 ],[ -22, 0 ],[ 11, -3 ]],[[ -26, 6 ],[ -17, -7 ],[ -41, -3 ],[ 39, -4 ]],[[ 37, -3 ],[ 18, 6 ],[ 19, 6 ],[ -37, 3 ]],[[ 9, -2 ],[ 5, 1 ],[ 14, 1 ],[ -5, 1 ]],[[ -11, -1 ],[ 6, -1 ],[ 6, -2 ],[ 7, 1 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 45, -7 ],[ 14, 10 ],[ 54, 5 ],[ -55, 5 ]],[[ 11, 3 ],[ -21, 0 ],[ -11, 3 ],[ -10, -3 ]]]),
(-39, 39, [[[ -5, 0 ],[ 11//2, -3//2 ],[ -7//2, -1//2 ],[ 19//2, -1//2 ]],[[ -5//2, -1//2 ],[ 5, 0 ],[ 1//2, -1//2 ],[ 5//2, 1//2 ]],[[ -11//2, 1//2 ],[ 0, -1 ],[ -11//2, -1//2 ],[ 11//2, -1//2 ]],[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ 3//2, -1//2 ],[ -1//2, 1//2 ],[ 1, 0 ],[ -1, 0 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ 7//2, 1//2 ],[ -7, 0 ],[ 1//2, 1//2 ],[ -7//2, -1//2 ]],[[ 2, 1 ],[ -21//2, -1//2 ],[ -5//2, 1//2 ],[ -2, -1 ]]]),
(-164, 41, [[[ -61, 2 ],[ 25, -9 ],[ -35, -6 ],[ 52, -1 ]],[[ -7, -2 ],[ 17, 0 ],[ 18, -2 ],[ 3, 4 ]],[[ 128, 3 ],[ -109, 17 ],[ 51, 15 ],[ -128, -3 ]],[[ 3, 1 ],[ -7, 0 ],[ -4, 1 ],[ -4, -1 ]],[[ -81, 25 ],[ -84, -29 ],[ -154, 1 ],[ 104, -22 ]],[[ 26, -5 ],[ 18, 7 ],[ 33, 4 ],[ -45, 3 ]],[[ 48, -3 ],[ -3, 7 ],[ 45, 4 ],[ -37, 4 ]],[[ -74, 11 ],[ -29, -18 ],[ -84, -4 ],[ 74, -11 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -13, -8 ],[ 44, 0 ],[ 57, -4 ],[ 9, 8 ]],[[ 8, 13 ],[ -89, -6 ],[ -51, 7 ],[ -17, -12 ]],[[ -48, -19 ],[ 104, -2 ],[ 132, -15 ],[ 48, 19 ]],[[ 25, -14 ],[ 64, 6 ],[ 74, -5 ],[ 9, 10 ]],[[ -12, -7 ],[ 39, 0 ],[ 23, -5 ],[ 21, 4 ]],[[ 56, -3 ],[ -23, 10 ],[ 37, 10 ],[ -84, -2 ]]]),
(-168, 42, [[[ -55, -6 ],[ 55, -3 ],[ 0, -12 ],[ 55, 6 ]],[[ -7, 2 ],[ -5, -2 ],[ -18, 0 ],[ 11, -2 ]],[[ 449, 40 ],[ -449, 40 ],[ 0, 80 ],[ -449, -40 ]],[[ -11, -1 ],[ 11, -1 ],[ 4, -3 ],[ 15, 2 ]],[[ 97, 0 ],[ -51, 13 ],[ 51, 13 ],[ -100, 0 ]],[[ 23, 0 ],[ -14, 3 ],[ 14, 3 ],[ -25, 0 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ 1, 6 ],[ -34, -3 ],[ -37, 4 ],[ -3, -7 ]],[[ 37, 5 ],[ -51, 2 ],[ -4, 9 ],[ -49, -6 ]],[[ 28, 72 ],[ -429, -42 ],[ -333, 42 ],[ -28, -72 ]],[[ -13, -2 ],[ 13, 0 ],[ 0, -4 ],[ 13, 2 ]],[[ -29, 7 ],[ -21, -7 ],[ -58, 0 ],[ 29, -7 ]]]),
(-43, 43, [[[ -3//2, -1//2 ],[ 4, 0 ],[ 3//2, -1//2 ],[ 5//2, 1//2 ]],[[ -5//2, 1//2 ],[ -1, -1 ],[ -3, 0 ],[ 7//2, -1//2 ]],[[ -3//2, -1//2 ],[ 4, 0 ],[ -3, 0 ],[ 3//2, -1//2 ]],[[ -2, 4 ],[ -49//2, -7//2 ],[ -37//2, 3//2 ],[ 5, -4 ]]]),
(-184, 46, [[[ 133, 6 ],[ -160, 14 ],[ 35, 19 ],[ -159, -12 ]],[[ -31, 14 ],[ -71, -16 ],[ -72, 4 ],[ 31, -14 ]],[[ 41, 7 ],[ -82, 0 ],[ -7, 7 ],[ -41, -7 ]],[[ 61, 2 ],[ -48, 7 ],[ 20, 8 ],[ -61, -2 ]],[[ 0, 8 ],[ -47, -4 ],[ -47, 4 ],[ 0, -8 ]],[[ 11, 0 ],[ -10, 2 ],[ 5, 1 ],[ -13, 0 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ -91, 6 ],[ 35, -19 ],[ -67, -5 ],[ 92, -6 ]],[[ 64, -7 ],[ 5, 12 ],[ 73, 4 ],[ -64, 7 ]],[[ -7, -4 ],[ 33, 2 ],[ 18, -3 ],[ 7, 5 ]],[[ -87, -8 ],[ 95, -7 ],[ -15, -11 ],[ 74, 4 ]],[[ 95, 4 ],[ -77, 10 ],[ 28, 10 ],[ -75, -2 ]],[[ -50, -8 ],[ 99, 0 ],[ 5, -8 ],[ 49, 8 ]]]),
(-47, 47, [[[ -10, -1 ],[ 10, -1 ],[ 2, -2 ],[ 12, 1 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ 7//2, -1//2 ],[ 7//2, 1//2 ],[ 7//2, 1//2 ],[ -7//2, 1//2 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 5//2, 1//2 ],[ -9//2, 1//2 ],[ -5//2, 1//2 ],[ -9//2, -1//2 ]],[[ 4, 1 ],[ -8, 0 ],[ -4, 1 ],[ -4, -1 ]],[[ 3, 0 ],[ -3//2, 1//2 ],[ 3//2, 1//2 ],[ -5, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]]]),
(-51, 51, [[[ 8, 4 ],[ 41//2, -11//2 ],[ 33//2, 3//2 ],[ -7, -4 ]],[[ 23, -3 ],[ -47, 0 ],[ 2, -3 ],[ -24, 3 ]],[[ 119//2, -5//2 ],[ -82, -5 ],[ 23, -5 ],[ -117//2, 5//2 ]],[[ -21//2, 1//2 ],[ 8, 1 ],[ -4, 1 ],[ 8, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 148, -37 ],[ -414, 22 ],[ -77//2, -57//2 ],[ -148, 37 ]],[[ 0, -1 ],[ -7, 1 ],[ -7//2, -1//2 ],[ 0, 1 ]]]),
(-212, 53, [[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -12, 1 ],[ 17, 2 ],[ 0, 2 ],[ 22, -1 ]],[[ 67, -1 ],[ -41, -8 ],[ 28, -5 ],[ -48, -1 ]],[[ -160, -43 ],[ -212, 42 ],[ -320, 0 ],[ 160, 41 ]],[[ 937, 36 ],[ -216, -144 ],[ 602, -89 ],[ -937, -36 ]],[[ 54, 5 ],[ 0, -10 ],[ 54, -3 ],[ -54, -5 ]],[[ -14, 3 ],[ 28, 0 ],[ 10, 3 ],[ 14, -3 ]],[[ -18, 56 ],[ 358, -25 ],[ 322, 25 ],[ 0, -50 ]],[[ -21, 1 ],[ 25, 2 ],[ -4, 3 ],[ 25, -2 ]],[[ -15, 10 ],[ 79, -3 ],[ 37, 4 ],[ 10, -7 ]],[[ -78, -11 ],[ 0, 22 ],[ -110, 4 ],[ 142, 11 ]],[[ -21, 8 ],[ 63, -2 ],[ 31, 4 ],[ 8, -6 ]],[[ -1, 0 ],[ 2, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ 0, -22 ],[ -148, 11 ],[ -130, -11 ],[ -9, 22 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 4, 1 ],[ 6, -1 ],[ 7, 0 ],[ -3, -1 ]]]),
(-55, 55, [[[ 13//2, -1//2 ],[ 0, 1 ],[ 13//2, 1//2 ],[ -13//2, 1//2 ]],[[ 15//2, -1//2 ],[ -7//2, 3//2 ],[ 7//2, 1//2 ],[ -7, 0 ]],[[ 9//2, 1//2 ],[ -7, 0 ],[ -1//2, 1//2 ],[ -5//2, -1//2 ]],[[ -3//2, 1//2 ],[ -7//2, -1//2 ],[ -3, 0 ],[ 3//2, -1//2 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 0, 1 ],[ -12, -1 ],[ -9//2, 1//2 ],[ -3//2, -3//2 ]],[[ 0, -1 ],[ 31//2, 1//2 ],[ 9//2, -1//2 ],[ 11//2, 3//2 ]]]),
(-228, 57, [[[ 757, -11 ],[ -384, -81 ],[ 251, -100 ],[ -748, 13 ]],[[ 155, 8 ],[ -12, -21 ],[ 128, -16 ],[ -157, -8 ]],[[ 352, 3 ],[ -141, -43 ],[ 175, -43 ],[ -370, -1 ]],[[ 44, 3 ],[ 3, -6 ],[ 40, -4 ],[ -40, -3 ]],[[ -13115, 1739 ],[ 17666, 751 ],[ 5704, 2339 ],[ 13102, -1740 ]],[[ 355, 18 ],[ -41, -50 ],[ 283, -38 ],[ -384, -16 ]],[[ -9, 0 ],[ 5, 1 ],[ -5, 1 ],[ 9, 0 ]],[[ -247, 20 ],[ 231, 20 ],[ 32, 40 ],[ 247, -20 ]],[[ -17913, 638 ],[ 12469, 1819 ],[ -3899, 2404 ],[ 17926, -639 ]],[[ 313, 22 ],[ 4, -47 ],[ 288, -26 ],[ -307, -22 ]],[[ 53, 4 ],[ 8, -8 ],[ 48, -5 ],[ -53, -4 ]],[[ 79, 7 ],[ 15, -12 ],[ 84, -7 ],[ -80, -7 ]],[[ -85, -50 ],[ -294, 31 ],[ -388, -12 ],[ 85, 50 ]],[[ 21, -8 ],[ -59, 1 ],[ -50, -6 ],[ -17, 8 ]],[[ -107, -5 ],[ 11, 14 ],[ -84, 11 ],[ 104, 5 ]],[[ -105, -8 ],[ -4, 17 ],[ -109, 9 ],[ 118, 9 ]],[[ -91, -6 ],[ -2, 13 ],[ -84, 9 ],[ 94, 6 ]]]),
(-232, 58, [[[ 37, 0 ],[ -12, 4 ],[ 12, 4 ],[ -29, 0 ]],[[ 16, 0 ],[ -5, 2 ],[ 5, 2 ],[ -16, 0 ]],[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -1, -2 ],[ 16, 0 ],[ 14, -1 ],[ 7, 2 ]],[[ 44, 2 ],[ -35, 4 ],[ -9, 6 ],[ -35, -4 ]],[[ 37, 9 ],[ -74, 0 ],[ -45, 9 ],[ -37, -9 ]],[[ -345, 8 ],[ 73, -45 ],[ -226, -36 ],[ 339, -14 ]],[[ 15, 2 ],[ -23, 1 ],[ -15, 2 ],[ -8, -3 ]],[[ 39, 2 ],[ -29, 4 ],[ -9, 5 ],[ -32, -3 ]],[[ -1451, 110 ],[ 0, -220 ],[ -1451, -110 ],[ 1451, -110 ]],[[ -1, 5 ],[ -35, -2 ],[ -43, 2 ],[ 2, -6 ]],[[ 22, 0 ],[ -7, 3 ],[ 7, 3 ],[ -26, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 43, 0 ],[ -21, 5 ],[ 21, 5 ],[ -44, 0 ]]]),
(-59, 59, [[[ 1, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ 2, 0 ],[ 1//2, 1//2 ],[ 3//2, 1//2 ],[ -15//2, 1//2 ]],[[ 23//2, -1//2 ],[ 0, 1 ],[ 9, 1 ],[ -13//2, 1//2 ]],[[ 0, -1 ],[ 12, 0 ],[ 5, 0 ],[ 0, 1 ]],[[ -5//2, -1//2 ],[ 5, 0 ],[ -4, 0 ],[ 5//2, -1//2 ]],[[ -1//2, -1//2 ],[ 4, 0 ],[ 4, 0 ],[ -1//2, 1//2 ]]]),
(-244, 61, [[[ -10, -3 ],[ 25, 0 ],[ 16, -3 ],[ 15, 3 ]],[[ 8, 1 ],[ -9, 1 ],[ -6, 2 ],[ -16, -1 ]],[[ -62, 0 ],[ 0, -9 ],[ 0, -7 ],[ 62, 0 ]],[[ 59, 4 ],[ -38, 7 ],[ -24, 8 ],[ -59, -4 ]],[[ -31, 4 ],[ -31, -4 ],[ -47, -2 ],[ 16, -6 ]],[[ -92, -15 ],[ 120, -11 ],[ 49, -18 ],[ 137, 7 ]],[[ 86, 18 ],[ -173, 0 ],[ -71, 18 ],[ -87, -18 ]],[[ 18, 0 ],[ -9, 2 ],[ 9, 2 ],[ -18, 0 ]],[[ 60, 11 ],[ -88, 7 ],[ -42, 13 ],[ -98, -6 ]],[[ -10, -1 ],[ 9, -1 ],[ 7, -1 ],[ 6, 1 ]],[[ -40, 0 ],[ 2, -5 ],[ -18, -5 ],[ 39, -2 ]],[[ 84, 0 ],[ -46, 9 ],[ 46, 9 ],[ -84, 0 ]],[[ -88, -12 ],[ 107, -12 ],[ 31, -16 ],[ 137, 5 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ 5, 1 ],[ -9, 0 ],[ -9, 2 ],[ -8, -2 ]],[[ -59, -11 ],[ 99, 0 ],[ 40, -13 ],[ 58, 11 ]]]),
(-248, 62, [[[ 319, 10 ],[ -230, 30 ],[ 89, 39 ],[ -311, -10 ]],[[ 603, -8 ],[ -250, 71 ],[ 350, 61 ],[ -597, 8 ]],[[ 69, -65 ],[ 412, 41 ],[ 470, -25 ],[ -69, 65 ]],[[ -63, -4 ],[ 63, -6 ],[ 0, -8 ],[ 63, 4 ]],[[ 78, -9 ],[ 33, 13 ],[ 99, 4 ],[ -71, 10 ]],[[ 8, 0 ],[ -1, 1 ],[ 1, 1 ],[ -8, 0 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 113, -25 ],[ 117, 25 ],[ 224, 0 ],[ -111, 25 ]],[[ 41, -3 ],[ 9, 8 ],[ 41, 3 ],[ -50, 5 ]],[[ 67, 42 ],[ -327, -14 ],[ -246, 28 ],[ -69, -42 ]],[[ 331, -115 ],[ 626, 95 ],[ 929, -21 ],[ -325, 114 ]],[[ 203, -15 ],[ 0, 30 ],[ 200, 14 ],[ -197, 15 ]],[[ 377, 81 ],[ -754, 0 ],[ -351, 81 ],[ -377, -81 ]],[[ 181, 39 ],[ -362, 0 ],[ -170, 39 ],[ -181, -39 ]],[[ -23, 3 ],[ -19, -2 ],[ -31, -1 ],[ 4, -3 ]],[[ -11, -2 ],[ 13, -1 ],[ 9, -2 ],[ 12, 1 ]],[[ 301, 7 ],[ -200, 30 ],[ 100, 36 ],[ -299, -7 ]],[[ 116, -28 ],[ 133, 27 ],[ 249, 1 ],[ -133, 27 ]],[[ 5, -1 ],[ 6, 1 ],[ 8, 0 ],[ -3, 1 ]]]),
(-260, 65, [[[ 4, -6 ],[ -59, 2 ],[ -35, -2 ],[ -4, 6 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -61, 4 ],[ 40, 7 ],[ 24, 8 ],[ 61, -4 ]],[[ 7, 0 ],[ -2, -1 ],[ 2, -1 ],[ -10, 0 ]],[[ -14, 1 ],[ 14, 1 ],[ 0, 2 ],[ 14, -1 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ -64, 0 ],[ 0, 9 ],[ 0, 7 ],[ 64, 0 ]],[[ -2, 6 ],[ 41, 0 ],[ 47, 2 ],[ 12, -5 ]],[[ 1, -3 ],[ -26, 1 ],[ -20, -1 ],[ -1, 3 ]],[[ 206, 19 ],[ 108, -23 ],[ 201, -29 ],[ -213, -18 ]],[[ -98, 15 ],[ 178, 7 ],[ 64, 14 ],[ 98, -15 ]],[[ -46, -3 ],[ -16, 5 ],[ -22, 3 ],[ 22, 2 ]],[[ 92, 9 ],[ 55, -10 ],[ 61, -5 ],[ -37, -6 ]],[[ 224, 7 ],[ 40, -24 ],[ 96, -32 ],[ -224, -9 ]],[[ 6, 0 ],[ 0, -1 ],[ 0, -1 ],[ -11, 0 ]],[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 26, 0 ],[ -8, -3 ],[ 8, -3 ],[ -25, 0 ]],[[ 0, 10 ],[ 79, -2 ],[ 79, 2 ],[ 0, -10 ]],[[ 10, 1 ],[ 6, -2 ],[ 9, -1 ],[ -14, -1 ]],[[ -4, -1 ],[ -6, 1 ],[ -8, 0 ],[ 4, 1 ]],[[ -33, 0 ],[ 9, 4 ],[ -9, 4 ],[ 34, 0 ]],[[ 2, 1 ],[ 12, -1 ],[ 5, 0 ],[ -3, -1 ]]]),
(-264, 66, [[[ 15, -1 ],[ -2, 2 ],[ 22, 2 ],[ -25, 1 ]],[[ 20, -4 ],[ 17, 3 ],[ 49, 1 ],[ -21, 4 ]],[[ 273, -14 ],[ -4, 28 ],[ 236, 21 ],[ -193, 14 ]],[[ -11, 5 ],[ -25, -4 ],[ -40, 2 ],[ 11, -5 ]],[[ 423, 54 ],[ -436, 21 ],[ -313, 87 ],[ -409, -53 ]],[[ -32, 5 ],[ -17, -6 ],[ -49, -2 ],[ 40, -4 ]],[[ 75, -4 ],[ -4, 9 ],[ 71, 5 ],[ -61, 5 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -407, -8 ],[ 272, -32 ],[ -213, -49 ],[ 407, 8 ]],[[ -5, 33 ],[ -194, -19 ],[ -321, 16 ],[ 85, -38 ]],[[ 177, -13 ],[ -20, 24 ],[ 199, 10 ],[ -175, 13 ]],[[ 4, -1 ],[ 5, 1 ],[ 9, 0 ],[ -5, 1 ]],[[ -120, 9 ],[ -17, -20 ],[ -143, -7 ],[ 131, -15 ]],[[ -1312, -68 ],[ 1159, -81 ],[ -387, -181 ],[ 1312, 68 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ 75, -19 ],[ 124, 19 ],[ 148, 0 ],[ -73, 19 ]],[[ -77, 3 ],[ 14, -10 ],[ -70, -6 ],[ 77, -5 ]],[[ -200, -10 ],[ 127, -15 ],[ -7, -35 ],[ 214, 11 ]],[[ -16, -8 ],[ 57, 3 ],[ 45, -7 ],[ 17, 8 ]],[[ -390, -23 ],[ 251, -27 ],[ 23, -69 ],[ 390, 23 ]],[[ 103, -44 ],[ 225, 22 ],[ 372, -18 ],[ -5, 38 ]],[[ -11, 14 ],[ -78, -9 ],[ -177, 5 ],[ 71, -19 ]]]),
(-67, 67, [[[ 11//2, -3//2 ],[ -13, 0 ],[ -17//2, -3//2 ],[ -15//2, 3//2 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -5//2, -1//2 ],[ -3//2, 1//2 ],[ -6, 0 ],[ 7//2, 1//2 ]],[[ 0, -7 ],[ -99//2, 7//2 ],[ -109//2, -7//2 ],[ 5//2, 15//2 ]]]),
(-276, 69, [[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ -15, -4 ],[ 35, 0 ],[ 23, -4 ],[ 20, 4 ]],[[ 58, 13 ],[ -145, 1 ],[ -58, 13 ],[ -87, -14 ]],[[ -142, -89 ],[ 708, 35 ],[ 532, -62 ],[ 142, 89 ]],[[ -56, 15 ],[ -92, -11 ],[ -134, 2 ],[ 30, -15 ]],[[ -46, -15 ],[ 122, 3 ],[ 79, -13 ],[ 47, 14 ]],[[ -57, -23 ],[ 181, 6 ],[ 125, -18 ],[ 57, 21 ]],[[ 34, 3 ],[ -44, 3 ],[ -23, 4 ],[ -25, -5 ]],[[ -49, 13 ],[ -65, -12 ],[ -117, 2 ],[ 49, -13 ]],[[ -11, 2 ],[ -7, -2 ],[ -22, 0 ],[ 11, -2 ]],[[ 22, 1 ],[ -22, 3 ],[ 0, 2 ],[ -22, -1 ]],[[ -50, 0 ],[ 26, -5 ],[ -26, -5 ],[ 48, 0 ]],[[ 12, -1 ],[ 5, 1 ],[ 13, 1 ],[ -6, 1 ]],[[ -5, 3 ],[ -24, -1 ],[ -24, 1 ],[ -5, -3 ]],[[ 3, -9 ],[ 62, 3 ],[ 80, -3 ],[ -3, 9 ]],[[ 0, 0 ],[ -1, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ -42, 1 ],[ 16, -5 ],[ -22, -6 ],[ 56, 1 ]],[[ -120, -9 ],[ 127, -8 ],[ -7, -17 ],[ 127, 8 ]],[[ 36, -25 ],[ 151, 17 ],[ 194, -9 ],[ -43, 24 ]],[[ -50, -2 ],[ 43, -4 ],[ 15, -6 ],[ 34, 5 ]],[[ -44, -3 ],[ 38, -4 ],[ 9, -6 ],[ 44, 3 ]]]),
(-280, 70, [[[ 53, 9 ],[ -106, 0 ],[ -27, 9 ],[ -53, -9 ]],[[ -31, 1 ],[ 8, -4 ],[ -18, -2 ],[ 25, -1 ]],[[ -43, 0 ],[ 30, -6 ],[ -20, -4 ],[ 53, 0 ]],[[ -35, -2 ],[ 44, -4 ],[ -4, -4 ],[ 45, 2 ]],[[ 107, -33 ],[ 199, 32 ],[ 258, -6 ],[ -107, 33 ]],[[ -5, -1 ],[ 12, 0 ],[ 3, -1 ],[ 7, 1 ]],[[ -8, -3 ],[ 33, 2 ],[ 17, -2 ],[ 0, 4 ]],[[ 31, -14 ],[ 95, 13 ],[ 96, -4 ],[ -31, 14 ]],[[ -48, -4 ],[ 63, -3 ],[ 7, -5 ],[ 36, 4 ]],[[ 33, 0 ],[ -20, 4 ],[ 10, 2 ],[ -23, 0 ]],[[ -41, 17 ],[ -117, -15 ],[ -123, 4 ],[ 40, -17 ]],[[ -7, -3 ],[ 27, 1 ],[ 13, -1 ],[ 0, 2 ]],[[ -30, -4 ],[ 49, -1 ],[ 11, -3 ],[ 17, 3 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ 7, 1 ],[ -15, 0 ],[ -1, 1 ],[ -8, -1 ]],[[ 64, 90 ],[ -765, -48 ],[ -525, 48 ],[ -64, -90 ]],[[ -4, -2 ],[ 19, 1 ],[ 11, -1 ],[ 0, 2 ]],[[ -29, -2 ],[ 29, -2 ],[ 0, -4 ],[ 29, 2 ]],[[ 5, -1 ],[ 11, 2 ],[ 9, 0 ],[ -8, 2 ]],[[ -24, -15 ],[ 137, 6 ],[ 83, -9 ],[ 25, 15 ]]]),
(-71, 71, [[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ -7//2, -3//2 ],[ -7//2, 3//2 ],[ -19//2, -1//2 ],[ 6, 1 ]],[[ 27//2, 1//2 ],[ -7, -2 ],[ 7//2, -1//2 ],[ -7, 0 ]],[[ 1, 0 ],[ -2, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ 19//2, -1//2 ],[ -19//2, -1//2 ],[ 2, -1 ],[ -15//2, 1//2 ]],[[ -8, -1 ],[ -1, 2 ],[ -8, 0 ],[ 8, 1 ]],[[ -7//2, 3//2 ],[ 16, -1 ],[ 9//2, 1//2 ],[ 0, -1 ]],[[ 0, 7 ],[ 59, -7 ],[ 59//2, 7//2 ],[ 0, -7 ]],[[ 5//2, 1//2 ],[ 5//2, -1//2 ],[ 5, 0 ],[ -5//2, -1//2 ]]]),
(-292, 73, [[[ -30, 7 ],[ -37, -7 ],[ -52, 1 ],[ 21, -6 ]],[[ -316, -163 ],[ 1738, 142 ],[ 474, -98 ],[ 316, 163 ]],[[ 4, -3 ],[ 19, 4 ],[ 15, -2 ],[ -2, 4 ]],[[ 299, 4 ],[ -265, 31 ],[ 128, 24 ],[ -299, -4 ]],[[ 1, 0 ],[ -2, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ -546, 64 ],[ 53, -134 ],[ -601, 8 ],[ 591, -79 ]],[[ -72, -3 ],[ 80, -6 ],[ -31, -6 ],[ 74, 1 ]],[[ -20, -29 ],[ 237, 12 ],[ 202, -15 ],[ 19, 29 ]],[[ 6, 1 ],[ -12, 0 ],[ -3, 1 ],[ -6, -1 ]],[[ -53, -5 ],[ 103, 0 ],[ -8, -5 ],[ 50, 5 ]],[[ 22, -2 ],[ -7, 4 ],[ 21, 0 ],[ -20, 2 ]],[[ 0, 12 ],[ -95, -6 ],[ -83, 6 ],[ -6, -12 ]],[[ -9, -1 ],[ 17, 0 ],[ 0, -1 ],[ 8, 1 ]],[[ -28, -7 ],[ 72, 4 ],[ 38, -6 ],[ 4, 9 ]],[[ -616, 192 ],[ -962, -283 ],[ -1050, 63 ],[ 616, -192 ]],[[ -14, 5 ],[ -22, -7 ],[ -27, 2 ],[ 15, -5 ]],[[ 0, 10 ],[ -74, -5 ],[ -74, 5 ],[ 0, -10 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ 43, 0 ],[ -49, 5 ],[ 22, 4 ],[ -59, -2 ]]]),
(-296, 74, [[[ -7, 7 ],[ 60, -1 ],[ 60, 1 ],[ -7, -7 ]],[[ 10, 3 ],[ 25, -1 ],[ 27, 0 ],[ 1, -3 ]],[[ 3, -1 ],[ -4, 0 ],[ -18, -1 ],[ -1, 1 ]],[[ -30, 3 ],[ 31, 3 ],[ 17, 6 ],[ 49, -3 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 209, -13 ],[ -143, -22 ],[ -78, -26 ],[ -209, 13 ]],[[ 23, 1 ],[ 7, -3 ],[ 27, -4 ],[ -40, -3 ]],[[ 0, 1 ],[ 5, 0 ],[ 15, 0 ],[ 0, -1 ]],[[ 0, 0 ],[ -1, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ -7, 1 ],[ 12, 1 ],[ 6, 1 ],[ 11, -1 ]],[[ -1, 2 ],[ 16, 0 ],[ 18, 1 ],[ 7, -2 ]],[[ -29, 0 ],[ 0, 3 ],[ 0, 3 ],[ 23, 0 ]],[[ -48, -2 ],[ -21, 7 ],[ -21, 5 ],[ 54, 3 ]],[[ 83, 14 ],[ 104, -12 ],[ 133, -7 ],[ -83, -14 ]],[[ -41, -4 ],[ -33, 5 ],[ -27, 4 ],[ 36, 3 ]],[[ 7, 1 ],[ 10, -1 ],[ 22, -1 ],[ -11, -3 ]],[[ -5, -1 ],[ -5, 1 ],[ -10, 0 ],[ 5, 1 ]],[[ -8, -4 ],[ -17, 1 ],[ -35, 1 ],[ 9, 2 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 82, 0 ],[ -27, -9 ],[ 27, -9 ],[ -82, 0 ]],[[ -17, 0 ],[ 3, 2 ],[ -3, 2 ],[ 18, 0 ]]]),
(-308, 77, [[[ -45, -15 ],[ 132, -5 ],[ 87, -10 ],[ 87, 10 ]],[[ 0, 10 ],[ -76, -5 ],[ -76, 5 ],[ 0, -10 ]],[[ 28, -1 ],[ 13, 3 ],[ 15, 2 ],[ -15, 2 ]],[[ -73, -8 ],[ 73, -8 ],[ 31, -12 ],[ 104, 4 ]],[[ 23, 0 ],[ -6, 2 ],[ 6, 2 ],[ -15, 0 ]],[[ -116, -13 ],[ 176, -7 ],[ 46, -17 ],[ 130, 14 ]],[[ -83, 24 ],[ -144, -24 ],[ -196, 5 ],[ 83, -24 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 65, -12 ],[ 65, 12 ],[ 132, 1 ],[ -67, 13 ]],[[ -120, 37 ],[ -231, -36 ],[ -298, 8 ],[ 120, -37 ]],[[ -79, -2 ],[ 63, -7 ],[ -17, -8 ],[ 74, 3 ]],[[ -21, 5 ],[ -34, -5 ],[ -43, 0 ],[ 22, -5 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -43, -6 ],[ 74, -2 ],[ 31, -5 ],[ 29, 6 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ -351, -20 ],[ 351, -30 ],[ 0, -40 ],[ 351, 20 ]],[[ -48, -3 ],[ 55, -3 ],[ 1, -6 ],[ 47, 4 ]],[[ 274, 15 ],[ -274, 25 ],[ 0, 30 ],[ -274, -15 ]],[[ 50, 0 ],[ -24, 5 ],[ 24, 5 ],[ -50, 0 ]],[[ 9, 2 ],[ -20, 0 ],[ -15, 1 ],[ -1, -2 ]],[[ -124, 20 ],[ -115, -24 ],[ -201, -4 ],[ 134, -21 ]],[[ 4, -1 ],[ 7, 1 ],[ 17, 0 ],[ -9, 2 ]],[[ -95, -3 ],[ 20, -11 ],[ -20, -11 ],[ 95, -3 ]]]),
(-312, 78, [[[ -5, -2 ],[ 20, 1 ],[ 12, -1 ],[ -1, 2 ]],[[ 14, -3 ],[ 17, 3 ],[ 29, 0 ],[ -15, 3 ]],[[ 27, 5 ],[ -59, -1 ],[ -23, 5 ],[ -22, -6 ]],[[ 16, 12 ],[ -105, -8 ],[ -57, 8 ],[ -16, -12 ]],[[ 7, 1 ],[ -14, 0 ],[ -2, 1 ],[ -7, -1 ]],[[ -175, -5 ],[ 194, -14 ],[ -69, -14 ],[ 175, 5 ]],[[ 55, 18 ],[ -207, -9 ],[ -61, 13 ],[ -64, -18 ]],[[ -71, -9 ],[ 142, 0 ],[ 9, -9 ],[ 71, 9 ]],[[ 25, -2 ],[ 0, 4 ],[ 25, 1 ],[ -25, 2 ]],[[ 245, -16 ],[ 0, 32 ],[ 204, 8 ],[ -163, 16 ]],[[ 23, 3 ],[ -44, 0 ],[ -5, 3 ],[ -21, -3 ]],[[ 11, -2 ],[ 13, 2 ],[ 18, 0 ],[ -7, 2 ]],[[ 376, 0 ],[ -187, 37 ],[ 187, 37 ],[ -377, 0 ]],[[ 25, -5 ],[ 31, 5 ],[ 46, 0 ],[ -21, 5 ]],[[ -209, -15 ],[ 254, -16 ],[ 11, -28 ],[ 249, 17 ]],[[ -41, 9 ],[ -59, -9 ],[ -80, 0 ],[ 39, -9 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 255, -12 ],[ -35, 31 ],[ 188, 19 ],[ -239, 9 ]],[[ 462, 7 ],[ -469, 44 ],[ 217, 39 ],[ -523, -11 ]],[[ 209, -20 ],[ 0, 40 ],[ 209, 4 ],[ -209, 20 ]],[[ -63, -1 ],[ 58, -6 ],[ -16, -6 ],[ 63, 3 ]]]),
(-79, 79, [[[ 9//2, 1//2 ],[ 9//2, -1//2 ],[ 9//2, -1//2 ],[ -9//2, -1//2 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ -12, 0 ],[ 8, 1 ],[ -8, 1 ],[ 12, 0 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -3, -1 ],[ -2, 1 ],[ -9, 0 ],[ 15//2, 1//2 ]],[[ 15//2, -1//2 ],[ -7, 0 ],[ 4, -1 ],[ -13//2, 1//2 ]],[[ 17, -2 ],[ -20, -1 ],[ -1, -3 ],[ -22, 1 ]],[[ -5, 0 ],[ 5//2, 1//2 ],[ -5//2, 1//2 ],[ 5, 0 ]],[[ 33//2, 1//2 ],[ -17//2, -3//2 ],[ 15//2, -3//2 ],[ -27//2, 1//2 ]]]),
(-328, 82, [[[ -79, -5 ],[ 73, -6 ],[ 10, -10 ],[ 79, 5 ]],[[ 249, -13 ],[ -16, 32 ],[ 235, 18 ],[ -269, 15 ]],[[ -19, 4 ],[ -25, -4 ],[ -38, 0 ],[ 19, -4 ]],[[ 5, -1 ],[ 7, 1 ],[ 9, 0 ],[ -4, 1 ]],[[ -155, 15 ],[ -36, -21 ],[ -177, -8 ],[ 143, -12 ]],[[ 55, 7 ],[ -73, 4 ],[ -27, 9 ],[ -70, -5 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -81, 15 ],[ -67, -15 ],[ -169, 0 ],[ 88, -15 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ -15, -3 ],[ 33, -1 ],[ 21, -2 ],[ 14, 3 ]],[[ 11, -2 ],[ 9, 2 ],[ 17, 1 ],[ -16, 1 ]],[[ -143, 1 ],[ 64, -14 ],[ -85, -14 ],[ 151, -1 ]],[[ -80, -5 ],[ 77, -5 ],[ 23, -10 ],[ 65, 7 ]],[[ 67, -13 ],[ 65, 13 ],[ 139, 0 ],[ -72, 13 ]],[[ -329, -22 ],[ 329, -19 ],[ 0, -44 ],[ 329, 22 ]],[[ -233, -15 ],[ 230, -14 ],[ 0, -30 ],[ 227, 15 ]],[[ 233, -99 ],[ 667, 72 ],[ 891, -28 ],[ -224, 100 ]],[[ -76, 0 ],[ 35, -7 ],[ -35, -7 ],[ 69, 0 ]],[[ -1162, 0 ],[ 587, -111 ],[ -587, -111 ],[ 1166, 0 ]]]),
(-83, 83, [[[ -37//2, -3//2 ],[ 37//2, -3//2 ],[ 5//2, -5//2 ],[ 21, 1 ]],[[ -37//2, 1//2 ],[ -7//2, -3//2 ],[ -6, -2 ],[ 27//2, -1//2 ]],[[ 17//2, -1//2 ],[ 3, 1 ],[ 11//2, 1//2 ],[ -11//2, 1//2 ]],[[ 5, 0 ],[ -1//2, 1//2 ],[ 1//2, 1//2 ],[ -4, 0 ]],[[ -15, 0 ],[ 7//2, -3//2 ],[ -17//2, -3//2 ],[ 29//2, -1//2 ]],[[ 12, 1 ],[ -25//2, 3//2 ],[ -5//2, 3//2 ],[ -33//2, -1//2 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]]]),
(-340, 85, [[[ -67, 0 ],[ 16, -7 ],[ -16, -7 ],[ 66, 0 ]],[[ 9, 0 ],[ -2, 1 ],[ 2, 1 ],[ -10, 0 ]],[[ 145, -1 ],[ -19, 16 ],[ 36, 15 ],[ -146, 1 ]],[[ -10, 0 ],[ 4, -1 ],[ -4, -1 ],[ 10, 0 ]],[[ -16, -1 ],[ 16, -1 ],[ 0, -2 ],[ 16, 1 ]],[[ 19, 0 ],[ -1, 2 ],[ 1, 2 ],[ -18, 0 ]],[[ -526, 9 ],[ 40, -57 ],[ -204, -54 ],[ 526, -9 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -38, 0 ],[ 11, -4 ],[ -11, -4 ],[ 39, 0 ]],[[ -114, -4 ],[ 52, -11 ],[ 10, -13 ],[ 111, 3 ]],[[ -124, -15 ],[ 154, -11 ],[ 108, -17 ],[ 138, 14 ]],[[ -213, -15 ],[ 183, -20 ],[ 90, -25 ],[ 212, 15 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -92, -15 ],[ 158, -7 ],[ 137, -10 ],[ 65, 17 ]],[[ -4, -39 ],[ 352, 5 ],[ 360, -6 ],[ 4, 39 ]],[[ -46, 0 ],[ 6, -5 ],[ -6, -5 ],[ 47, 0 ]],[[ 2000, 115 ],[ -1454, 195 ],[ -644, 230 ],[ -2000, -115 ]],[[ -85, 8 ],[ -57, -11 ],[ -88, -8 ],[ 93, -8 ]],[[ 277, -27 ],[ 176, 37 ],[ 289, 24 ],[ -296, 25 ]],[[ -171, -12 ],[ 157, -14 ],[ 77, -20 ],[ 152, 14 ]],[[ -172, 17 ],[ -127, -22 ],[ -180, -15 ],[ 173, -17 ]],[[ 281, 231 ],[ -2191, -14 ],[ -1995, 72 ],[ -281, -231 ]],[[ -457, -13 ],[ 212, -47 ],[ 27, -50 ],[ 456, 13 ]]]),
(-344, 86, [[[ -91, -17 ],[ -91, 17 ],[ -166, -1 ],[ 75, 16 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -77, 22 ],[ 219, -7 ],[ 126, 20 ],[ 75, -24 ]],[[ 43, 3 ],[ 2, -6 ],[ 21, -2 ],[ -29, -1 ]],[[ -253, -15 ],[ 40, 33 ],[ -239, 13 ],[ 255, 14 ]],[[ 52, -9 ],[ -97, 0 ],[ -53, -10 ],[ -50, 10 ]],[[ -99, -19 ],[ -85, 19 ],[ -222, 0 ],[ 123, 19 ]],[[ 187, 16 ],[ 13, -25 ],[ 226, -6 ],[ -171, -16 ]],[[ -189, -32 ],[ -116, 36 ],[ -362, -2 ],[ 211, 32 ]],[[ -187, 5 ],[ 149, 16 ],[ -54, 22 ],[ 221, -7 ]],[[ -161, 1 ],[ 93, 14 ],[ -88, 15 ],[ 163, 0 ]],[[ 371, -16 ],[ -360, -26 ],[ 61, -39 ],[ -361, 18 ]],[[ 158, 7 ],[ -45, -19 ],[ 149, -9 ],[ -166, -8 ]],[[ 59, -20 ],[ -200, 7 ],[ -126, -16 ],[ -51, 22 ]],[[ -58, 30 ],[ 285, -13 ],[ 207, 21 ],[ 46, -33 ]],[[ -65, 17 ],[ 185, -3 ],[ 118, 16 ],[ 73, -21 ]],[[ 101, -1 ],[ -70, -8 ],[ 23, -8 ],[ -73, 3 ]],[[ -21, -5 ],[ -33, 5 ],[ -48, 0 ],[ 27, 5 ]],[[ 212, -12 ],[ -229, -13 ],[ 45, -25 ],[ -234, 11 ]],[[ -86, 12 ],[ 151, 1 ],[ 41, 15 ],[ 99, -13 ]],[[ 83, 36 ],[ 247, -30 ],[ 298, 12 ],[ -83, -36 ]],[[ -101, 12 ],[ 160, 2 ],[ 48, 12 ],[ 67, -12 ]],[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 0, 47 ],[ 343, -29 ],[ 343, 29 ],[ 0, -47 ]]]),
(-87, 87, [[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ -1, 0 ],[ 2, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ -5//2, 1//2 ],[ -6, -1 ],[ -5, 0 ],[ 5, -1 ]],[[ -7//2, 1//2 ],[ -4, -1 ],[ -3, 0 ],[ 5//2, -1//2 ]],[[ 13//2, -1//2 ],[ 0, 1 ],[ 5, 0 ],[ -7//2, 1//2 ]],[[ -27//2, -5//2 ],[ 53//2, 1//2 ],[ 13//2, -3//2 ],[ 13//2, 3//2 ]],[[ 39//2, -3//2 ],[ -11//2, 5//2 ],[ 25//2, 1//2 ],[ -25//2, 1//2 ]],[[ -28, -3 ],[ 56, 0 ],[ 0, -3 ],[ 28, 3 ]],[[ 13//2, -5//2 ],[ 20, 3 ],[ 43//2, -1//2 ],[ -14, 3 ]],[[ -8, 1 ],[ -3, -2 ],[ -8, 0 ],[ 8, -1 ]]]),
(-356, 89, [[[ -90, -17 ],[ 184, 0 ],[ 66, -10 ],[ 50, 11 ]],[[ 440, 13 ],[ -255, 38 ],[ 108, 47 ],[ -437, -5 ]],[[ -1, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ 462, -8 ],[ -143, 46 ],[ 275, 36 ],[ -418, 9 ]],[[ 0, -1 ],[ 9, 0 ],[ 10, 0 ],[ 0, 1 ]],[[ 88, 9 ],[ -113, 4 ],[ -54, 9 ],[ -49, -9 ]],[[ 7, 0 ],[ -6, 1 ],[ -1, 1 ],[ -12, -1 ]],[[ -33, 0 ],[ 16, -3 ],[ -16, -3 ],[ 32, 0 ]],[[ 107, -24 ],[ 144, 24 ],[ 232, -3 ],[ -107, 24 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ -215, 16 ],[ -64, -27 ],[ -239, -13 ],[ 200, -19 ]],[[ 62, -231 ],[ 1856, 110 ],[ 1928, -107 ],[ 2, 225 ]],[[ 7, 2 ],[ -28, 0 ],[ -11, 1 ],[ -7, -2 ]],[[ 785, 48 ],[ -768, 51 ],[ -32, 96 ],[ -785, -48 ]],[[ 211, -8 ],[ -30, 23 ],[ 156, 14 ],[ -185, 8 ]],[[ 4, 3 ],[ -27, -1 ],[ -27, 1 ],[ 4, -3 ]],[[ -19, 0 ],[ 9, -3 ],[ -6, -2 ],[ 31, 0 ]],[[ -43, -4 ],[ 54, -2 ],[ 11, -2 ],[ 11, 2 ]],[[ 180, -13 ],[ 19, 23 ],[ 161, 10 ],[ -161, 10 ]],[[ -12, -29 ],[ 242, 12 ],[ 139, -5 ],[ -22, 15 ]],[[ 205, -80 ],[ 574, 65 ],[ 761, -20 ],[ -257, 85 ]],[[ -79, 6 ],[ -7, -11 ],[ -59, -3 ],[ 59, -4 ]],[[ -74, 34 ],[ -272, -25 ],[ -326, 9 ],[ 85, -38 ]],[[ 543, 130 ],[ -1306, -9 ],[ -856, 114 ],[ -543, -130 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -15, 0 ],[ 6, -2 ],[ -3, -1 ],[ 13, 0 ]]]),
(-91, 91, [[[ 9//2, 1//2 ],[ 2, -1 ],[ 4, 0 ],[ -7//2, -1//2 ]],[[ 11//2, -1//2 ],[ -19//2, -1//2 ],[ -3//2, -1//2 ],[ -11//2, 1//2 ]],[[ 123//2, -3//2 ],[ -125//2, -15//2 ],[ 17//2, -9//2 ],[ -63, 2 ]],[[ 23//2, 1//2 ],[ -3, -2 ],[ 13//2, -1//2 ],[ -23//2, -1//2 ]],[[ -677//2, 57//2 ],[ 606, 27 ],[ 105//2, 59//2 ],[ 677//2, -57//2 ]],[[ -19//2, -7//2 ],[ -85//2, 9//2 ],[ -45//2, -1//2 ],[ 12, 4 ]],[[ 1, 0 ],[ 0, 0 ],[ 1, 0 ],[ -1, 0 ]],[[ 6, 0 ],[ -5//2, -1//2 ],[ 5//2, -1//2 ],[ -5, 0 ]]]),
(-372, 93, [[[ 27, 3 ],[ 11, -4 ],[ 28, -1 ],[ -23, -2 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 19, 0 ],[ -14, -2 ],[ 7, -1 ],[ -15, 0 ]],[[ -68, -7 ],[ 1, 14 ],[ -68, 0 ],[ 68, 7 ]],[[ 22, -3 ],[ -44, 0 ],[ -8, -3 ],[ -22, 3 ]],[[ 1520, 91 ],[ 0, -182 ],[ 1520, -91 ],[ -1520, -91 ]],[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ -6, -1 ],[ -7, 1 ],[ -10, 0 ],[ 4, 1 ]],[[ 80, -9 ],[ -156, -2 ],[ -18, -9 ],[ -80, 9 ]],[[ 200, 3 ],[ -122, -22 ],[ 111, -16 ],[ -230, 1 ]],[[ 6, -4 ],[ -47, 2 ],[ -23, -2 ],[ -6, 4 ]],[[ -87, 6 ],[ 95, 5 ],[ -11, 8 ],[ 74, -3 ]],[[ -47, 6 ],[ 94, 0 ],[ 24, 7 ],[ 47, -8 ]],[[ 4354, -222 ],[ -4677, -280 ],[ 579, -448 ],[ -4354, 222 ]],[[ -80, 28 ],[ 278, -7 ],[ 190, 19 ],[ 64, -27 ]],[[ -1, 0 ],[ 2, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ -267, -20 ],[ -14, 38 ],[ -298, 14 ],[ 309, 20 ]],[[ 106, -5 ],[ -120, -7 ],[ 20, -10 ],[ -106, 5 ]],[[ -150, -27 ],[ -152, 27 ],[ -299, 0 ],[ 149, 27 ]],[[ 281, -3 ],[ -252, -27 ],[ 123, -20 ],[ -292, 3 ]],[[ -39, -4 ],[ -7, 7 ],[ -40, 0 ],[ 31, 4 ]],[[ -91, 30 ],[ 350, -14 ],[ 130, 22 ],[ 105, -30 ]],[[ 17, -2 ],[ -30, 0 ],[ -5, -2 ],[ -13, 2 ]],[[ 172, -5 ],[ -128, -13 ],[ 50, -13 ],[ -134, 2 ]],[[ 43, 8 ],[ 51, -8 ],[ 83, 0 ],[ -40, -8 ]]]),
(-376, 94, [[[ 33, -4 ],[ 17, 3 ],[ 50, 1 ],[ -17, 3 ]],[[ 97, 29 ],[ -194, 0 ],[ -359, 29 ],[ -97, -29 ]],[[ -12, 5 ],[ -49, -1 ],[ -49, 1 ],[ -12, -5 ]],[[ 7, 1 ],[ -12, 1 ],[ -8, 1 ],[ -13, -1 ]],[[ 37, 0 ],[ -6, 2 ],[ 21, 7 ],[ -39, 0 ]],[[ 9, 0 ],[ -2, 1 ],[ 2, 1 ],[ -11, 0 ]],[[ 313, 16 ],[ -230, 19 ],[ -108, 66 ],[ -451, -32 ]],[[ -2351, 140 ],[ 0, -280 ],[ -2351, -140 ],[ 2351, -140 ]],[[ 0, 0 ],[ -1, 0 ],[ -1, 0 ],[ 0, 0 ]],[[ -5, -1 ],[ 10, 0 ],[ 7, -1 ],[ 5, 1 ]],[[ 7, 3 ],[ -14, 0 ],[ -57, 3 ],[ -7, -3 ]],[[ 0, 0 ],[ -1, 0 ],[ 1, 0 ],[ 0, 0 ]],[[ -72, -5 ],[ 35, -3 ],[ 13, -9 ],[ 42, 2 ]],[[ -153, 25 ],[ -131, -21 ],[ -284, -4 ],[ 131, -21 ]],[[ -9, 0 ],[ -1, -1 ],[ -7, -2 ],[ 20, -1 ]],[[ 87, -16 ],[ 68, 7 ],[ 320, 8 ],[ -87, 16 ]],[[ 26, -11 ],[ 51, 3 ],[ 183, -2 ],[ -17, 10 ]],[[ 1, 1 ],[ -4, 0 ],[ -23, 1 ],[ -3, -1 ]],[[ 5, 1 ],[ -6, 0 ],[ -15, 1 ],[ -1, -1 ]],[[ -68, -4 ],[ 29, -3 ],[ 39, -7 ],[ 29, 3 ]],[[ 9, 0 ],[ 0, 1 ],[ 9, 2 ],[ -21, 1 ]],[[ 149, 11 ],[ -149, 11 ],[ -40, 22 ],[ -189, -11 ]],[[ 95, 3 ],[ -27, 4 ],[ 16, 12 ],[ -55, -1 ]],[[ -84, -3 ],[ 67, -6 ],[ 17, -9 ],[ 67, 6 ]]]),
(-95, 95, [[[ 0, 0 ],[ 1, 0 ],[ -1, 0 ],[ 1, 0 ]],[[ 7//2, -1//2 ],[ -7, 0 ],[ -3//2, -1//2 ],[ -7//2, 1//2 ]],[[ 15, 0 ],[ -12, -1 ],[ 12, -1 ],[ -16, 0 ]],[[ 3//2, 1//2 ],[ -1//2, -1//2 ],[ 1, 0 ],[ -1, 0 ]],[[ 15//2, 3//2 ],[ 11//2, -3//2 ],[ 7, 0 ],[ -9//2, -1//2 ]],[[ 17//2, 1//2 ],[ 0, -1 ],[ 17//2, -1//2 ],[ -17//2, -1//2 ]],[[ -1, 0 ],[ 1, 0 ],[ 0, 0 ],[ 1, 0 ]],[[ 25//2, 1//2 ],[ -6, -1 ],[ 13//2, -1//2 ],[ -7, 0 ]],[[ 9//2, -1//2 ],[ -9, 0 ],[ -1//2, -1//2 ],[ -9//2, 1//2 ]],[[ -14, 0 ],[ 10, 1 ],[ -10, 1 ],[ 14, 0 ]],[[ 21//2, 1//2 ],[ -3//2, -5//2 ],[ 21//2, -1//2 ],[ -39//2, -3//2 ]],[[ -27//2, 1//2 ],[ 23//2, 1//2 ],[ -15//2, 3//2 ],[ 27//2, -1//2 ]]]),
(-388, 97, [[[ -4, 1 ],[ -10, -1 ],[ -8, 0 ],[ 4, -1 ]],[[ 42, -1 ],[ -10, 4 ],[ 22, 2 ],[ -26, 1 ]],[[ 11, 0 ],[ -5, 1 ],[ 6, -1 ],[ 6, 1 ]],[[ 0, -3 ],[ 34, 2 ],[ 20, -1 ],[ -2, 3 ]],[[ -165, -2 ],[ 89, -13 ],[ -60, -16 ],[ 157, 2 ]],[[ 20, 10 ],[ -126, -5 ],[ -64, 5 ],[ -9, -11 ]],[[ -6, -37 ],[ 399, 17 ],[ 279, -13 ],[ 6, 37 ]],[[ 483, 88 ],[ -984, 13 ],[ -511, 67 ],[ -424, -73 ]],[[ 108, -5 ],[ -5, 11 ],[ 103, 6 ],[ -91, 6 ]],[[ 6, 1 ],[ -11, 0 ],[ -6, 1 ],[ -5, -1 ]],[[ 1166, -18 ],[ -371, 106 ],[ 753, 102 ],[ -1166, 18 ]],[[ -90, 17 ],[ -129, -18 ],[ -199, -2 ],[ 120, -20 ]],[[ -732, 99 ],[ -476, -106 ],[ -1282, -19 ],[ 732, -99 ]],[[ 26, -1 ],[ -6, 4 ],[ 19, 2 ],[ -38, 1 ]],[[ 53, 8 ],[ -129, 3 ],[ -53, 8 ],[ -76, -11 ]],[[ 40, -3 ],[ 20, 7 ],[ 40, 3 ],[ -60, 4 ]],[[ 24, -17 ],[ 160, 11 ],[ 163, -4 ],[ -41, 19 ]],[[ 26, -7 ],[ 57, 8 ],[ 74, -1 ],[ -43, 9 ]],[[ 188, -49 ],[ 399, 44 ],[ 376, 0 ],[ -188, 39 ]],[[ -255, -18 ],[ 313, -20 ],[ 53, -26 ],[ 256, 18 ]],[[ -230, -52 ],[ 567, -2 ],[ 365, -48 ],[ 303, 53 ]],[[ -9, 2 ],[ -17, -2 ],[ -18, 0 ],[ 9, -2 ]],[[ 3, -1 ],[ 12, 1 ],[ 7, 0 ],[ -4, 1 ]]])
]
################################################################################
#
#  Orbit stabilizer
#
################################################################################

function _orbit_stabilizer(G, idity, a)
  OT = Tuple{typeof(idity), FakeFmpqMat}[(idity, hnf(basis_matrix(a)))]
  Y = typeof(idity)[]
  m = 1
  while m <= length(OT)
    @show m, length(OT), length(Y)
    b = OT[m][2]
    for g in G
      c = _operate(g, b)
      i = findfirst(x -> x[2] == c, OT)
      if i isa Nothing
        push!(OT, (OT[m][1] * g, c))
      elseif i isa Int
        w = OT[m][1] * g * inv(OT[i][1])
        if !(w in Y && inv(w) in Y)
          push!(Y, w)
        end
      end
    end
    m += 1
  end

  return OT, Y
end

function _operate(g::AbsAlgAssElem, b)
  M = representation_matrix(g, :right)
  c = hnf(b * FakeFmpqMat(M))
  return c
end

################################################################################
#
#  PIP for Z[Q_32]
#
################################################################################

function _isfree_Q32(K::AnticNumberField)
  G, mG = automorphism_group(K)
  QG, KtoQG = galois_module(K, mG)
  OKasideal = KtoQG(lll(maximal_order(K)))

  res = decompose(QG)
  _compute_matrix_algebras_from_reps2(QG, res)


  # lets compute a A_theta

  # A_theta = { lambda in Q[G] | thetha * lambda in O_N }
  # where theta is a normal basis element
  # by construction KtoQG\one(QG) is our normal basis element
  # so A_theta = { lambda in Q[G] | Z[G] * lambda \subseteq O_n }
  # which is just a right colon ideal

  n = degree(K)

  ZG = Order(QG, collect(G))

  # theta = one(QG)

  # N = _colon_raw(OKasideal, ideal(QG, ZG, FakeFmpqMat(representation_matrix(theta, :left))), :left)
  # #N = _colon_raw(OKasideal, ideal(QG, ZG, FakeFmpqMat(identity_matrix(FlintQQ, n))), :left)
  # # Johannes convention is the other way around
  #
  # Atheta = ideal(QG, ZG, N)

  # @assert all(theta * lambda in OKasideal for lambda in basis(Atheta))

  # M = maximal_order(ZG)

  # AthetaM = sum(b * M  for b in basis(Atheta))

  # d = denominator(AthetaM)

  # dAthetaM = d * AthetaM

  # fl, _delta = _isprincipal_maximal(dAthetaM, M, :right)

  # @assert fl

  # @assert dAthetaM == _delta * M

  # delta = inv(QG(d)) * _delta

  # @assert AthetaM == delta * M

  # thetaprime = theta * delta

  # N = _colon_raw(OKasideal, ideal(QG, ZG, FakeFmpqMat(representation_matrix(thetaprime, :left))), :left)

  # Athetaprime = ideal(QG, ZG, N)

  # @assert all(thetaprime * lambda in OKasideal for lambda in basis(Athetaprime))

  # X = order(G) * Athetaprime


  res = __decompose(QG)
  #Z, mZ = subgroups(G, order = 2)[1]
  #k, mk = fixed_field(K, [mG(mZ(z)) for z in Z])
  #@show k
  #H, mH = automorphism_group(k)
  #@show find_small_group(H)
  #QH, ktoQH = galois_module(k, mH)
  #res2 = decompose(QH)
  #_compute_matrix_algebras_from_reps2(QH, res2)
  #ZH = Order(QH, collect(H))
  #@show ktoQH
  #Ok = lll(maximal_order(k))
  #Okasideal = ktoQH(lll(maximal_order(k)))
  #@show istamely_ramified(k)
  ##fl, x = _isprincipal(Okasideal, ZH, :right)

  fl, y, Ok, Q32toD16, repsD16, ktoD16, groupmap, k_to_K = _is_D16_subfield_free(K, KtoQG, QG)

  if !fl
    return false, zero(K), "dihedral failure"
  end

  QD16 = codomain(Q32toD16)

  B, BtoA = [(B, mB) for (B, mB) in res if dim(B) == div(dim(QG), 2)][1]
  #@show B
  #@show isdefined(B, :isomorphic_full_matrix_algebra)
  e = BtoA(one(B))
  C, BtoC, CtoB = Hecke._as_algebra_over_center(B)
  @assert CtoB(one(C)) == one(B)
  #@show C
  Q, QtoC = isquaternion_algebra(C)
  #@show [ QtoC\(BtoC(BtoA\(e*elem_in_algebra(b)))) for b in basis(ZG) ]
  _eZG = Hecke._get_order_from_gens(B, [ (BtoA\(e*elem_in_algebra(b))) for b in basis(ZG) ])
  #@show one(B) in _eZG
  __eZG = Hecke._get_order_from_gens(C, [ BtoC(elem_in_algebra(b)) for b in basis(_eZG)])
  #@show one(C) in __eZG
  #@show QtoC(one(Q)) == one(C)

  _e1 = rand(QG, -5:5)
  _e2 = rand(QG, -5:5)

  @assert QtoC\(BtoC(BtoA\(e * _e1 * _e2))) == QtoC\(BtoC(BtoA\(e * _e1))) * (QtoC\(BtoC(BtoA\(e * _e2))))

  @assert QtoC\(BtoC(BtoA\(e * (_e1 + _e2)))) == QtoC\(BtoC(BtoA\(e * _e1))) + (QtoC\(BtoC(BtoA\(e * _e2))))

  @assert QtoC\(BtoC(BtoA\(e * one(QG)))) == one(Q)

  eZG = Hecke._get_order_from_gens(Q, [ QtoC\(BtoC(BtoA\(e*elem_in_algebra(b)))) for b in basis(ZG) ])

  Lambda = maximal_order(eZG)

  Lambda_star = _unit_group_generators_quaternion(Lambda)

  #allunitsLambda = map(x -> BtoA(CtoB(QtoC(elem_in_algebra(x)))), (closure(Lambda_star, *)))

   # I want to make sure that Lambda_star = eZG^times

   QoverQQ, QtoQoverQQ, theother = restrict_scalars(Q, FlintQQ)

   #@show Q

   eZGabs = Hecke._get_order_from_gens(QoverQQ, [ QtoQoverQQ(elem_in_algebra(u)) for u in absolute_basis(eZG) ])
   units_abs = [ QtoQoverQQ(elem_in_algebra(u)) for u in Lambda_star ]
   _, eZGstar = _orbit_stabilizer(units_abs, one(QoverQQ), eZGabs)
   #@show length(eZGstar)
   #@show issetequal(closure(eZGstar, *), [QtoQoverQQ(elem_in_algebra(u)) for u in allunitsLambda if elem_in_algebra(u) in eZG ])
   #@show closure(eZGstar, *)
   #@show [QtoQoverQQ(elem_in_algebra(u)) for u in allunitsLambda if elem_in_algebra(u) in eZG ]
   eZGstar = [ theother(u) for u in eZGstar ]
   #@assert length(eZGstar) == length(Lambda_star)


  # #Now move O_K over to O_K Lambda

  d = denominator(OKasideal)

  OKasidealnum = d * OKasideal

  OKLambda = sum(Lambda(QtoC\(BtoC(BtoA\(e * b)))) * Lambda for b in basis(OKasidealnum))

  fl, x = _is_principal_maximal_quaternion_generic_proper(OKLambda, Lambda, :right)


  if !fl
    return false, zero(K), "quaternion failure1"
  end

  OKasidealnume = sum(Lambda(QtoC\(BtoC(BtoA\(e * b)))) * eZG for b in basis(OKasidealnum))

  if !(x in OKasidealnume)
  #if !(x in OKasidealnume)
  #  found = false
  #  for u in Lambda_star
  #    if x * elem_in_algebra(u) in OKasidealnume
  #      x = x * elem_in_algebra(u)
  #      found = true
  #    end
  #  end
  #  if !found
  #    println("bad try")
    return false, zero(K), "quaternion failure2"
  end

  x = inv(Q(d)) * x

  #@assert sum(eZG(QtoC\(BtoC(BtoA\(d * e * b)))) * eZG for b in basis(OKasideal)) == (d * x) * eZG

  # Now move Lambda_star (which is in fact (eZG)^\times back to ZG)

  #Lambda_star_in_QGalmost = [BtoA(CtoB(QtoC(elem_in_algebra(u)))) for u in Lambda_star]
  Lambda_star_in_QGalmost = [BtoA(CtoB(QtoC(u))) for u in eZGstar]

  @assert all(u in eZG for u in eZGstar)

  Lambda_star_in_QG = elem_type(QG)[]

  Me = representation_matrix(e, :left)

  for i in 1:length(Lambda_star_in_QGalmost)
    v = matrix(FlintQQ, 1, dim(QG), Lambda_star_in_QGalmost[i].coeffs);
    d = denominator(v) * denominator(Me)
    fl, w = can_solve_with_solution(change_base_ring(FlintZZ, d * Me), change_base_ring(FlintZZ, d * v), side = :left)
    @assert fl
    @assert e * QG(fmpq[w[1, j] for j in 1:dim(QG)]) == Lambda_star_in_QGalmost[i]
    push!(Lambda_star_in_QG, QG(fmpq[w[1, j] for j in 1:dim(QG)]))
    @assert Lambda_star_in_QG[end] in ZG
  end

  F = GF(2, cached = false)
  F2D16 = F[group(QD16)]

  _units = elem_type(QG)[]
  _units_reduced = elem_type(F2D16)[]
  for u in Lambda_star_in_QG
    ured = sum(FlintZZ(u.coeffs[QG.group_to_base[g]]) * F2D16(groupmap(g)) for g in group(QG))
    if !(ured in _units_reduced)
      push!(_units, u)
      push!(_units_reduced, ured)
    end
  end

  __units = collect(zip(_units, _units_reduced))

  cl = closure(__units, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])

  repsLambdastart = [x for (x, y) in cl]

  xlift = BtoA(CtoB(QtoC(x)))

  M1 = basis_matrix(Ref(e) .* basis(OKasideal)); M2 =  matrix(FlintQQ, 1, dim(QG), [xlift.coeffs[i] for i in 1:dim(QG)])
  dd = lcm(denominator(M1), denominator(M2))
  fl, v = can_solve_with_solution(map_entries(x -> FlintZZ(x * dd), M1), map_entries(x -> FlintZZ(x * dd), M2), side = :left)
  @assert fl
  xxlift = dot(basis(OKasideal), fmpz[v[1, i] for i in 1:dim(QG)])
  #xxlift = divexact_left(xlift, e)

  @assert xlift == xxlift * e

  @assert xxlift in OKasideal

  @show "Starting the numeration ..."

  Krelk, m = relative_extension(k_to_K)

  xxtocheck = [ tr(m(KtoQG\(xxlift * repsLambdastart[i]))) for i in 1:length(repsLambdastart) ]
  ytocheck = [ ktoD16\(y * repsD16[j]) for j in 1:length(repsD16) ]

  F = GF(2, cached = false)

  Ok = maximal_order(domain(k_to_K))

  xxtocheckcoordinates = [ matrix(F, 1, 16, coordinates(Ok(x))) for x in xxtocheck]

  ytocheckcoordinates = [ matrix(F, 1, 16, coordinates(Ok(y))) for y in ytocheck ]

  Ok2 = 2 * maximal_order(domain(k_to_K))

  @time for (i, x) in enumerate(xxtocheck)
    @show i
    for y in ytocheck
      if x - y in Ok2
        __x = KtoQG\(xxlift * repsLambdastart[i])
        _x = __x - k_to_K(divexact(tr(m(__x)) - y, 2))
        @assert ismaximal(Order(K, [mG(g)(_x) for g in G], isbasis = true))
        return true, _x
      end
    end
  end

  return false, zero(K), "enumeration failure"

  #return xxlift, y, repsD16, repsLambdastart, Ok, Q32toD16, KtoQG, ktoD16, e, BtoA
  return xxlift, y, repsD16, repsLambdastart, Ok, Q32toD16, KtoQG, ktoD16, e, BtoA, k_to_K, groupmap
end

function _isless(x::gfp_mat, y::gfp_mat)
  i = 0
  c = ncols(x)
  while i < c
    i += 1
    if x[i] == y[i]
      continue
    else
      return x[i] < y[i]
    end
  end
  return false
end

function _get_D16(QG::AlgGrp)
  G = group(QG)
  Z, mZ = center(group(QG))
  Q, mQ = quotient(G, Z, mZ)
  D16 = QQ[Q]
  Q32toD16 = hom(QG, D16, mQ)
  return D16, Q32toD16, mQ
end

global _cache_tmp = []

function _is_D16_subfield_free(K, KtoQG, QG::AlgGrp)
  G = group(QG)
  Z, mZ = center(G)
  Q, mQ = quotient(G, Z, mZ)
  D16 = QQ[Q]
  Q32toD16 = hom(QG, D16, mQ)

  f1 = KtoQG.mG(mZ(Z[1]))
  f2 = KtoQG.mG(mZ(Z[2]))
  k, mk = fixed_field(K, [KtoQG.mG(mZ(Z[1])), KtoQG.mG(mZ(Z[2]))])
  _nbK = KtoQG\one(QG)
  _b = f1(_nbK) + f2(_nbK)
  Krelk, m = relative_extension(mk)
  _new_inb = k(m(_b))
  #@show "\n $_new_inb\n"
  #println("\n\n\ndas dsd s\n")
  D16, Q32toD16, mQ = _get_D16(QG)
  kauto = _adjust_automorphism_group(KtoQG.mG, mQ, mk)
  DD16, ktoD16 = Hecke.galois_module(k, kauto, normal_basis_generator = _new_inb)
  MM = zero_matrix(FlintQQ, degree(k), degree(k))
  for i in 1:degree(k)
    z = gen(k)^(i - 1)
    v = Q32toD16(KtoQG(mk(z))).coeffs
    for j in 1:degree(k)
      MM[i, j] = v[j]
    end
  end
  #@show MM
  MMinv = inv(MM)
  ktoD16.M = MMinv
  ktoD16.Minv = MM
  @assert DD16 === D16
  Ok = ktoD16(lll(maximal_order(k)))
  ZD16 = Order(D16, basis(D16))
  res = __decompose(D16)
  #@show [isdefined(B, :isomorphic_full_matrix_algebra) for (B, mB) in res]
  _compute_matrix_algebras_from_reps2(D16, res)
  #@show [isdefined(B, :isomorphic_full_matrix_algebra) for (B, mB) in res]
  fl, x = _isprincipal(Ok, ZD16, :right)

  if !fl return
    false
  end

  if length(_cache_tmp) == 0
   unitss = _unit_group_generators(ZD16)
   append!(_cache_tmp, unitss)
  else
    B = parent(_cache_tmp[1])
    GG = group(B)
    fl, f = isisomorphic(GG, group(D16))
    @assert fl
    ff = hom(B, D16, f)
    unitss = ff.(_cache_tmp)
  end

  F = GF(2, cached = false)

  F2D16 = F[group(D16)]

  _units = elem_type(D16)[]
  _units_reduced = elem_type(F2D16)[]

  for u in unitss
    ured = sum(FlintZZ(u.coeffs[D16.group_to_base[g]]) * F2D16(g) for g in group(D16))
    if !(ured in _units_reduced)
      push!(_units, u)
      push!(_units_reduced, ured)
    end
  end

  __units = collect(zip(_units, _units_reduced))

  cl = closure(__units, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
  return true, x, Ok, Q32toD16, [x for (x, y) in cl], ktoD16, mQ, mk #[x for (x, y) in cl], ktoD16
end

function maximal_order_via_absolute(O::AlgAssRelOrd)
  A = algebra(O)
  C, AtoC, CtoA = restrict_scalars(A, FlintQQ)
  OC = maximal_order(Hecke._get_order_from_gens(C, AtoC.(elem_in_algebra.(absolute_basis(O)))))
  M = zero_matrix(base_ring(A), degree(OC), dim(A))
  for i = 1:degree(OC)
    elem_to_mat_row!(M, i, CtoA(elem_in_algebra(basis(OC, copy = false)[i], copy = false)))
  end
  PM = sub(pseudo_hnf(PseudoMatrix(M), :lowerleft, true), (degree(OC) - dim(A) + 1):degree(OC), 1:dim(A))
  O = Order(A, PM)
  O.ismaximal = 1
  return O
end

function _adjust_automorphism_group(mK, mQ, ktoK)
  Q = codomain(mQ)
  K = codomain(ktoK)
  k = domain(ktoK)
  v = Vector{NfToNfMor}(undef, degree(k))
  au = automorphisms(k)
  for q in Q
    b = (mK(mQ\q))(ktoK(gen(k)))
    fl, bb = haspreimage(ktoK, b)
    @assert fl
    for a in au
      if a(gen(k)) == bb
        v[q[]] = a
      end
    end
  end
  return GrpGenToNfMorSet(Q, v, k)
end

################################################################################
#
#  Bley--Johnston--Hofmann enumeration method
#
################################################################################

function _unit_reps(M, F; dir = ".")
  dec = decompose(algebra(M))
  D = get_attribute!(M, :unit_reps) do
    return Dict{typeof(F), Vector{Vector{elem_type(algebra(M))}}}()
  end::Dict{typeof(F), Vector{Vector{elem_type(algebra(M))}}}

  if haskey(D, F)
    @info "Unit representatives cached for this conductor ideal"
    return D[F]
  else
    local u::Vector{Vector{elem_type(algebra(M))}}
    _u = nothing # _find_unit_reps_in_file(M, F)
    if _u !== nothing
      u = _u
    else
      u = __unit_reps(M, F)
      ii = 1
      fname = joinpath(dir, "$(degree(M))_$(ii).tmpinfo")
      while isfile(fname)
        ii += 1
        fname = joinpath(dir, "$(degree(M))_$(ii).tmpinfo")
      end
      dec = decompose(algebra(M))
      k = length(dec)
      idemsA = [dec[i][2](one(dec[i][1])) for i in 1:k]
      #@info "Saving to file"
      #@time _save_elements(fname, algebra(M), basis_matrix(M), basis_matrix(F), idemsA, u)
    end
    D[F] = u
    return u
  end
end

function _find_unit_reps_in_file(M, F; dir = ".")
  l = readdir(dir)
  for file in l
    if !isfile(file)
      continue
    end
    if !endswith(file, ".tmpinfo")
      continue
    end
    if !(_is_suitable_file(file, algebra(M), M, F; check_algebra = true))
      continue
    end
    @info "Found unit reps in a file ... loading"
    @time u = __test_load(file, algebra(M), M, F)
    @info "done"
    return u
  end
  return nothing
end

function _describe(B)
  d = dimension_of_center(B)
  s = div(dim(B), d)
  n = isqrt(s)
  if isdefined(B, :isomorphic_full_matrix_algebra)
    ismatalg = true
  else
    ismatalg = false
  end
  if ismatalg
    return "Full matrix algebra of degree $n over field of degree $d"
  else
    return "Divison ring of degree $n over field of degree $d"
  end
end

global _debug = []

function __unit_reps_simple(M, F)
  #push!(_debug, (M, F))
  B = algebra(M)
  @info _describe(B)
  @info "Computing generators of the maximal order"
  UB = _unit_group_generators_maximal_simple(M)
  Q, MtoQ = quo(M, F)
  for u in UB
    @assert u in M && inv(u) in M
    #@show u in FinB
  end
  @info "Number of generators: $(length(UB))"
  UB_reduced = unique!([MtoQ(M(u)) for u in UB])
  #@show UB_reduced
  @show norm(F)
  #QQ, MtoQQ = _quo_as_mat_alg_small(M, F)
  QQ = FakeAbsOrdQuoRing(M, F)
  _UB_reduced = unique!([QQ(M(u)) for u in UB])

  #@show length(UB)
  #@show UB_reduced
  @info "computing closure"
  @info "dimension $(dim(B))"

  if isdefined(B, :isomorphic_full_matrix_algebra)
    # It is faster to compute products in M_n(F) than in an associative algebra
    local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    local BtoC::Hecke.AbsAlgAssMorGen{AlgAss{fmpq}, AlgMat{nf_elem, AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}, AbstractAlgebra.Generic.MatSpaceElem{nf_elem}, fmpq_mat}
    #local BtoC::morphism_type(typeof(B), AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}})
    C, BtoC = B.isomorphic_full_matrix_algebra
    UBinC = elem_type(C)[BtoC(u)::elem_type(C) for u in UB]
    ___units = collect(zip(UBinC, UB_reduced))
    ___units_ = collect(zip(UBinC, _UB_reduced))
    ___units_all = collect(zip(UBinC, UB_reduced, _UB_reduced))
    #@time cl = closure(___units, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
    @time cl = closure(___units_, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
    # @show length(cl), length(cl2)
    # @assert length(cl) == length(cl2)
    # @time cl = closure(___units_all, (x, y) -> 
    #                    begin
    #                   #   if !(MtoQ\(x[2] * y[2]) - lift(x[3] * y[3]) in F)
    #                   #     push!(_debug, ((M(BtoC\x[1]), x[2], x[3]), (M(BtoC\y[1]), y[2], y[3])))
    #                   #     @show "oops";
    #                   #     @show coordinates(MtoQ\x[2])
    #                   #     @show coordinates(MtoQ\y[2]);
    #                   #     @show lift(x[3]) - M(BtoC\(x[1])) in F
    #                   #     @show lift(y[3]) - M(BtoC\(y[1])) in F
    #                   #     @show MtoQ\x[2] - M(BtoC\(x[1])) in F
    #                   #     @show MtoQ\y[2] - M(BtoC\(y[1])) in F
    #                   #     @show (x[3] * y[3]).v
    #                   #     @show QQ(lift(x[3]) * lift(y[3])).v
    #                   #     @show (QQ(M(BtoC\(x[1] * y[1])))).v
    #                   #    error("asdsdsd")
    #                   #  end;
    #                   #  w = x[3] * y[3];
    #                   #@assert QQ(lift(w)) == w;
    #                 (x[1] * y[1], x[2] * y[2], x[3] * y[3]);
    #               end,
    #                 eq = (x, y) -> begin
    #                # @assert MtoQ\x[2] - lift(x[3]) in F "oooops"; @assert MtoQ\y[2] - lift(y[3]) in F "oooops2"; if (x[2] == y[2]) != (x[3] == y[3]); @show coordinates(MtoQ\y[2]), coordinates(MtoQ\x[2]); @show coordinates(lift(x[3])); @show coordinates(lift(y[3])); @show x[3]; @show y[3]; error("asss"); end;
    #                x[2] == y[2];
    #                end
    #               )
    # #@time cl2 = closure(___units_, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
    @show length(cl)
    #@show length(cl2)
    #@assert first.(cl) == first.(cl2)
    #push!(_debug, cl)
    to_return = Vector{elem_type(B)}(undef, length(cl))
    @info "Mapping back"
    @time Threads.@threads for i in 1:length(cl)
      to_return[i] = BtoC\(cl[i][1])
    end
    #@time to_return2 = elem_type(B)[ (BtoC\(c[1]))::elem_type(B) for c in cl ]
    #@assert to_return == to_return2
    return to_return
  else
    __units = collect(zip(UB, UB_reduced))
    @info "Closing in the other case"
    @time cl = closure(__units, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
    return first.(cl)
  end
end

function __unit_reps(M, F)
  _assert_has_refined_wedderburn_decomposition(algebra(M))
  A = algebra(M)
  dec = decompose(algebra(M))
  unit_reps = Vector{elem_type(algebra(M))}[]
  for (B, mB) in dec
    MinB = Order(B, elem_type(B)[(mB\(mB(one(B)) * elem_in_algebra(b))) for b in absolute_basis(M)])
    FinB = ideal_from_lattice_gens(B, elem_type(B)[(mB\(b)) for b in absolute_basis(F)])
    @assert Hecke._test_ideal_sidedness(FinB, MinB, :right)
    FinB.order = MinB
    _unit_reps =  __unit_reps_simple(MinB, FinB)
    @info "Mapping back once more"
    to_return = Vector{elem_type(A)}(undef, length(_unit_reps))
    @time Threads.@threads for i in 1:length(_unit_reps)
      to_return[i] = mB(_unit_reps[i])
    end
    push!(unit_reps, to_return)
  end
  return unit_reps
end

function _assert_has_refined_wedderburn_decomposition(A)
  get_attribute!(A, :refined_wedderburn) do
    dec = decompose(A)
    _compute_matrix_algebras_from_reps2(A, dec)
    return true
  end
  return true
end

function _get_a_twosided_conductor(O, M)
  A = algebra(O)
  Z, ZtoA = center(A)
  Fl = conductor(O, M, :left)

  FinZ = _as_ideal_of_smaller_algebra(ZtoA, Fl)
  # Compute FinZ*OA but as an ideal of O
  bM = basis(M, copy = false)
  bFinZ = basis(FinZ, copy = false)
  basis_F = Vector{elem_type(A)}()
  for x in bM
    for y in bFinZ
      yy = ZtoA(y)
      t = yy * elem_in_algebra(x, copy = false)
      push!(basis_F, t)
    end
  end

  for b in basis_F
    @assert b in O
  end

  F = ideal_from_lattice_gens(A, O, basis_F, :twosided)
  return F
end

function __isprincipal(O, I, side = :right; dir = ".")
  A = algebra(O)
  _assert_has_refined_wedderburn_decomposition(A)
  dec = decompose(A)
  local M::order_type(A)
  _M = _find_maximal_order_in_file(O, dir = dir)
  if _M !== nothing
    @info "Found a maximal order in a file"
    M = _M
  else
    M = maximal_order(O)
  end

  fl, alpha = _isprincipal_maximal(I * M, M, :right)

  if !fl
    @info "Not principal over maximal order"
    return false, zero(A)
  end

  # Now test local freeness at the primes dividing the index [M : O]
  for p in prime_divisors(index(O, M))
    if !islocally_free(O, I, p, side = :right)[1]
      @info "Not locally free at $p"
      return false, zero(A)
    end
  end

  @assert alpha * M == I * M

  Z, ZtoA = center(A)
  Fl = conductor(O, M, :left)

  FinZ = _as_ideal_of_smaller_algebra(ZtoA, Fl)
  # Compute FinZ*OA but as an ideal of O
  bM = basis(M, copy = false)
  bFinZ = basis(FinZ, copy = false)
  basis_F = Vector{elem_type(A)}()
  for x in bM
    for y in bFinZ
      yy = ZtoA(y)
      t = yy * elem_in_algebra(x, copy = false)
      push!(basis_F, t)
    end
  end

  for b in basis_F
    @assert b in O
  end

  F = ideal_from_lattice_gens(A, O, basis_F, :twosided)

  #@show F == (conductor(O, M, :left) * conductor(O, M, :right))
  #@show det(basis_matrix(F))
  #@show det(basis_matrix(conductor(O, M, :left) * conductor(O, M, :right)))

  bases = Vector{elem_type(A)}[]

  IM = I * M

  for (B, mB) in dec
    MinB = Order(B, elem_type(B)[(mB\(mB(one(B)) * elem_in_algebra(b))) for b in absolute_basis(M)])
    #@show ismaximal(MinC)
    #@show hnf(basis_matrix(MinC))
    IMinB = ideal_from_lattice_gens(B, elem_type(B)[(mB\(b)) for b in absolute_basis(IM)])
    IMinB_basis = [mB(u) for u in absolute_basis(IMinB)]
    push!(bases, IMinB_basis)
    #@show UB
    #if isdefined(B, :isomorphic_full_matrix_algebra)
    #  local C::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    #  C, BtoC = B.isomorphic_full_matrix_algebra
    #  MinC = _get_order_from_gens(C, elem_type(C)[BtoC(elem_in_algebra(b)) for b in absolute_basis(MinB)])
    #  @show MinC
    #  @show nice_order(MinC)
    #end
    #@show FinB
  end

  unit_reps = _unit_reps(M, F)

  decc = copy(dec)
  p = sortperm(unit_reps, by = x -> length(x))
  dec_sorted = decc[p]
  units_sorted = unit_reps[p]
  bases_sorted = bases[p]
  bases_offsets_and_lengths = Tuple{Int, Int}[]
  k = 1
  for i in 1:length(bases_sorted)
    push!(bases_offsets_and_lengths, (k, length(bases_sorted[i])))
    k += length(bases_sorted[i])
  end

  #@show bases_offsets_and_lengths

  # let's collect the Z-basis of the Mi
  bases_sorted_cat = reduce(vcat, bases_sorted)
  special_basis_matrix = basis_matrix(bases_sorted_cat)
  inv_special_basis_matrix = inv(special_basis_matrix)
  Amatrix = fmpq_mat(basis_matrix(I)) * inv(special_basis_matrix)
  H, U = hnf_with_transform(change_base_ring(ZZ, Amatrix))
  Hinv = inv(fmpq_mat(H))
  
  local_coeffs = Vector{Vector{fmpq}}[]

  inv_special_basis_matrix_Hinv = inv_special_basis_matrix * Hinv

  #@info "preprocessing units"
  #@time for i in 1:length(dec)
  #  _local_coeffs = Vector{fmpq}[]
  #  m = dec_sorted[i][2]::morphism_type(AlgAss{fmpq}, typeof(A))
  #  alphai = dec_sorted[i][2](dec_sorted[i][2]\(alpha))
  #  for u in units_sorted[i]
  #    aui =  alphai * u
  #    auiasvec = _eltseq(matrix(QQ, 1, dim(A), coefficients(aui)) * inv_special_basis_matrix_Hinv)
  #    push!(_local_coeffs, auiasvec)
  #  end
  #  push!(local_coeffs, _local_coeffs)
  #end
  #@info "done"

  @info "new preprocessing units"
  @time local_coeffs = _compute_local_coefficients_parallel(alpha, A, dec_sorted, units_sorted, inv_special_basis_matrix_Hinv)

  #@time for i in 1:length(dec)
  #  _local_coeffs = Vector{fmpq}[]
  #  m = dec_sorted[i][2]::morphism_type(AlgAss{fmpq}, typeof(A))
  #  alphai = dec_sorted[i][2](dec_sorted[i][2]\(alpha))
  #  par = Iterators.partition(1:length(units_sorted[i]), multi * dim(A))
  #  ui = units_sorted[i]
  #  for p in par
  #    for (j, j_index) in enumerate(p)
  #      u =  ui[j_index]
  #      aui =  alphai * u
  #      __set_row!(t1, j, coefficients(aui, copy = false))
  #      #auiasvec = _eltseq(matrix(QQ, 1, dim(A), coefficients(aui)) * inv_special_basis_matrix_Hinv)
  #      #push!(_local_coeffs, auiasvec)
  #    end
  #    mul!(t2, t1, inv_special_basis_matrix_Hinv)
  #    for (j, j_index) in enumerate(p)
  #      push!(_local_coeffs, fmpq[ t2[j, k] for k in 1:dim(A)])
  #    end
  #    #push!(_local_coeffs, auiasvec)
  #  end
  #  push!(local_coeffs2, _local_coeffs)
  #end
  #@info "done"
  #@assert local_coeffs == local_coeffs2

  #for i in 1:length(dec)
  #  @show local_coeffs
  #end

  # Try to reduce the number of tests
  #@info "Collected information for the last block"
  l = bases_offsets_and_lengths[end][2]
  o = bases_offsets_and_lengths[end][1]
  indices_integral = Vector{Int}[Int[] for i in 1:l]
  indices_nonintegral = Vector{Int}[Int[] for i in 1:l]
  for j in 1:length(local_coeffs[end])
    for i in o:(o + l - 1)
      if isintegral(local_coeffs[end][j][i])
        push!(indices_integral[i - o + 1], j)
      else
        push!(indices_nonintegral[i - o + 1], j)
      end
    end
  end

  #@info "Lengths $(length.(local_coeffs))"
  #@info "Unrestricted length of last block: $(length(local_coeffs[end]))"
  #@info "Restricted lengths (integral) of the last block $(length.(indices_integral))"
  #@info "Restricted lengths (non-integral) of the last block $(length.(indices_nonintegral))"

  dd = dim(A)

  # form the product of the first sets
  #@show length(cartesian_product_iterator([1:length(local_coeffs[i]) for i in 1:length(dec) - 1]))


  @info "Starting the new method :)"
  fl, x = recursive_iterator([length(local_coeffs[i]) for i in 1:length(dec)], dd, local_coeffs, bases_offsets_and_lengths, indices_integral, indices_nonintegral)
  @info "New method says $fl"
  if fl
    _vtemp = reduce(.+, (local_coeffs[i][x[i]] for i in 1:length(local_coeffs)))
    el = A(_vtemp * (H * special_basis_matrix))
    @assert el * O == I
    @info "Checking with old method"
    ffl, xx = _old_optimization(dd, local_coeffs, dec, bases_offsets_and_lengths, H, special_basis_matrix, indices_integral, indices_nonintegral, A)
    @assert ffl
    return true, el
  end

  return false, zero(A)

  ffl, xx = _old_optimization(dd, local_coeffs, dec, bases_offsets_and_lengths, H, special_basis_matrix, indices_integral, indices_nonintegral, A)

  @assert fl === ffl
  return ffl, xx


#  for u in Iterators.product(unit_reps...)
#    uu = sum(dec[i][2](u[i]) for i in 1:length(dec))
#    aui = [ dec[i][2](dec[i][2]\(alpha)) * dec[i][2](u[i]) for i in 1:length(dec)]
#    @assert sum(aui) == alpha * uu
#    if uu * alpha in I
#      @show alpha * uu
#      return true, uu * alpha
#    end
#  end
#  return false, zero(O)
end

function _old_optimization(dd, local_coeffs, dec, bases_offsets_and_lengths, H, special_basis_matrix, indices_integral, indices_nonintegral, A)
  vtemp = [zero(fmpq) for i in 1:dd]
  k = 0
  l = 0
  ll = [0 for i in 1:length(local_coeffs)]
  for idx in cartesian_product_iterator([1:length(local_coeffs[i]) for i in 1:length(dec) - 1])
    k += 1
    if k % 1000000 == 0
      @info "$k"
    end
    w = local_coeffs[1][idx[1]]
    for i in 1:dd
      ccall((:fmpq_set, libflint), Ref{Nothing}, (Ref{fmpq}, Ref{fmpq}), vtemp[i], w[i])
    end
    #@show vtemp
    for j in 2:(length(dec) - 1)
      w = local_coeffs[j][idx[j]]
      for i in bases_offsets_and_lengths[j][1]:dd
        add!(vtemp[i], vtemp[i], w[i])
      end
      #@show j, vtemp
    end
    #@show vtemp
    #@assert vtemp == reduce(.+, (local_coeffs[j][idx[j]] for j in 1:length(dec) - 1))
    if any(!isintegral, @view vtemp[1:bases_offsets_and_lengths[end][1] - 1])
      l += 1
      j = findfirst([any(!isintegral, vtemp[bases_offsets_and_lengths[j][1]:bases_offsets_and_lengths[j + 1][1] - 1]) for j in 1:length(dec) - 1])
      ll[j] += 1
      continue
    else
      @info "good"
    end
    o = bases_offsets_and_lengths[end][1]
    l = bases_offsets_and_lengths[end][2]
    ids = reduce(intersect, [isintegral(vtemp[o - 1 + i]) ? indices_integral[i] : indices_nonintegral[i] for i in 1:l])
    _vtempcopy = deepcopy(vtemp)
    #@show length(ids)
    for j in ids
      #for i in 1:dd
      #  ccall((:fmpq_set, libflint), Ref{Nothing}, (Ref{fmpq}, Ref{fmpq}), vtemp[i], _vtempcopy[i])
      #end
      _vtemp = deepcopy(vtemp) .+ local_coeffs[end][j]
      if all(isintegral, _vtemp)
        @info "found x = $((idx...,j))"
        return true, A(_vtemp * (H * special_basis_matrix))
      end
    end
  end
  @info "when I could have skipped $ll"
  @info "Skipped $l things"

  return false, zero(A)
end

# 
function _recursive_iterator!(x, lengths, d, elts::Vector, bases_offsets, indices_integral, indices_nonintegral, k, i, vtemp)
  if i > k
    println("2", x)
  elseif i == k # unroll 1-loop base case for speed
    # this is the last component

    # We do something clever for the indicies
    o = bases_offsets[end][1]
    l = bases_offsets[end][2]
    ids = copy(isintegral(vtemp[o]) ? indices_integral[1] : indices_nonintegral[1])
    for i in 2:l
      intersect!(ids, isintegral(vtemp[o - 1 + i]) ? indices_integral[i] : indices_nonintegral[i])
    end

    #ids2 = reduce(intersect!, (isintegral(vtemp[o - 1 + i]) ? indices_integral[i] : indices_nonintegral[i] for i in 1:l))
    #@assert ids == ids2

    for j in ids # 1:lengths[i]
      x[i] = j
      if _is_admissible(x, i, d, elts, bases_offsets, vtemp)
        #@assert all(isintegral, reduce(.+, (elts[k][x[k]] for k in 1:length(elts))))
        return true
      end
      #if _is_admissible(x, i, d, elts, bases_offsets)
      #  return true
      #end
      # here is the work done
    end
    return false
  else
    for j = 1:lengths[i]
      x[i] = j
      # So x = [...,j,*]
      # We test whether this is admissible
      if !_is_admissible(x, i, d, elts, bases_offsets, vtemp)
        continue
      end
      fl = _recursive_iterator!(x, lengths, d, elts, bases_offsets, indices_integral, indices_nonintegral, k, i + 1, vtemp)
      if fl
        return true
      end
    end
    return false
  end
end

function _is_admissible(x, i, d, elts, bases_offsets, vtemp)
  # Test if x[1,...,i] is admissible
  w = elts[1][x[1]]
  for k in 1:d
    ccall((:fmpq_set, libflint), Ref{Nothing}, (Ref{fmpq}, Ref{fmpq}), vtemp[k], w[k])
  end
  #@show vtemp
  for j in 2:i
    w = elts[j][x[j]]
    #@assert all(iszero, @view w[1:bases_offsets[j][1] - 1])
    for k in bases_offsets[j][1]:d
      add!(vtemp[k], vtemp[k], w[k])
    end
  end

  #@show i, vtemp

  # admissible means different things for different i
  # if i < end
  # then admissible means that the first i component of vtemp must be integral
  #
  # if i == end,
  # then admissible means that the last component must be integral

  vvtemp = @view vtemp[bases_offsets[i][1]:(bases_offsets[i][1] + bases_offsets[i][2] - 1)]

  if any(!isintegral, vvtemp)
    return false
  else
    return true
  end
end

function recursive_iterator(lengths::Vector{Int}, d::Int, elts::Vector, bases_offsets::Vector{Tuple{Int, Int}}, indices_integral, indices_nonintegral)
  k = length(lengths)
  x = zeros(Int, k)
  vtemp = fmpq[zero(fmpq) for i in 1:d]
  if _recursive_iterator!(x, lengths, d, elts, bases_offsets, indices_integral, indices_nonintegral, k, 1, vtemp)
    return true, x
  else
    return false, zeros(Int, k)
  end
end

################################################################################
#
#  IsIsomorphic
#
################################################################################

function _isisomorphic_generic(X, Y, side = :right)
  @assert side == :right
  C = _colon_raw(Y, X, :right)
  CI = ideal(algebra(X), C)
  for x in basis(CI)
    for y in basis(X)
      @assert  x * y in Y
    end
  end
  if Y != CI * X
    return false, zero(algebra(X))
  end
  Gamma = left_order(X)
  @assert Hecke._test_ideal_sidedness(CI, Gamma, :right)
  d = denominator(CI, Gamma)
  CIint = d * CI
  CIint.order = Gamma
  @assert Hecke._test_ideal_sidedness(CIint, Gamma, :right)
  fl, alpha  = __isprincipal(Gamma, CIint, :right)
  if fl
    alpha = inv(QQ(d)) * alpha
    @assert alpha * X == Y
  end
  return fl, alpha
end

################################################################################
#
#  Is Aut(G)-isomomorphic?
#
################################################################################

function _is_aut_isomorphic(X, Y; side::Symbol = :right)
  if side === :right
    return _is_aut_isomorphic_right(X, Y)
  elseif side === :left
    _, op = opposite_algebra(algebra(order(X)))
    Xop = op(X)
    Yop = op(Y)
    Xop.order = order(X)
    Yop.order = order(X)
    return _is_aut_isomorphic_right(Xop, Yop)
  end
end

function _is_aut_isomorphic_right(X, Y)
  QG = algebra(order(X))
  ZG = order(X)
  @assert _test_ideal_sidedness(X, ZG, :right)
  @assert _test_ideal_sidedness(Y, ZG, :right)
  G = group(QG)
  n = order(G)
  rep1 = fmpq_mat[ representation_matrix(QG(g), :right) for g in gens(G)];
  A = outer_automorphisms(G)
  isos = fmpq_mat[];
  @info "Computing automorphisms and induced maps"
  for a in A
    rep2 = [ representation_matrix(QG(a(g)), :right) for g in gens(G)];
    brep = _basis_of_commutator_algebra(rep1, rep2);
    @assert det(brep[1]) != 0
    t = brep[1]
    @assert all([representation_matrix(QG(a(g)), :right) * t == t * representation_matrix(QG(g), :right) for g in gens(G)])
    push!(isos, t);
  end
  @info "Testing $(length(isos)) isomorphisms"
  for j in 1:length(isos);
    @info "$(j)/$(length(isos))"
    t = isos[j]
    newbas = fmpq_mat(basis_matrix(Y)) * t
    Ytwisted = ideal_from_lattice_gens(QG, order(Y), [elem_from_mat_row(QG, newbas, i) for i in 1:n]);
    @assert _test_ideal_sidedness(Ytwisted, ZG, :right)
    fl, _ = _isisomorphic_generic(X, Ytwisted, :right)
    if fl
      return true
    end
  end
  return false
end

function _twists(Y)
  res = typeof(Y)[]
  QG = algebra(order(Y))
  ZG = order(Y)
  G = group(QG)
  n = order(G)
  rep1 = fmpq_mat[ representation_matrix(QG(g), :right) for g in gens(G)];
  A = outer_automorphisms(G)
  @info "Outer automorphisms $(length(A))"
  isos = fmpq_mat[];
  @info "Computing automorphisms and induced maps"
  for a in A
    rep2 = [ representation_matrix(QG(a(g)), :right) for g in gens(G)];
    brep = _basis_of_commutator_algebra(rep1, rep2);
    @assert det(brep[1]) != 0
    t = brep[1]
    @assert all([representation_matrix(QG(a(g)), :right) * t == t * representation_matrix(QG(g), :right) for g in gens(G)])
    push!(isos, t);
  end
  @info "Testing $(length(isos)) isomorphisms"
  for j in 1:length(isos);
    @info "$(j)/$(length(isos))"
    t = isos[j]
    newbas = fmpq_mat(basis_matrix(Y)) * t
    Ytwisted = ideal_from_lattice_gens(QG, order(Y), [elem_from_mat_row(QG, newbas, i) for i in 1:n]);
    @assert _test_ideal_sidedness(Ytwisted, ZG, :right)
    push!(res, Ytwisted)
  end
  return res
end

function twist_classes(Y)
  Ytwist = _twists(Y)
  res = typeof(Y)[]
  for i in 1:length(Ytwist)
    @info "#Twists/Aut(G): $i, $(length(res))"
    found = false
    if any(Z -> _isisomorphic_generic(Z, Ytwist[i])[1], res)
      found = true
    end
    if !found
      push!(res, Ytwist[i])
    end
  end
  return res
end

function representation_matrix_wrt(x::AlgAssAbsOrdElem, v::Vector, action = :left)
  O = parent(x)
  M = FakeFmpqMat(basis_matrix(elem_in_algebra.(v)))
  M1 = inv(M)
  B = FakeFmpqMat(representation_matrix(elem_in_algebra(x, copy = false), action))
  B = mul!(B, M, B)
  B = mul!(B, B, M1)
  @assert B.den == 1
  return B.num
end

function _local_coeffs_buffer(A, l)
  D = get_attribute!(A, :local_coeffs_buffer) do
    Dict{Vector{Int}, Vector{Vector{Vector{fmpq}}}}()
  end::Dict{Vector{Int}, Vector{Vector{Vector{fmpq}}}}

  return get!(D, l) do
    Vector{Vector{fmpq}}[Vector{fmpq}[ fmpq[zero(fmpq) for i in 1:dim(A)] for ii in 1:l[j]] for j in 1:length(l)]
  end::Vector{Vector{Vector{fmpq}}}
end

function _compute_local_coefficients_parallel(alpha, A, dec_sorted, units_sorted, M, block_size = 1)
  #push!(_debug, (alpha, A, dec_sorted, units_sorted, M, block_size))
  res = Vector{Vector{fmpq}}[]
  k = dim(A)
  kblock = k * block_size
  nt = Threads.nthreads()
  #nt = 1

  @assert size(M) == (k, k)
  #@assert all(x -> ncols(x) == k, tmps)
  #@assert all(x -> ncols(x) == k, tmps2)
  __local_coeffs = _local_coeffs_buffer(A, length.(units_sorted))
  for i in 1:length(dec_sorted)
    ui = units_sorted[i]
    #@info "Allocating for result"
    _local_coeffs = __local_coeffs[i]
    #_local_coeffs = _local_coeffs_buffer(A, length(ui)) #Vector{fmpq}[ fmpq[zero(fmpq) for i in 1:k] for ii in 1:length(ui)]
    #_local_coeffs = Vector{fmpq}[ fmpq[zero(fmpq) for i in 1:k] for ii in 1:length(ui)]
    m = dec_sorted[i][2]::morphism_type(AlgAss{fmpq}, typeof(A))
    alphai = dec_sorted[i][2](dec_sorted[i][2]\(alpha))
    kblock = div(length(ui), nt) 
    if mod(length(ui), nt) != 0
      kblock += 1
    end
    if length(ui) < 100
      kblock = length(ui)
    end
    par = collect(Iterators.partition(1:length(ui), kblock))
    @assert length(ui) < 100 || length(par) == nt
    #@info "Length/Blocksize: $(length(ui))/$(kblock)"
    tmps = [zero_matrix(QQ, kblock, k) for i in 1:nt]
    tmps2 = [zero_matrix(QQ, kblock, k) for i in 1:nt]
    tmp_elem = [A() for i in 1:nt]
    if length(par) >= nt
      GC.gc(true)
      Threads.@threads for i in 1:length(par)
        #thi = 1 #Threads.threadid()
        thi = Threads.threadid()
        p = par[i]
        t1 = tmps[thi]
        t2 = tmps2[thi]
        t_elem = tmp_elem[thi]
        for (j, j_index) in enumerate(p)
          u =  ui[j_index]
          #aui =  alphai * u
          mul!(t_elem, alphai, u)
          __set_row!(t1, j, coefficients(t_elem, copy = false))
        end
        mul!(t2, t1, M)
        for (j, j_index) in enumerate(p)
          Hecke.__set_row!(_local_coeffs[j_index], t2, j)
        end
      end
    else
      for i in 1:length(par)
        #thi = 1 #Threads.threadid()
        thi = 1
        p = par[i]
        t1 = tmps[thi]
        t2 = tmps2[thi]
        t_elem = tmp_elem[thi]
        for (j, j_index) in enumerate(p)
          u =  ui[j_index]
          mul!(t_elem, alphai, u)
          __set_row!(t1, j, coefficients(t_elem, copy = false))
        end
        mul!(t2, t1, M)
        for (j, j_index) in enumerate(p)
          Hecke.__set_row!(_local_coeffs[j_index], t2, j)
        end
      end
    end
    push!(res, _local_coeffs)
  end
  return res
end

function parallel_mul(list, M, res)
  par = collect(Iterators.partition(1:length(list), nrows(M)))
  Ms = [deepcopy(M) for i in 1:nt]
  #res = Vector{fmpq}[]
  Threads.@threads for i in 1:length(par)
    thi = Threads.threadid()
    p = par[i]
    t1 = tmps[thi]
    t2 = tmps2[thi]
    for (j, j_index) in enumerate(p)
      u = list[j_index]
      Hecke.__set_row!(t1, j, u)
    end
    mul!(t2, t1, M)
    for (j, j_index) in enumerate(p)
      Hecke.__set_row!(res[j_index], t2, j)
      #push!(res, fmpq[t2[j, k] for k in 1:ncols(M)])
    end
  end
  return res
end

function _save_elements(io::IO, A, bmat_order::FakeFmpqMat, bmat_conductor::FakeFmpqMat, idempotents::Vector, v::Vector)
  println(io, _stringify(vec(A.mult_table)))
  println(io, _stringify(_eltseq(fmpq_mat(bmat_order))))
  bmatc = fmpq_mat(bmat_conductor)
  bmatcc = change_base_ring(ZZ, denominator(bmatc) * bmatc)
  @assert ishnf(bmatcc, :lowerleft)
  println(io, _stringify(_eltseq(fmpq_mat(bmat_conductor))))
  println(io, _stringify(coefficients.(idempotents)))
  for i in 1:length(v)
    w = v[i]
    println(io, _stringify(length(w)))
    for j in 1:length(w)
      println(io, _stringify(coefficients(w[j], copy = false)))
    end
  end
end

function _save_elements(file::String, A, bmat_order, bmat_conductor, idempotents, v)
  open(file, "w") do io
    _save_elements(io, A, bmat_order, bmat_conductor, idempotents, v)
  end
end

function _load_all(file, A)
  open(file) do io
    _load_all(io, A)
  end
end

function _load_header(file::String)
  open(file) do io
    _load_header(io)
  end
end

function _load_header(io::IO)
  b, v = _parse(Vector{Int}, io)
  n = length(v)
  d = isqrt(n)
  mult_table = reshape(v, (d, d))
  b, v = _parse(Vector{fmpq}, io)
  n = length(v)
  d = isqrt(n)
  @assert d^2 == n
  bmat_order = FakeFmpqMat(matrix(QQ, d, d, v))
  b, v = _parse(Vector{fmpq}, io)
  bmat_conductor = FakeFmpqMat(matrix(QQ, d, d, v))
  return mult_table, bmat_order, bmat_conductor
end

function _load_rest(io::IO, A)
  b, v = _parse(Vector{Vector{fmpq}}, io)
  idempotents = [A(v[i], copy = false) for i in 1:length(v)]
  @assert sum(idempotents) == one(A)
  k = length(v)
  units = Vector{Vector{elem_type(A)}}(undef, k)
  for i in 1:k
    _, l = _parse(Int, io)
    res = Vector{elem_type(A)}(undef, l)
    for j in 1:l
      _, v = _parse(Vector{fmpq}, io)
      res[j] = A(v, copy = false)
    end
    units[i] = res
  end
  return idempotents, units
end

function _load_all(io::IO, A)
  mult_table, bmat_order, bmat_conductor = _load_header(io)
  idem, units = _load_rest(io, A)
  return mult_table, bmat_order, bmat_conductor, idem, units
end

function _is_suitable_file(io::IO, A, M, F; check_algebra::Bool = false)
  mult_table, bmat_order, bmat_conductor = _load_header(io)
  if mult_table != A.mult_table
    if check_algebra
      return false
    else
      error("Multiplication tables do not match")
    end
  end
  if basis_matrix(M) != bmat_order
    @info "Orders do not coincide"
    return false
  end
  if basis_matrix(F) != bmat_conductor
    @info "Conductors do not coincide"
    return false
  end
  @info "Conductors do coincide"
  return true
end

function _is_suitable_file(file::String, A, M, F; check_algebra::Bool = false)
  open(file) do io
    _is_suitable_file(io, A, M, F, check_algebra = check_algebra)
  end
end

function _load_units_from_rest(io::IO, A)
  idempotents, units = _load_rest(io, A) 
  #@info "Reordering if necessary"
  dec = decompose(A)
  k = length(dec)
  perm = Int[]
  idemsA = [dec[i][2](one(dec[i][1])) for i in 1:k]
  @assert length(dec) == length(idempotents)
  for i in 1:k
    e = idemsA[i]
    for j in 1:k
      if idempotents[j]  == e
        push!(perm, j)
        break
      end
    end
  end
  @assert length(perm) == k
  @assert idempotents[perm] == idemsA
  _units = permute!(units, perm)
  return _units
end

function __test_load(file::String, A, M, F)
  local units
  open(file) do io
    fl = _is_suitable_file(io, A, M, F, check_algebra = true)
    @assert fl
    units = _load_units_from_rest(io, A)
  end
  return units
end

function _find_maximal_order_in_file(O; dir = ".")
  l = readdir(dir)
  for file in l
    if !isfile(file)
      continue
    end
    if !endswith(file, ".tmpinfo")
      continue
    end
    mult_table, bmat_order, bmat_conductor = _load_header(file)
    if algebra(O).mult_table != mult_table
      continue
    end
    d = denominator(basis_matrix(O, copy = false) * inv(bmat_order))
    if isone(d)
      return Order(algebra(O), bmat_order)
    end
  end
  return nothing
end

