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
  @assert _test_ideal_sidedness(a, M, :right)
  @assert ismaximal(M)

  dena = denominator(a, M)
  aorig = a
  a = dena * a

  A = algebra(M)
  res = decompose(A)
  abas = basis(a)
  Mbas = basis(M)
  
  @assert all(b in M for b in abas)
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
    @assert all(b in MinB for b in basis(ainB))
    fl, gen = _is_principal_maximal_simple_component(ainB, MinB, side)
    #@show "not simple for component", B
    if !fl
      return false, zero(A)
    end
    push!(gens, mB(gen))
  end
  return true, inv(base_ring(A)(dena)) * sum(gens)
end

function absolute_basis(M::AlgAssAbsOrd{<:AlgAss{fmpq}})
  return basis(M)
end

function _is_principal_maximal_simple_component(a, M, side = :right)
  A = algebra(M)
  ZA, _ = _as_algebra_over_center(A)
  @show A
  @show ZA
  if base_ring(A) isa FlintRationalField && dim(A) == 4 && !issplit(A)
    return _is_principal_maximal_quaternion(a, M, side)
  elseif dim(ZA) == 4 && !isdefined(A, :isomorphic_full_matrix_algebra)
    #@show A
    return _is_principal_maximal_quaternion_generic(a, M, side)
  else
    local B::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    @assert isdefined(A, :isomorphic_full_matrix_algebra)
    B, AtoB = A.isomorphic_full_matrix_algebra
    OB = _get_order_from_gens(B, elem_type(B)[AtoB(elem_in_algebra(b)) for b in absolute_basis(M)])
    ainOB = ideal_from_lattice_gens(B, elem_type(B)[(AtoB(b)) for b in absolute_basis(a)])
    fl, gen = _is_principal_maximal_full_matrix_algebra(ainOB, OB, side)
    return fl, (AtoB\gen)::elem_type(A)
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
    AM = algebra(M)
    aN = ideal_from_lattice_gens(algebra(M), elem_type(AM)[b * inv(S) for b in absolute_basis(a)])
    fl, _gen = _isprincipal_maximal_simple_nice(aN, N, side)
    gen = _gen * S
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
  J = st.coeffs[end] * inv(a)
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
  h = hnf(FakeFmpqMat(z)')'
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
  if hnf(basis_matrix(O)) != hnf(basis_matrix(right_order(a)))
    return false, zero(algebra(O))
  end

  if ismaximal(O)
    return _isprincipal_maximal(a, O, side)
  end


  # So O is the right order of a

  n = dim(algebra(O))
  aa = denominator(a, O) * a
  aa.order = O
  for (p, ) in factor(discriminant(O))
    println("Testing local freeness at ", p)
    if !islocally_free(O, aa, p, side = :right)[1]::Bool
      return false, zero(algebra(O))
    end
  end

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
  F = ideal_from_lattice_gens(A, O, basis_F, :twosided)

  aorig = a

  # I shoul improve this
  a, sca = _coprime_integral_ideal_class(a, F)
  @show "Found coprime integral ideal class"

  @assert sca * aorig == a

  @assert a + F == one(A) * O

  # Compute K_1(O/F) and the subgroup of R generated by nr(a)*OZ for a in k1 where
  # nr is the reduced norm and OZ the maximal order in Z
  aOA = sum(b * OA for b in basis(a))
  fl, beta = _isprincipal_maximal(aOA, OA, side)
  if !fl
    return false, zero(A)
  end
  @assert beta * OA == aOA

  println("Computing K1...")
  k1 = K1_order_mod_conductor(O, OA, F, FinZ)
  OZ = maximal_order(Z)
  Q, mQ = quo(OZ, FinZ)
  Quni, mQuni = unit_group(Q)
  U::GrpAbFinGen, mU = unit_group(OZ)
  println("Solving principal ideal problem over maximal order...")

  #@show Q
  normbeta = OZ(normred_over_center(beta, ZtoA))

  #@show parent(normbeta) == domain(mQ)
  ttt = mQuni\(mQ(normbeta))
  imgofK1 = GrpAbFinGenElem[ mQuni\(mQ(OZ(normred_over_center(elem_in_algebra(b), ZtoA)))) for b in k1]
  QbyK1, mQbyK1 = quo(Quni, imgofK1)

  SS, mSS = sub(Quni, imgofK1)

  S, mS = sub(QbyK1, elem_type(QbyK1)[ mQbyK1(mQuni\(mQ(mU(U[i])::elem_type(OZ)))) for i in 1:ngens(U)])

  fl, u = haspreimage(mS, mQbyK1(ttt))

  println("Solving norm requation over center")
  UU = _solve_norm_equation_over_center(OA, ZtoA(elem_in_algebra(mU(u)::elem_type(OZ))))

  fll, uu = haspreimage(mSS,  mQuni\(mQ(OZ(normred_over_center(elem_in_algebra(UU), ZtoA)))) - ttt)
  
  @assert fll
  
  elemA = one(A)
  for i in 1:length(uu.coeff)
    if !iszero(uu.coeff[1, i])
      elemA = elemA * elem_in_algebra(k1[i])^Int(uu.coeff[1, i])
    end
  end

  ##@show mQuni\(mQ(OZ(normred_over_center(elem_in_algebra(UU), ZtoA)))) ==  mQuni\(mQ(OZ(normred_over_center(beta * elemA, ZtoA))))

  println("Lifting to norm one unit")
  V = lift_norm_one_unit( UU^(-1) * OA(elemA)  * OA(beta), F)

  gamma =  beta * inv(elem_in_algebra(UU) * V)
  @assert gamma * O == a
  @assert inv(sca) * gamma * O == aorig

  return true, inv(sca) * gamma
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
  if degree(A) == 4 && !issplit(A)
    return _solve_norm_equation_over_center_quaternion(M, x)
  else
    local B::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    @assert isdefined(A, :isomorphic_full_matrix_algebra)
    B, AtoB = A.isomorphic_full_matrix_algebra
    Mbas = absolute_basis(M)
    MinB = _get_order_from_gens(B, elem_type(B)[ AtoB(elem_in_algebra(b)) for b in Mbas])
    y = Hecke._solve_norm_equation_over_center_full_matrix_algebra(MinB, AtoB(x)::elem_type(B))
    sol = M(AtoB\elem_in_algebra(y))
    ZA, ZAtoA = center(A)
    @assert ZAtoA(normred_over_center(elem_in_algebra(sol), ZAtoA)) == x
    return sol
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
    MB = Order(B, [BtoA\elem_in_algebra(b) for b in absolute_basis(M)])
    xinB = BtoA\x
    solB = _solve_norm_equation_over_center_full_rational_matrix_algebra(MB, xinB)
    sol = M(BtoA(elem_in_algebra(solB)))
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
  for i in 1:length(res)
    Ai, AitoA = res[i]
    MinAi = Order(Ai, elem_type(Ai)[ AitoA\(AitoA(one(Ai)) * elem_in_algebra(b)) for b in Mbas])
    xinAi = MinAi(preimage(AitoA, elem_in_algebra(x)))
    Fi = ideal_from_lattice_gens(Ai, MinAi, [ AitoA\b for b in basis(F) ], :twosided)
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
  if degree(A) == 4 && !issplit(A)
    return _lift_norm_one_unit_quaternion(x, F)
  else
    local B::AlgMat{nf_elem, Generic.MatSpaceElem{nf_elem}}
    @assert isdefined(A, :isomorphic_full_matrix_algebra)
    B, AtoB = A.isomorphic_full_matrix_algebra
    Mbas = basis(M)
    MinB = _get_order_from_gens(B, elem_type(B)[ AtoB(elem_in_algebra(b)) for b in Mbas])
    FinB = ideal_from_lattice_gens(B, MinB, elem_type(B)[ AtoB(b) for b in basis(F) ], :twosided)
    y = _lift_norm_one_unit_full_matrix_algebra(MinB(AtoB(elem_in_algebra(x))::elem_type(B)), FinB)
    return (AtoB\y)::elem_type(A)
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
  el, id = pseudo_basis(FinZA)[1]
  fl, el2 = isprincipal(id)
  @assert fl 
  n = el.coeffs[1] * el2
  OK = base_ring(M)
  @assert basis_pmatrix(M).matrix == identity_matrix(base_ring(A), dim(A))
  R, mR = quo(OK, OK(n) * OK)
  @assert isone(mR(FacElem(det(matrix(elem_in_algebra(x))))))
  li = _lift_unimodular_matrix(change_base_ring(OK, matrix(elem_in_algebra(x))), OK(n), R)
  return A(change_base_ring(base_ring(A), li))
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

  li = _lift_unimodular_matrix(change_base_ring(FlintZZ, matrix(xwrtR)), nn, ResidueRing(FlintZZ, nn))

  return (inv(c) * B(change_base_ring(FlintQQ, li)) * c)
end

################################################################################
#
#  Lifting unimodular matrix
#
################################################################################

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

function lift_triangular_matrix(E)
  #@show E
  z = map_entries(_lift, E)
  #@show matrix(base_ring(E), z)
  @assert matrix(base_ring(E), z) == E
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
    x = zero(A)
    while !isunit(M[1, 1] + x * M[2, 1])
      x += 1
    end
    E[1,2] = M[1,1] + x*M[2,1]
    B = E*M
    @assert det(B) == 1
    push!(left_elementary, E)
	end

  #@show B
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
  @show a * OK + b * OK
  fl, g = isprincipal(a * OK + b * OK)
  @assert fl
  Ma = representation_matrix(a)
  Mb = representation_matrix(b)
  M = vcat(Ma, Mb)
  onee = matrix(FlintZZ, 1, d, coordinates(g))
  fl, v = can_solve(M, onee, side = :left)
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
    dd = dim(B)
    mtB = multiplication_table(B)
    BtoA = zero_matrix(K, dim(B), d)
    AtoB = zero_matrix(K, d, dim(B))
    for i = 1:dd
      BtoA[i, offset + i] = one(K)
      AtoB[offset + i, i] = one(K)
      for j = 1:dd
        for k = 1:dd
          mt[i + offset, j + offset, k + offset] = multiplication_table(B)[i, j, k]
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
  if isdefined(A, :isomorphic_full_matrix_algebra)
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
    r = unit_rank(OK)
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

  if n == 2 && unit_rank(OK) == 0 && degree(K) == 2
    throw(NotImplemented())
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
    @show m, length(OT)
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
    fl, w = can_solve(change_base_ring(FlintZZ, d * Me), change_base_ring(FlintZZ, d * v), side = :left)
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
  fl, v = can_solve(map_entries(x -> FlintZZ(x * dd), M1), map_entries(x -> FlintZZ(x * dd), M2), side = :left)
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

function center(G::GrpGen)
  if isabelian(G)
    return subgroup(G, collect(G))
  end

  c = elem_type(G)[]

  for g in G
    cent = true
    for h in G
      if h * g != g *h
        cent = false
        break
      end
    end

    if cent
      push!(c, g)
    end
  end

  return subgroup(G, c)
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

