################################################################################
#
#  Is principal for maximal orders
#
################################################################################

include("PIP/misc.jl")
include("PIP/maximal.jl")
include("PIP/bley_johnston.jl")
include("PIP/bley_hofmann_johnston.jl")
include("PIP/unit_group_generators.jl")

abstract type _PIPDefault end

abstract type _PIPEichler end

function _satisfies_condition_h(A::AbstractAssociativeAlgebra)
  dec = decompose(A)
  for (B, _) in dec
    if is_commutative(B)
      continue
    end
    C, = _as_algebra_over_center(B)
    s = schur_index(C)
    if s > 1
      return false
    end
  end
  return true
end

_is_principal_with_data(::Type{_PIPEichler}, x...; kw...) = _is_principal_with_data(_PIPDefault, x...; kw...)

_is_principal_with_data(::Type{<: Any}, x...; kw...) = _is_principal_with_data_bj(x...; kw...)

_is_principal(::Type{_PIPEichler}, x...; kw...) = _is_principal(_PIPDefault, x...; kw...)

_is_principal(::Type{<: Any}, x...; kw...) = _is_principal_with_data_bj(x...; kw...)[1]

function _is_principal_with_data(I, O = right_order(I); side = :right, local_freeness = false)
  A = algebra(O)
  @assert side === :right
  if is_commutative(A)
    return _is_principal_with_data_etale(I, local_freeness = local_freeness)
#  elseif is_eichler(A)
#    return _is_principal_with_data(_PIPEichler, I, O; side = side)
  elseif _satisfies_condition_h(A)
    return _is_principal_with_data_bhj(I, O; side = side, local_freeness = local_freeness)
  else
    return _is_principal_with_data(_PIPDefault, I, O; side = side, local_freeness = local_freeness)
  end
end

function _is_principal(I, O = right_order(I); side = :right, local_freeness = false)
  A = algebra(O)
  @assert side === :right
  if is_commutative(A)
    return _is_principal_with_data_etale(I, local_freeness = local_freeness)[1]
  elseif is_eichler(A)
    return _is_principal(_PIPEichler, I, O; side = side, local_freeness = local_freeness)
  else
    return _is_principal(_PIPDefault, I, O; side = side, local_freeness = local_freeness)
  end
end

function is_principal(I::AlgAssAbsOrdIdl, O = nothing; side = :right)
  if O === nothing
    # check side here
    _O = right_order(I)
  else
    _O = O::order_type(algebra(I))
  end
  return _is_principal(I, _O, side = side)
end

function is_principal_with_data(I::AlgAssAbsOrdIdl, O = nothing; side = :right)
  if O === nothing
    # check side here
    _O = right_order(I)
  else
    _O = O::order_type(algebra(I))
  end
  return _is_principal_with_data(I, _O; side = side)
end

################################################################################
#
#  IsIsomorphic
#
################################################################################

function _isisomorphic_generic(X, Y; side::Symbol = :right, strategy = :default)
  if side === :right
    return _isisomorphic_generic_right(X, Y, strategy = strategy)
  elseif side === :left
    _, op = opposite_algebra(algebra(order(X)))
    Xop = op(X)
    Yop = op(Y)
    Xop.order = order(X)
    Yop.order = order(X)
    return _isisomorphic_generic_right(Xop, Yop, strategy = strategy)
  end
end

function _isisomorphic_generic_right(X, Y; strategy = :default)
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
  if strategy == :default
    fl, alpha  = __isprincipal(Gamma, CIint, :right)
    if fl
      alpha = inv(QQ(d)) * alpha
      @assert alpha * X == Y
    end
  elseif strategy == :s1
    fl = _is_principal(CIint, Gamma; side = :right)::Bool
    alpha = zero(algebra(order(X)))
  else
    error("strategy :$strategy not valid")
  end

  return fl, alpha
end

__isprincipal_s1(R, I, side) = error("asd")

################################################################################
#
#  Is Aut(G)-isomomorphic?
#
################################################################################

function _is_aut_isomorphic(X, Y; side::Symbol = :right, strategy = :default)
  if side === :right
    return _is_aut_isomorphic_right(X, Y, strategy = strategy)
  elseif side === :left
    _, op = opposite_algebra(algebra(order(X)))
    Xop = op(X)
    Yop = op(Y)
    Xop.order = order(X)
    Yop.order = order(X)
    return _is_aut_isomorphic_right(Xop, Yop, strategy = strategy)
  end
end

function _is_aut_isomorphic_right(X, Y; strategy = :default)
  QG = algebra(order(X))
  ZG = order(X)
  @assert _test_ideal_sidedness(X, ZG, :right)
  @assert _test_ideal_sidedness(Y, ZG, :right)
  G = group(QG)
  n = degree(ZG)
  rep1 = QQMatrix[ representation_matrix(QG(g), :right) for g in gens(G)];
  A = outer_automorphisms(G)
  isos = QQMatrix[];
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
    newbas = QQMatrix(basis_matrix(Y)) * t
    Ytwisted = ideal_from_lattice_gens(QG, order(Y), [elem_from_mat_row(QG, newbas, i) for i in 1:n]);
    @assert _test_ideal_sidedness(Ytwisted, ZG, :right)
    fl, _ = _isisomorphic_generic(X, Ytwisted, side = :right, strategy = strategy)
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
  n = degree(ZG)
  rep1 = QQMatrix[ representation_matrix(QG(g), :right) for g in gens(G)];
  A = outer_automorphisms(G)
  @info "Outer automorphisms $(length(A))"
  isos = QQMatrix[];
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
    newbas = QQMatrix(basis_matrix(Y)) * t
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

################################################################################
#
#  Isfree
#
################################################################################

function is_free_with_basis(a::AlgAssAbsOrdIdl)
  _assert_has_refined_wedderburn_decomposition(algebra(a))
  R = order(a)
  fl, beta = _isprincipal(a, R, :right)
  return fl, [beta]
end
