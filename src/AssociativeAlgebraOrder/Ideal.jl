################################################################################
#
#  Accessors and construction
#
################################################################################

order(I::AssociativeAlgebraOrderIdeal) = I.order

lattice(I::AssociativeAlgebraOrderIdeal) = I.lattice

algebra(I::AssociativeAlgebraOrderIdeal) = algebra(lattice(I))

_algebra(I::AssociativeAlgebraOrderIdeal) = algebra(I)

base_ring(I::AssociativeAlgebraOrderIdeal) = base_ring(lattice(I))

ideal_type(::Type{AssociativeAlgebraOrder{S, T}}) where {S, T} =
  AssociativeAlgebraOrderIdeal{AssociativeAlgebraOrder{S, T}, AssociativeAlgebraLattice{S, T}}

fractional_ideal_type(::Type{AssociativeAlgebraOrder{S, T}}) where {S, T} =
  ideal_type(AssociativeAlgebraOrder{S, T})

function _ideal(O::AssociativeAlgebraOrder, L::AssociativeAlgebraLattice)
  @req algebra(O) === algebra(L) "The order and lattice have different ambient algebras"
  @req base_ring(O) === base_ring(L) "The order and lattice have different coefficient rings"
  return AssociativeAlgebraOrderIdeal(O, L)
end

function _set_sidedness(I::AssociativeAlgebraOrderIdeal, side)
  if side === :left
    I.isleft = 1
    I.isright = 0
  elseif side === :right
    I.isleft = 0
    I.isright = 1
  elseif side === :twosided
    I.isleft = 1
    I.isright = 1
  elseif side === nothing || side === :nothing
    I.isleft = 0
    I.isright = 0
  else
    error("Not a valid side ($side)")
  end
end

function _test_ideal_sidedness(I::AssociativeAlgebraOrderIdeal, side::Symbol)
  if side === :left
    return issubset(lattice(order(I))*lattice(I), lattice(I))
  elseif side === :right
    return issubset(lattice(I)*lattice(order(I)), lattice(I))
  elseif side === :twosided
    return _test_ideal_sidedness(I, :left) && _test_ideal_sidedness(I, :right)
  else
    error("Side must be :left or :right")
  end
end

function _determine_sidedness!(I::AssociativeAlgebraOrder, side::Symbol)
  is_left_ideal(I) && is_right_ideal(I)
  return nothing
end

function is_left_ideal(I::AssociativeAlgebraOrderIdeal)
  I.isleft == 1 && return true
  I.isleft == 2 && return false
  I.isleft = _test_ideal_sidedness(I, :left) ? 1 : 2
  return I.isleft == 1
end

function is_right_ideal(I::AssociativeAlgebraOrderIdeal)
  I.isright == 1 && return true
  I.isright == 2 && return false
  I.isright = _test_ideal_sidedness(I, :right) ? 1 : 2
  return I.isright == 1
end

function ideal(O::AssociativeAlgebraOrder, L::AssociativeAlgebraLattice;
               side::Union{Symbol, Nothing} = nothing, check::Bool = true)
  @req side in (:left, :right, :twosided) "Side must be :left, :right or :twosided"
  I = _ideal(O, L)
  _set_sidedness(I, side)
  if check
    I.isleft == 1 && @req _test_ideal_sidedness(I, :left) "The lattice is not a left ideal of the order"
    I.isright == 1 && @req _test_ideal_sidedness(I, :right) "The lattice is not a right ideal of the order"
  end
  return I
end

function ideal(O::AssociativeAlgebraOrder, M::Union{MatElem, PMat};
               side::Union{Symbol, Nothing} = nothing, check::Bool = true,
               is_basis_matrix::Bool = false)
  @req side in (:left, :right, :twosided) "Side must be :left, :right or :twosided"
  L = lattice(algebra(O), base_ring(O), M; is_basis_matrix)
  return ideal(O, L; side, check)
end

#function ideal(O::AssociativeAlgebraOrder,
#               elts::Vector{<:Union{AbstractAssociativeAlgebraElem, PseudoElement}};
#               side::Union{Symbol, Nothing} = nothing, check::Bool = true)
#  L = lattice(algebra(O), base_ring(O), elts)
#  return ideal(O, L; side, check)
#end

#function ideal(O::AssociativeAlgebraOrder, x::AbstractAssociativeAlgebraElem, side::Symbol)
#  @req parent(x) === algebra(O) "The element and order have different ambient algebras"
#  LO = lattice(O)
#  L = if side === :left
#    LO*x
#  elseif side === :right
#    x*LO
#  elseif side === :twosided
#    (LO*x)*LO
#  else
#    error("Not a valid side")
#  end
#  return ideal(O, L; side, check = false)
#end

#ideal(O::AssociativeAlgebraOrder, x::AbstractAssociativeAlgebraElem) = ideal(O, x, :twosided)

#function ideal(O::AssociativeAlgebraOrder, x::AssociativeAlgebraOrderElem, side::Symbol)
#  @req parent(x) === O "The element does not belong to the order"
#  return ideal(O, elem_in_algebra(x, copy = false), side)
#end
#
#ideal(O::AssociativeAlgebraOrder, x::AssociativeAlgebraOrderElem) = ideal(O, x, :twosided)
#
#zero_ideal(O::AssociativeAlgebraOrder) =
#  ideal(O, zero_lattice(algebra(O), base_ring(O)); side = :twosided, check = false)
#
#unit_ideal(O::AssociativeAlgebraOrder) =
#  ideal(O, lattice(O); side = :twosided, check = false)
#
#ideal(O::AssociativeAlgebraOrder) = unit_ideal(O)

################################################################################
#
#  Basis and rank
#
################################################################################

basis_matrix(I::AssociativeAlgebraOrderIdeal; copy::Bool = true) = basis_matrix(lattice(I); copy)

basis(I::AssociativeAlgebraOrderIdeal; copy::Bool = true) = [order(I)(x; check = false) for x in basis(lattice(I); copy = false)]

pseudo_basis(I::AssociativeAlgebraOrderIdeal; copy::Bool = true) = pseudo_basis(lattice(I); copy)

rank(I::AssociativeAlgebraOrderIdeal) = rank(lattice(I))

ambient_rank(I::AssociativeAlgebraOrderIdeal) = ambient_rank(lattice(I))

is_full_lattice(I::AssociativeAlgebraOrderIdeal) = is_full_lattice(lattice(I))

is_full_rank(I::AssociativeAlgebraOrderIdeal) = is_full_rank(lattice(I))

iszero(I::AssociativeAlgebraOrderIdeal) = iszero(lattice(I))

isone(I::AssociativeAlgebraOrderIdeal) = lattice(I) == lattice(order(I))

one(I::AssociativeAlgebraOrderIdeal) = unit_ideal(order(I))

################################################################################
#
#  Containment and equality
#
################################################################################

in(x::Union{AbstractAssociativeAlgebraElem, PseudoElement}, I::AssociativeAlgebraOrderIdeal) = in(x, lattice(I))

function in(x::AssociativeAlgebraOrderElem, I::AssociativeAlgebraOrderIdeal)
  return in(elem_in_algebra(x, copy = false), lattice(I))
end

issubset(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal) =
  issubset(lattice(I), lattice(J))

  ==(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal) = base_ring(I) == base_ring(J) && lattice(I) == lattice(J)

Base.hash(I::AssociativeAlgebraOrderIdeal, h::UInt) = hash(lattice(I), h)

Base.copy(I::AssociativeAlgebraOrderIdeal) = I

################################################################################
#
#  Arithmetic
#
################################################################################

# We allow arithmetic between any two O-ideals, as long as the result is an
# O-ideal (with respect to some side)
function _check_compatible(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal)
  @req order(I) === order(J) "The ideals belong to different orders"
  _check_compatible(lattice(I), lattice(J))
  return nothing
end

function _ideal_with_sidedness(O, L, isleft::Int, isright::Int)
  I = _ideal(O, L)
  I.isleft = isleft
  I.isright = isright
  return I
end

function +(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal)
  _check_compatible(I, J)
  L = _ideal_with_sidedness(order(I), lattice(I) + lattice(J),
                            I.isleft == 1 && J.isleft == 1 ? 1 : 0,
                            I.isright == 1 && J.isright == 1 ? 1 : 0)
  @req L.isright == 1 || L.isleft == 1 "Ideal sum is not an ideal"
  return L
end

function intersect(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal)
  _check_compatible(I, J)
  L = _ideal_with_sidedness(order(I), intersect(lattice(I), lattice(J)),
                               I.isleft == 1 && J.isleft == 1 ? 1 : 0,
                               I.isright == 1 && J.isright == 1 ? 1 : 0)
  @req L.isright == 1 || L.isleft == 1 "Ideal sum is not an ideal"
  return L
end

function *(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal)
  _check_compatible(I, J)
  L = _ideal_with_sidedness(order(I), lattice(I)*lattice(J),
                               I.isleft == 1 ? 1 : 0,
                               J.isright == 1 ? 1 : 0)
  @req L.isright == 1 || L.isleft == 1 "Ideal sum is not an ideal"
  return L
end

function *(x::Union{IntegerUnion, RingElem}, I::AssociativeAlgebraOrderIdeal)
  return _ideal_with_sidedness(order(I), x*lattice(I), I.isleft, I.isright)
end

function *(x::Union{IntegerUnion, RingElem}, O::AssociativeAlgebraOrder)
  return _ideal_with_sidedness(O, base_ring(O)(x)*lattice(O), 1, 1)
end

*(I::AssociativeAlgebraOrderIdeal, x::Union{IntegerUnion, RingElem}) = x*I

function *(x::AbstractAssociativeAlgebraElem, I::AssociativeAlgebraOrderIdeal)
  return _ideal_with_sidedness(order(I), x*lattice(I), 0, I.isright == 1 ? 1 : 0)
end

function *(I::AssociativeAlgebraOrderIdeal, x::AbstractAssociativeAlgebraElem)
  return _ideal_with_sidedness(order(I), lattice(I)*x, I.isleft == 1 ? 1 : 0, 0)
end

function *(x::AssociativeAlgebraOrderElem, I::AssociativeAlgebraOrderIdeal)
  @req parent(x) === order(I) "The element and ideal belong to different orders"
  return elem_in_algebra(x, copy = false)*I
end

function *(I::AssociativeAlgebraOrderIdeal, x::AssociativeAlgebraOrderElem)
  @req parent(x) === order(I) "The element and ideal belong to different orders"
  return I*elem_in_algebra(x, copy = false)
end

################################################################################
#
#  Printing
#
################################################################################

function show(io::IO, I::AssociativeAlgebraOrderIdeal)
  print(io, "Ideal with underlying ")
  show(io, lattice(I))
end

###

function quotient_algebra(O::AssociativeAlgebraOrder, I::AssociativeAlgebraOrderIdeal, p::RingElem)
  V, OtoV, RtoF = quotient_vector_space(_underlying_module(O), _module(lattice(I)), p)
  basislifted = O.(preimage.(OtoV, gens(V)))
  F = base_ring(V)
  d = dim(V)
  mtable = Array{elem_type(F), 3}(undef, d, d, d)
  for i in 1:d
    for j in 1:d
      mtable[i, j, :] = Generic._matrix(OtoV(elem_in_module(basislifted[i] * basislifted[j])))[1, :]
    end
  end
  A = structure_constant_algebra(F, mtable)
  OtoA = hom(O, A, RtoF,
             [A(Generic._matrix(OtoV(elem_in_module(x)))[1, :]) for x in basis(O)];
             preimage = x -> O(preimage(OtoV, V(coefficients(x)))))
  return A, OtoA
end

# Returns the twosided maximal ideals of O containing I, where p*O \subseteq I.
# If strict_containment == true and I is already prime, we return an empty array.
function _maximal_ideals(O::AssociativeAlgebraOrder, I::AssociativeAlgebraOrderIdeal, p::RingElem; strict_containment::Bool = false)
  A1, OtoA1 = quotient_algebra(O, I, p)
  @vtime :AlgAssOrd 1 lg = gens(A1)
  lM = dense_matrix_type(base_ring(A1))[ representation_matrix(lg[i]) for i = 1:length(lg) ]
  append!(lM, dense_matrix_type(base_ring(A1))[ representation_matrix(lg[i], :right) for i = 1:length(lg) ])
  M = Amodule(lM)
  ls = maximal_submodules(M)
  if strict_containment && isone(length(ls)) && iszero(nrows(ls[1]))
    ls = typeof(ls[1])[]
  end
  return typeof(I)[_from_submodules_to_ideals(M, O, I, x, A1, OtoA1) for x in ls ]
end

function _from_submodules_to_ideals(M::ModAlgAss, O::AssociativeAlgebraOrder, I::AssociativeAlgebraOrderIdeal, x::Union{FqMatrix, Zmodn_mat, Generic.Mat{EuclideanRingResidueFieldElem{ZZRingElem}}}, A1::StructureConstantAlgebra, OtoA1)
  @hassert :AlgAssOrd 1 begin r = rref(x)[1]; closure(x, M.action_of_gens) == sub(rref(x)[2], 1:r, 1:ncols(x)) end
  g = Vector{elem_type(O)}(undef, nrows(x))
  for i in 1:nrows(x)
    g[i] = preimage(OtoA1, elem_from_mat_row(A1, x, i))
  end
  #m = zero_matrix(ZZ, nrows(x), degree(O))
  #g = Vector{elem_type(algebra(O))}(undef, nrows(x))
  #for i = 1:nrows(x)
  #  el = OtoA1\(elem_from_mat_row(A1, x, i))
  #  for j = 1:degree(O)
  #    m[i, j] = coordinates(el, copy = false)[j]
  #  end
  #  g[i] = elem_in_algebra(elem_from_mat_row(O, m, i), copy = false)
  #end
  # m = m*basis_matrix(O, copy = false)
  # m = vcat(m, basis_matrix(I, copy = false))
  # m = sub(_hnf_integral(m, :lowerleft), nrows(x) + 1:nrows(m), 1:degree(O))
  # J = ideal(algebra(O), O, m; side=:twosided, M_in_hnf=true)
  J = ideal(O, lattice(algebra(O), base_ring(O), vcat(elem_in_algebra.(g), elem_in_algebra.(basis(I; copy = false)))); side = :twosided)
  if isdefined(I, :gens)
    append!(g, I.gens)
    J.gens = g
  else
    append!(g, basis(I, copy = false))
  end
  return J
end

is_prime(f::PolyRingElem{<:FieldElem}) = is_irreducible(f)

# This computes a basis matrix for \{ x \in A | bx \subseteq a \} if
# side == :left or \{ x \in A | xb \subseteq a \} if side == :right.
#
# TODO: split into _PID and _DD case
function _colon_raw(a::AssociativeAlgebraOrderIdeal, b::AssociativeAlgebraOrderIdeal, side::Symbol)
  # TODO: more checks
  @assert is_full_lattice(a) && is_full_lattice(b)
  A = algebra(a)
  @assert A === algebra(b)
  K = base_ring(A)
  d = dim(A)
  # TODO: are the bases correct?
  bb = elem_in_algebra.(basis(b, copy = false))
  B = inv(basis_matrix(lattice(a), copy = false)) # wrt basis of A
  M = zero_matrix(base_ring(A), d^2, d)
  for i = 1:d
    N = representation_matrix(bb[i], side)*B
    for s = 1:d
      for t = 1:d
        M[t + (i - 1)*d, s] = N[s, t]
      end
    end
  end
  M = sub(_hnf_integral(M, base_ring(a), :upperright), 1:d, 1:d)
  N = inv(transpose(M))
  return N
end

@doc raw"""
    ring_of_multipliers(a::AlgAssAbsOrdIdl) -> AlgAssAbsOrd

Given an ideal $a$, it returns the ring $(a : a)$.
"""
function ring_of_multipliers(a::AssociativeAlgebraOrderIdeal, action::Symbol = :left)
  M = _colon_raw(a, a, action)
  R = base_ring(a)
  return new_order(algebra(a), R, _hnf_integral(M, R))
end
