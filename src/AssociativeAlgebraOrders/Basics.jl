underlying_lattice(O::AssociativeAlgebraOrder) = O.lattice

underlying_module(O::AssociativeAlgebraOrder) = underlying_module(underlying_lattice(O))
algebra(O::AssociativeAlgebraOrder) = O.algebra
base_ring(O::AssociativeAlgebraOrder) = base_ring(underlying_lattice(O))
algebra_type(::Type{AssociativeAlgebraOrder{R, K, A}}) where {R, K, A} = A
base_ring_type(::Type{AssociativeAlgebraOrder{R, K, A}}) where {R, K, A} = R
order_type(::Type{AssociativeAlgebraLattice{A, R}}) where {A, R} = AssociativeAlgebraOrder{R, _ring_type(R), A}

_lattice_type(::Type{AssociativeAlgebraOrder{R, K, A}}) where {R, K, A} = AssociativeAlgebraLattice{A, R}

function defines_order(L::AssociativeAlgebraLattice)::Bool
  is_full_lattice(L) || return false
  A = algebra(L)
  has_one(A) || return false
  one(A) in L || return false
  # TODO: Adapt the basis-product checks from AlgAssAbsOrd/Order.jl to
  # avoid constructing the entire product lattice.
  return issubset(L*L, L)
end

order(L::AssociativeAlgebraLattice; check::Bool = true) = AssociativeAlgebraOrder(L; check)

function order(A::AbstractAssociativeAlgebra, R::Ring,
               data::Union{MatElem, EmbeddedModule, Vector};
               check::Bool = true, kwargs...)
  return order(lattice(A, R, data; kwargs...); check)
end

rank(O::AssociativeAlgebraOrder) = rank(underlying_lattice(O))
ambient_rank(O::AssociativeAlgebraOrder) = ambient_rank(underlying_lattice(O))
is_full_lattice(O::AssociativeAlgebraOrder) = is_full_lattice(underlying_lattice(O))
is_full_rank(O::AssociativeAlgebraOrder) = is_full_lattice(O)
degree(O::AssociativeAlgebraOrder) = dim(algebra(O))
iszero(O::AssociativeAlgebraOrder) = iszero(underlying_lattice(O))
characteristic(O::AssociativeAlgebraOrder) = characteristic(base_ring(algebra(O)))
is_commutative(O::AssociativeAlgebraOrder) = is_commutative(algebra(O))

function basis_matrix(O::AssociativeAlgebraOrder; copy::Bool = true)
  return basis_matrix(underlying_lattice(O); copy)
end

function basis_matrix_inverse(O::AssociativeAlgebraOrder; copy::Bool = true)
  B = basis_matrix_inverse(underlying_module(O))
  return copy ? deepcopy(B) : B
end

@attr Vector{elem_type(O)} function _basis(O::AssociativeAlgebraOrder)
  return [O(b; check = false) for b in basis(underlying_lattice(O); copy = false)]
end

function basis(O::AssociativeAlgebraOrder; copy::Bool = true)
  B = _basis(O)
  return copy ? Base.copy(B) : B
end

basis_alg(O::AssociativeAlgebraOrder; copy::Bool = true) = basis(underlying_lattice(O); copy)

function basis(O::AssociativeAlgebraOrder, A::AbstractAssociativeAlgebra; copy::Bool = true)
  @req A === algebra(O) "The algebras do not agree"
  return basis_alg(O; copy)
end

pseudo_basis(O::AssociativeAlgebraOrder; copy::Bool = true) = pseudo_basis(underlying_lattice(O); copy)

function in(x::Union{AbstractAssociativeAlgebraElem, PseudoElement, AssociativeAlgebraLatticeElem},
            O::AssociativeAlgebraOrder)
  return x in underlying_lattice(O)
end

is_compatible(O::AssociativeAlgebraOrder, P::AssociativeAlgebraOrder) =
  is_compatible(underlying_lattice(O), underlying_lattice(P))

issubset(O::AssociativeAlgebraOrder, P::AssociativeAlgebraOrder) =
  issubset(underlying_lattice(O), underlying_lattice(P))

module_index(O::AssociativeAlgebraOrder, P::AssociativeAlgebraOrder; check = true) =
  module_index(underlying_lattice(O), underlying_lattice(P); check)

==(O::AssociativeAlgebraOrder, P::AssociativeAlgebraOrder) =
  underlying_lattice(O) == underlying_lattice(P)

hash(O::AssociativeAlgebraOrder, h::UInt) = hash(underlying_lattice(O), h)

function intersect(O::AssociativeAlgebraOrder, P::AssociativeAlgebraOrder)
  return order(intersect(underlying_lattice(O), underlying_lattice(P)); check = false)
end

function show(io::IO, O::AssociativeAlgebraOrder)
  print(io, "Order over ")
  show(io, base_ring(O))
  print(io, " in ")
  show(io, algebra(O))
end
