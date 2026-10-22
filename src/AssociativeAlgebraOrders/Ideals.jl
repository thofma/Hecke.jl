base_ring(I::AssociativeAlgebraOrderIdeal) = I.order
underlying_lattice(I::AssociativeAlgebraOrderIdeal) = I.lattice
underlying_module(I::AssociativeAlgebraOrderIdeal) =
  underlying_module(underlying_lattice(I))
algebra(I::AssociativeAlgebraOrderIdeal) = algebra(base_ring(I))

base_ring_type(::Type{AssociativeAlgebraOrderIdeal{O, L}}) where {O, L} = O
algebra_type(::Type{AssociativeAlgebraOrderIdeal{O, L}}) where {O, L} =
  algebra_type(O)
ideal_type(::Type{O}) where {O <: AssociativeAlgebraOrder} =
  AssociativeAlgebraOrderIdeal{O, _lattice_type(O)}
ideal_type(O::AssociativeAlgebraOrder) = ideal_type(typeof(O))

function _check_ideal_side(side::Symbol)
  @req side in (:left, :right, :twosided) "Invalid ideal side"
  return nothing
end

function _set_ideal_side!(I::AssociativeAlgebraOrderIdeal, side::Symbol)
  if side === :left || side === :twosided
    set_attribute!(I, :is_left_ideal, true)
  end
  if side === :right || side === :twosided
    set_attribute!(I, :is_right_ideal, true)
  end
  return I
end

@attr Bool function is_left_ideal(I::AssociativeAlgebraOrderIdeal)
  L = underlying_lattice(I)
  return issubset(underlying_lattice(base_ring(I))*L, L)
end

@attr Bool function is_right_ideal(I::AssociativeAlgebraOrderIdeal)
  L = underlying_lattice(I)
  return issubset(L*underlying_lattice(base_ring(I)), L)
end

function _test_ideal_sidedness(I::AssociativeAlgebraOrderIdeal, side::Symbol)
  _check_ideal_side(side)
  return (side === :right || is_left_ideal(I)) &&
         (side === :left || is_right_ideal(I))
end

@doc raw"""
    ideal(O::AssociativeAlgebraOrder, L::AssociativeAlgebraLattice;
          side, check = true)

Return the integral ideal represented by `L`, with `side` equal to `:left`,
`:right` or `:twosided`. The lattice must be contained in `O`, including when
`check = false`; that keyword only skips sidedness verification. The lattice
is shared with the ideal and must not be modified independently.
"""
function ideal(O::AssociativeAlgebraOrder, L::AssociativeAlgebraLattice;
               side::Symbol, check::Bool = true)
  return AssociativeAlgebraOrderIdeal(O, L; side, check)
end

function _ideal_generator(O::AssociativeAlgebraOrder,
                          x::AbstractAssociativeAlgebraElem)
  @req x in O "The generator is not contained in the order"
  return x
end

function _ideal_generator(O::AssociativeAlgebraOrder,
                          x::AssociativeAlgebraOrderElem)
  return _ideal_generator(O, elem_in_algebra(x; copy = false))
end

function _ideal_generator(O::AssociativeAlgebraOrder,
                          x::Union{IntegerUnion, RingElem})
  return elem_in_algebra(O(x); copy = false)
end

function _ideal_from_generators(O::AssociativeAlgebraOrder, generators;
                                side::Symbol, check::Bool = true)
  _check_ideal_side(side)
  A = algebra(O)
  v = elem_type(A)[_ideal_generator(O, x) for x in generators]
  N = lattice(A, base_ring(O), v)
  Lo = underlying_lattice(O)
  L = if side === :left
    Lo*N
  elseif side === :right
    N*Lo
  else
    Lo*N*Lo
  end
  return ideal(O, L; side, check)
end

@doc raw"""
    ideal(O::AssociativeAlgebraOrder, generators::AbstractVector;
          side, check = true)
    ideal(O::AssociativeAlgebraOrder, x; side, check = true)

Generate an integral left, right or two-sided ideal of `O`. Every generator
must belong to `O`, including when `check = false`. Generators may be order
elements, ambient algebra elements, or scalars coercible into `O`.
"""
ideal(O::AssociativeAlgebraOrder, generators::AbstractVector; kw...) =
  _ideal_from_generators(O, generators; kw...)

# Resolve AbstractAlgebra's typed-vector ideal constructor.
ideal(O::AssociativeAlgebraOrder,
      generators::AbstractVector{<:NCRingElement}; kw...) =
  _ideal_from_generators(O, generators; kw...)

function ideal(O::AssociativeAlgebraOrder,
               x::Union{AbstractAssociativeAlgebraElem,
                        AssociativeAlgebraOrderElem, IntegerUnion, RingElem};
               side::Symbol, check::Bool = true)
  return ideal(O, [x]; side, check)
end

left_ideal(O::AssociativeAlgebraOrder, x...; kw...) =
  ideal(O, x...; side = :left, kw...)
right_ideal(O::AssociativeAlgebraOrder, x...; kw...) =
  ideal(O, x...; side = :right, kw...)
twosided_ideal(O::AssociativeAlgebraOrder, x...; kw...) =
  ideal(O, x...; side = :twosided, kw...)

*(O::AssociativeAlgebraOrder,
  x::Union{AbstractAssociativeAlgebraElem, AssociativeAlgebraOrderElem,
           IntegerUnion, RingElem}) = left_ideal(O, x)
*(x::Union{AbstractAssociativeAlgebraElem, AssociativeAlgebraOrderElem,
           IntegerUnion, RingElem},
  O::AssociativeAlgebraOrder) = right_ideal(O, x)

in(x::AbstractAssociativeAlgebraElem, I::AssociativeAlgebraOrderIdeal) =
  x in underlying_lattice(I)
in(x::AssociativeAlgebraOrderElem, I::AssociativeAlgebraOrderIdeal) =
  elem_in_algebra(x; copy = false) in underlying_lattice(I)

rank(I::AssociativeAlgebraOrderIdeal) = rank(underlying_lattice(I))
ambient_rank(I::AssociativeAlgebraOrderIdeal) =
  ambient_rank(underlying_lattice(I))
is_full_lattice(I::AssociativeAlgebraOrderIdeal) =
  is_full_lattice(underlying_lattice(I))
is_full_rank(I::AssociativeAlgebraOrderIdeal) = is_full_lattice(I)
iszero(I::AssociativeAlgebraOrderIdeal) = iszero(underlying_lattice(I))
isone(I::AssociativeAlgebraOrderIdeal) =
  underlying_lattice(I) == underlying_lattice(base_ring(I))

basis(I::AssociativeAlgebraOrderIdeal; copy::Bool = true) =
  basis(underlying_lattice(I); copy)
pseudo_basis(I::AssociativeAlgebraOrderIdeal; copy::Bool = true) =
  pseudo_basis(underlying_lattice(I); copy)
basis_matrix(I::AssociativeAlgebraOrderIdeal; copy::Bool = true) =
  basis_matrix(underlying_lattice(I); copy)

is_compatible(I::AssociativeAlgebraOrderIdeal,
              J::AssociativeAlgebraOrderIdeal) = base_ring(I) === base_ring(J)

function _check_ideal_parents(I::AssociativeAlgebraOrderIdeal,
                              J::AssociativeAlgebraOrderIdeal)
  @req is_compatible(I, J) "The ideals have different base orders"
  return nothing
end

function ==(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal)
  return is_compatible(I, J) && underlying_lattice(I) == underlying_lattice(J)
end

function hash(I::AssociativeAlgebraOrderIdeal, h::UInt)
  return hash(underlying_lattice(I), hash(objectid(base_ring(I)), h))
end

function issubset(I::AssociativeAlgebraOrderIdeal,
                  J::AssociativeAlgebraOrderIdeal)
  _check_ideal_parents(I, J)
  return issubset(underlying_lattice(I), underlying_lattice(J))
end

function module_index(I::AssociativeAlgebraOrderIdeal,
                      J::AssociativeAlgebraOrderIdeal; check::Bool = true)
  _check_ideal_parents(I, J)
  return module_index(underlying_lattice(I), underlying_lattice(J); check)
end

function _ideal_result(O::AssociativeAlgebraOrder,
                       L::AssociativeAlgebraLattice, left::Bool, right::Bool)
  if !left && !right
    Lo = underlying_lattice(O)
    left = issubset(Lo*L, L)
    right = issubset(L*Lo, L)
    @req left || right "The result is neither a left nor a right ideal"
  end
  side = left ? (right ? :twosided : :left) : :right
  return ideal(O, L; side, check = false)
end

function _ideal_result(I::AssociativeAlgebraOrderIdeal,
                       J::AssociativeAlgebraOrderIdeal,
                       L::AssociativeAlgebraLattice)
  left = get_attribute(I, :is_left_ideal, false) &&
         get_attribute(J, :is_left_ideal, false)
  right = get_attribute(I, :is_right_ideal, false) &&
          get_attribute(J, :is_right_ideal, false)
  return _ideal_result(base_ring(I), L, left, right)
end

function _ideal_result(I::AssociativeAlgebraOrderIdeal,
                       L::AssociativeAlgebraLattice)
  return _ideal_result(base_ring(I), L,
                       get_attribute(I, :is_left_ideal, false),
                       get_attribute(I, :is_right_ideal, false))
end

function +(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal)
  _check_ideal_parents(I, J)
  return _ideal_result(I, J, underlying_lattice(I) + underlying_lattice(J))
end

function intersect(I::AssociativeAlgebraOrderIdeal,
                   J::AssociativeAlgebraOrderIdeal)
  _check_ideal_parents(I, J)
  return _ideal_result(I, J, intersect(underlying_lattice(I),
                                      underlying_lattice(J)))
end

zero(I::AssociativeAlgebraOrderIdeal) =
  twosided_ideal(base_ring(I), zero_lattice(algebra(I),
                                          base_ring(base_ring(I)));
                 check = false)
one(I::AssociativeAlgebraOrderIdeal) =
  twosided_ideal(base_ring(I), underlying_lattice(base_ring(I));
                 check = false)
copy(I::AssociativeAlgebraOrderIdeal) = _ideal_result(I, underlying_lattice(I))

function *(I::AssociativeAlgebraOrderIdeal, J::AssociativeAlgebraOrderIdeal)
  _check_ideal_parents(I, J)
  L = underlying_lattice(I)*underlying_lattice(J)
  return _ideal_result(base_ring(I), L,
                       get_attribute(I, :is_left_ideal, false),
                       get_attribute(J, :is_right_ideal, false))
end

function ^(I::AssociativeAlgebraOrderIdeal, n::IntegerUnion)
  @req n >= 0 "The exponent must be nonnegative"
  return Base.power_by_squaring(I, n isa Integer ? n : BigInt(n))
end

Base.literal_pow(::typeof(^), I::AssociativeAlgebraOrderIdeal,
                 ::Val{n}) where {n} = I^n

function *(r::Union{IntegerUnion, RingElem}, I::AssociativeAlgebraOrderIdeal)
  R = base_ring(base_ring(I))
  if !(r isa IntegerUnion)
    @req parent(r) === R "The scalar must belong to the coefficient ring"
  end
  return _ideal_result(I, R(r)*underlying_lattice(I))
end

*(I::AssociativeAlgebraOrderIdeal, r::Union{IntegerUnion, RingElem}) = r*I

function *(I::AssociativeAlgebraOrderIdeal,
           x::Union{AssociativeAlgebraOrderElem,
                    AbstractAssociativeAlgebraElem})
  a = _ideal_generator(base_ring(I), x)
  return _ideal_result(base_ring(I), underlying_lattice(I)*a,
                       get_attribute(I, :is_left_ideal, false), false)
end

function *(x::Union{AssociativeAlgebraOrderElem,
                    AbstractAssociativeAlgebraElem},
           I::AssociativeAlgebraOrderIdeal)
  a = _ideal_generator(base_ring(I), x)
  return _ideal_result(base_ring(I), a*underlying_lattice(I),
                       false, get_attribute(I, :is_right_ideal, false))
end

left_order(I::AssociativeAlgebraOrderIdeal) =
  left_order(underlying_lattice(I))
right_order(I::AssociativeAlgebraOrderIdeal) =
  right_order(underlying_lattice(I))

function module_index(I::AssociativeAlgebraOrderIdeal,
                      O::AssociativeAlgebraOrder; check::Bool = true)
  @req base_ring(I) === O "The ideal has a different base order"
  return module_index(underlying_lattice(I), underlying_lattice(O); check)
end

RandomExtensions.maketype(I::AssociativeAlgebraOrderIdeal, _) =
  elem_type(algebra(I))

function RandomExtensions.make(I::AssociativeAlgebraOrderIdeal, B::Int)
  @req B >= 0 "The coefficient bound must be nonnegative"
  return RandomExtensions.Make(I, make(ZZ, -B:B))
end

function RandomExtensions.make(I::AssociativeAlgebraOrderIdeal, args...)
  return RandomExtensions.Make(I, make(base_ring(base_ring(I)), args...))
end

function rand(rng::AbstractRNG,
              sp::SamplerTrivial{<:Make2{<:NCRingElem,
                                        <:AssociativeAlgebraOrderIdeal}})
  I, coefficients = sp[][1:end]
  R = base_ring(base_ring(I))
  c = elem_type(R)[R(rand(rng, coefficients)) for _ in 1:rank(I)]
  return elem_in_algebra(underlying_lattice(I)(c; check = false))
end

@doc raw"""
    rand([rng], I::AssociativeAlgebraOrderIdeal, B::Int)
    rand([rng], I::AssociativeAlgebraOrderIdeal, r::AbstractUnitRange, args...)

Return an ambient algebra element in `I`. An integer bound `B` samples integer
basis coefficients in `-B:B`. Other arguments specify a sampler for the
coefficient ring, as in `rand(rng, base_ring(base_ring(I)), args...)`.
"""
rand(I::AssociativeAlgebraOrderIdeal, B::Int) = rand(GLOBAL_RNG, I, B)
rand(rng::AbstractRNG, I::AssociativeAlgebraOrderIdeal, B::Int) =
  rand(rng, make(I, B))
rand(I::AssociativeAlgebraOrderIdeal, r::AbstractUnitRange, args...) =
  rand(GLOBAL_RNG, I, r, args...)
rand(rng::AbstractRNG, I::AssociativeAlgebraOrderIdeal,
     r::AbstractUnitRange, args...) = rand(rng, make(I, r, args...))

@doc raw"""
    mod(x::AssociativeAlgebraOrderElem, I::AssociativeAlgebraOrderIdeal)
    mod!(x::AssociativeAlgebraOrderElem, I::AssociativeAlgebraOrderIdeal)

Return a representative in `base_ring(I)` of the additive coset `x + I`, using
normal-form reduction in the underlying lattice. Require
`parent(x) === base_ring(I)`. The ideal may have either sidedness or smaller
rank. The mutating form replaces `x`.
"""
function mod(x::AssociativeAlgebraOrderElem, I::AssociativeAlgebraOrderIdeal)
  @req parent(x) === base_ring(I) "The element has a different parent order"
  y = mod(elem_in_lattice(x), underlying_lattice(I))
  return AssociativeAlgebraOrderElem(parent(x), y)
end

function mod!(x::AssociativeAlgebraOrderElem, I::AssociativeAlgebraOrderIdeal)
  x.elem_in_lattice = elem_in_lattice(mod(x, I))
  return x
end

@doc raw"""
    contract(I::AssociativeAlgebraOrderIdeal, R::Ring)
    intersect(I::AssociativeAlgebraOrderIdeal, R::Ring)

For `R === base_ring(base_ring(I))`, return the ideal of scalars `r` in `R`
whose images `r*1` belong to `I`, using the inverse image under the scalar
inclusion. For a compatible suborder `OO`, use `contract(I, OO)`.
"""
function contract(I::AssociativeAlgebraOrderIdeal, R::Ring)
  @req R === base_ring(base_ring(I)) "Not the coefficient ring of the order"
  iszero(base_ring(I)) && return ideal(R, one(R))
  O = base_ring(I)
  K = base_ring(algebra(O))
  S = embedded_module(R, K, identity_matrix(K, 1); is_basis_matrix = true)
  B = matrix(K, 1, degree(O), ambient_coordinates(one(O); copy = false))
  f = _hom_from_ambient_matrix(S, underlying_module(O), B)
  return ideal(R, preimage(f, underlying_module(I)))
end

intersect(I::AssociativeAlgebraOrderIdeal, R::Ring) = contract(I, R)
intersect(R::Ring, I::AssociativeAlgebraOrderIdeal) = contract(I, R)
minimum(I::AssociativeAlgebraOrderIdeal{<:AssociativeAlgebraOrder{ZZRing}}) =
  gen(contract(I, ZZ))

function is_coprime(I::AssociativeAlgebraOrderIdeal,
                    J::AssociativeAlgebraOrderIdeal)
  _check_ideal_parents(I, J)
  return underlying_lattice(I) + underlying_lattice(J) ==
         underlying_lattice(base_ring(I))
end

@doc raw"""
    idempotents(I::AssociativeAlgebraOrderIdeal,
                J::AssociativeAlgebraOrderIdeal)

Require `I + J` to be the base order `O`. Return order elements `a` in `I` and
`b` in `J` such that `a + b == one(O)`. When both ideals are two-sided, these
give complementary idempotents modulo their intersection.
"""
function idempotents(I::AssociativeAlgebraOrderIdeal,
                     J::AssociativeAlgebraOrderIdeal)
  @req is_coprime(I, J) "The ideals are not coprime"
  O = base_ring(I)
  f, pI, _ = addition_map(underlying_module(I), underlying_module(J),
                         underlying_module(O))
  z = preimage(f, elem_in_module(one(O)))
  a = AssociativeAlgebraLatticeElem(underlying_lattice(I), pI(z))
  x = O(a; check = false)
  return x, one(O) - x
end

@doc raw"""
    extend(I::AssociativeAlgebraOrderIdeal, OO::AssociativeAlgebraOrder;
           side = :twosided)

Require `base_ring(I)` to be contained in the compatible order `OO`. Return
`OO*I`, `I*OO`, or `OO*I*OO` according to `side`.
"""
function extend(I::AssociativeAlgebraOrderIdeal,
                OO::AssociativeAlgebraOrder; side::Symbol = :twosided)
  _check_ideal_side(side)
  @req issubset(base_ring(I), OO) "The base order is not contained in OO"
  L = underlying_lattice(I)
  Lo = underlying_lattice(OO)
  side !== :right && (L = Lo*L)
  side !== :left && (L = L*Lo)
  return ideal(OO, L; side, check = false)
end

*(OO::AssociativeAlgebraOrder, I::AssociativeAlgebraOrderIdeal) =
  extend(I, OO; side = :left)
*(I::AssociativeAlgebraOrderIdeal, OO::AssociativeAlgebraOrder) =
  extend(I, OO; side = :right)

@doc raw"""
    contract(I::AssociativeAlgebraOrderIdeal, OO::AssociativeAlgebraOrder)

Require `OO` to be contained in the compatible order `base_ring(I)`. Return
the inverse image of `I` under the inclusion of `OO`, with base order `OO`.
This is `I` intersected with `OO`; known left and right sidedness is retained.
"""
function contract(I::AssociativeAlgebraOrderIdeal,
                  OO::AssociativeAlgebraOrder)
  @req issubset(OO, base_ring(I)) "OO is not contained in the base order"
  f = underlying_map(inclusion_map(underlying_lattice(OO),
                                  underlying_lattice(base_ring(I))))
  M = preimage(f, underlying_module(I))
  L = lattice(algebra(OO), base_ring(OO), M)
  return _ideal_result(OO, L,
                       get_attribute(I, :is_left_ideal, false),
                       get_attribute(I, :is_right_ideal, false))
end

intersect(I::AssociativeAlgebraOrderIdeal, OO::AssociativeAlgebraOrder) =
  contract(I, OO)
intersect(OO::AssociativeAlgebraOrder, I::AssociativeAlgebraOrderIdeal) =
  contract(I, OO)

@doc raw"""
    invmod(x::AssociativeAlgebraOrderElem, I::AssociativeAlgebraOrderIdeal)

Return a reduced representative of the inverse of `x` modulo `I`. Require
`parent(x) === base_ring(I)` and `I` to be two-sided. Both inverse identities
must hold modulo `I`; `x` need not be a unit of its parent order.
Throw an error if no inverse exists.
"""
function invmod(x::AssociativeAlgebraOrderElem,
                I::AssociativeAlgebraOrderIdeal)
  O = parent(x)
  @req O === base_ring(I) "The element has a different parent order"
  @req is_left_ideal(I) && is_right_ideal(I) "The ideal must be two-sided"
  L = underlying_lattice(O)
  f = underlying_map(multiplication_map(L, elem_in_lattice(x); side = :left))
  g = underlying_map(inclusion_map(underlying_lattice(I), L))
  h, p, _ = addition_map(f, g)
  z = preimage(h, elem_in_module(one(O)))
  y = AssociativeAlgebraOrderElem(O, AssociativeAlgebraLatticeElem(L, p(z)))
  @req x*y - one(O) in I && y*x - one(O) in I "Not invertible modulo I"
  return mod(y, I)
end

@doc raw"""
    powermod(x::AssociativeAlgebraOrderElem, n::IntegerUnion,
             I::AssociativeAlgebraOrderIdeal)

Return a representative of `x^n` modulo the two-sided ideal `I`. Require
`parent(x) === base_ring(I)`. Negative exponents use `invmod(x, I)` and do
not require an inverse in the order itself.
"""
function powermod(x::AssociativeAlgebraOrderElem, n::IntegerUnion,
                  I::AssociativeAlgebraOrderIdeal)
  O = parent(x)
  @req O === base_ring(I) "The element has a different parent order"
  @req is_left_ideal(I) && is_right_ideal(I) "The ideal must be two-sided"
  if n < 0
    return powermod(invmod(x, I), n isa Integer ? -widen(n) : -n, I)
  end
  y = mod(one(O), I)
  a = mod(x, I)
  while !iszero(n)
    isodd(n) && (y = mod(y*a, I))
    n = div(n, 2)
    !iszero(n) && (a = mod(a*a, I))
  end
  return y
end

function show(io::IO, I::AssociativeAlgebraOrderIdeal)
  print(io, "Integral ideal of ")
  show(io, base_ring(I))
end
