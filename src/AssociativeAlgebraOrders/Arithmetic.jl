function _check_parent(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  @req parent(x) === parent(y) "The elements have different parent orders"
  return nothing
end

function +(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  _check_parent(x, y)
  return AssociativeAlgebraOrderElem(parent(x), elem_in_lattice(x) + elem_in_lattice(y))
end

function -(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  _check_parent(x, y)
  return AssociativeAlgebraOrderElem(parent(x), elem_in_lattice(x) - elem_in_lattice(y))
end

-(x::AssociativeAlgebraOrderElem) = AssociativeAlgebraOrderElem(parent(x), -elem_in_lattice(x))

function *(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  _check_parent(x, y)
  a = elem_in_algebra(x; copy = false)*elem_in_algebra(y; copy = false)
  return parent(x)(a; check = false)
end

function *(a::Union{IntegerUnion, RingElem}, x::AssociativeAlgebraOrderElem)
  return AssociativeAlgebraOrderElem(parent(x), a*elem_in_lattice(x))
end

*(x::AssociativeAlgebraOrderElem, a::Union{IntegerUnion, RingElem}) = a*x

function is_invertible(x::AssociativeAlgebraOrderElem)
  iszero(parent(x)) && return true, zero(parent(x))
  flag, a = is_invertible(elem_in_algebra(x; copy = false))
  if !flag || !(a in parent(x))
    return false, x
  end
  return true, parent(x)(a; check = false)
end

is_unit(x::AssociativeAlgebraOrderElem) = first(is_invertible(x))

function inv(x::AssociativeAlgebraOrderElem)
  flag, y = is_invertible(x)
  @req flag "The element is not a unit of the order"
  return y
end

function ^(x::AssociativeAlgebraOrderElem, n::IntegerUnion)
  return parent(x)(elem_in_algebra(x; copy = false)^n; check = n < 0)
end

function divexact(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem;
                  side::Symbol, check::Bool = true)
  _check_parent(x, y)
  @req side === :left || side === :right "The side must be :left or :right"
  O = parent(x)
  f = multiplication_map(underlying_lattice(O), elem_in_lattice(y); side)
  return AssociativeAlgebraOrderElem(O, preimage(f, elem_in_lattice(x)))
end

divexact_left(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem; check::Bool = true) =
  divexact(x, y; side = :left, check)

divexact_right(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem; check::Bool = true) =
  divexact(x, y; side = :right, check)

function add!(z::AssociativeAlgebraOrderElem, x::AssociativeAlgebraOrderElem,
              y::AssociativeAlgebraOrderElem)
  z.elem_in_lattice = elem_in_lattice(x + y)
  return z
end

function mul!(z::AssociativeAlgebraOrderElem, x::AssociativeAlgebraOrderElem,
              y::AssociativeAlgebraOrderElem)
  z.elem_in_lattice = elem_in_lattice(x*y)
  return z
end

function mul!(z::AssociativeAlgebraOrderElem, a::Union{IntegerUnion, RingElem},
              x::AssociativeAlgebraOrderElem)
  z.elem_in_lattice = elem_in_lattice(a*x)
  return z
end

mul!(z::AssociativeAlgebraOrderElem, x::AssociativeAlgebraOrderElem,
     a::Union{IntegerUnion, RingElem}) = mul!(z, a, x)

function addmul!(z::AssociativeAlgebraOrderElem, x::AssociativeAlgebraOrderElem,
                 y::AssociativeAlgebraOrderElem)
  z.elem_in_lattice = elem_in_lattice(z + x*y)
  return z
end

function zero!(x::AssociativeAlgebraOrderElem)
  x.elem_in_lattice = zero(underlying_lattice(parent(x)))
  return x
end
