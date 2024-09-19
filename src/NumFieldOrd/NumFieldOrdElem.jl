################################################################################
#
#  Parent
#
################################################################################

@doc raw"""
    parent(a::NumFieldOrderElem) -> NumFieldOrder

Returns the order of which $a$ is an element.
"""
parent(a::NumFieldOrderElem) = a.parent::parent_type(a)

################################################################################
#
#  Element in number field
#
################################################################################

@doc raw"""
    elem_in_nf(a::NumFieldOrderElem) -> NumFieldElem

Returns the element $a$ considered as an element of the ambient number field.
"""
function elem_in_nf(a::NumFieldOrderElem; copy::Bool = true)
  if isdefined(a, :elem_in_nf)
    if copy
      return deepcopy(a.elem_in_nf)
    else
      return a.elem_in_nf
    end
  end
  error("Not a valid order element")
end

_elem_in_algebra(a::NumFieldOrderElem; copy::Bool = true) = elem_in_nf(a, copy = copy)

################################################################################
#
#  Special elements
#
################################################################################

zero(O::NumFieldOrder) = O(ZZRingElem(0))

one(O::NumFieldOrder) = O(ZZRingElem(1))

zero(a::NumFieldOrderElem) = parent(a)(0)

one(a::NumFieldOrderElem) = one(parent(a))

function zero!(a::NumFieldOrderElem)
  zero!(a.elem_in_nf)
  a.has_coord = false
  return a
end

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::NumFieldOrderElem) = isone(a.elem_in_nf)

iszero(a::NumFieldOrderElem) = iszero(a.elem_in_nf)

################################################################################
#
#  Unary operations
#
################################################################################

function -(a::NumFieldOrderElem)
  b = parent(a)()
  b.elem_in_nf = - a.elem_in_nf
  if a.has_coord
    b.coordinates = map(x -> -x, a.coordinates)
    b.has_coord = true
  end
  return b
end

###############################################################################
#
#  Binary operations
#
###############################################################################

function *(x::T, y::T) where T <: NumFieldOrderElem
  check_parent(x, y)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf*y.elem_in_nf
  return z
end

function +(x::T, y::T) where T <: NumFieldOrderElem
  check_parent(x, y)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  if x.has_coord && y.has_coord
    z.coordinates =
      [ x.coordinates[i] + y.coordinates[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

function -(x::T, y::T) where T <: NumFieldOrderElem
  check_parent(x, y)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y.elem_in_nf
  if x.has_coord && y.has_coord
    z.coordinates = [ x.coordinates[i] - y.coordinates[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

function divexact(x::T, y::T; check::Bool = true) where T <: NumFieldOrderElem
  check_parent(x, y)
  a = divexact(x.elem_in_nf, y.elem_in_nf)
  if check && !(in(a, parent(x)))
    throw(ArgumentError("Quotient not an element of the order."))
  end
  z = parent(x)()
  z.elem_in_nf = a
  return z
end

function //(x::T, y::T) where {T <: NumFieldOrderElem}
  return divexact(x.elem_in_nf, y.elem_in_nf)
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

for T in [Integer, ZZRingElem]
  @eval begin
    function *(a::NumFieldOrderElem, b::$T)
      c = parent(a)()
      c.elem_in_nf = a.elem_in_nf*b
      if a.has_coord
        c.coordinates = map(x -> b*x, a.coordinates)
        c.has_coord = true
      end
      return c
    end

    *(a::$T, b::NumFieldOrderElem) = b*a

    function +(x::NumFieldOrderElem, y::$T)
      z = parent(x)()
      z.elem_in_nf = x.elem_in_nf + y
      return z
    end

    +(x::$T, y::NumFieldOrderElem) = y + x

    function -(x::NumFieldOrderElem, y::$T)
      z = parent(x)()
      z.elem_in_nf = x.elem_in_nf - y
      return z
    end

    function -(x::$T, y::NumFieldOrderElem)
      z = parent(y)()
      z.elem_in_nf = x - y.elem_in_nf
      return z
    end

    function divexact(a::NumFieldOrderElem, b::$T; check::Bool = true)
      t = divexact(a.elem_in_nf, b)
      if check && !(in(t, parent(a)))
        throw(ArgumentError("Quotient not an element of the order."))
      end
      c  = parent(a)(t)
      return c
    end

    function //(a::NumFieldOrderElem, b::$T)
      return divexact(a.elem_in_nf, b)
    end
  end
end

################################################################################
#
#  Exponentiation
#
################################################################################

# TODO: In the following parent(x)(z) does also a deepcopy, which is not
# necessary (as ^y should produce something mutable)
for T in [Integer, ZZRingElem]
  @eval begin
    function ^(x::NumFieldOrderElem, y::$T)
      if y >= 0
        return parent(x)(elem_in_nf(x)^y, false)
      else
        z = elem_in_nf(x)^y
        return parent(x)(z)
      end
    end
  end
end

################################################################################
#
#  Unsafe operations
#
################################################################################

@inline function add!(z::AbsNumFieldOrderElem, x::AbsNumFieldOrderElem, y::AbsNumFieldOrderElem)
  add!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

@inline function sub!(z::AbsNumFieldOrderElem, x::AbsNumFieldOrderElem, y::AbsNumFieldOrderElem)
  sub!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

@inline function mul!(z::AbsNumFieldOrderElem, x::AbsNumFieldOrderElem, y::AbsNumFieldOrderElem)
  mul!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

################################################################################
#
#  Unsafe ad hoc operations
#
################################################################################

# ad hoc
for T in [Integer, ZZRingElem]
  @eval begin
    @inline function mul!(z::NumFieldOrderElem, x::NumFieldOrderElem, y::$T)
      z.elem_in_nf = mul!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    mul!(z::NumFieldOrderElem, x::$T, y::NumFieldOrderElem) = mul!(z, y, x)
  end
end

for T in [Integer, ZZRingElem]
  @eval begin
    @inline function add!(z::NumFieldOrderElem, x::NumFieldOrderElem, y::$T)
      z.elem_in_nf = add!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    add!(z::NumFieldOrderElem, x::$T, y::NumFieldOrderElem) = add!(z, y, x)
  end
end

for T in [Integer, ZZRingElem]
  @eval begin
    @inline function sub!(z::NumFieldOrderElem, x::NumFieldOrderElem, y::$T)
      z.elem_in_nf = sub!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    sub!(z::NumFieldOrderElem, x::$T, y::NumFieldOrderElem) = add!(z, y, x)
  end
end

################################################################################
#
#  Base cases for dot product of vectors
#
################################################################################

dot(x::NumFieldOrderElem, y::Integer) = x * y

dot(x::Integer, y::NumFieldOrderElem) = y * x

dot(x::NumFieldOrderElem, y::ZZRingElem) = x * y

dot(x::ZZRingElem, y::NumFieldOrderElem) = y * x


################################################################################
#
#  Trace
#
################################################################################

@doc raw"""
    tr(a::NumFieldOrderElem)

Returns the trace of $a$ as an element of the base ring.
"""
function tr(a::NumFieldOrderElem)
  OK = parent(a)
  return base_ring(OK)(tr(a.elem_in_nf))
end

@doc raw"""
    absolute_tr(a::NumFieldOrderElem) -> ZZRingElem

Return the absolute trace as an integer.
"""
absolute_tr(a::AbsNumFieldOrderElem) = tr(a)
absolute_tr(a::RelNumFieldOrderElem) = absolute_tr(tr(a))

################################################################################
#
#  Norm
#
################################################################################

@doc raw"""
    norm(a::NumFieldOrderElem)

Returns the norm of $a$ as an element in the base ring.
"""
function norm(a::NumFieldOrderElem)
  OK = parent(a)
  return base_ring(OK)(norm(a.elem_in_nf))
end

@doc raw"""
    absolute_norm(a::NumFieldOrderElem) -> ZZRingElem

Return the absolute norm as an integer.
"""
absolute_norm(a::AbsNumFieldOrderElem) = norm(a)
absolute_norm(a::RelNumFieldOrderElem) = absolute_norm(norm(a))

################################################################################
#
#  Discriminant
#
################################################################################

@doc raw"""
    discriminant(B::Vector{NumFieldOrderElem})

Returns the discriminant of the family $B$ of algebraic numbers,
i.e. $det((tr(B[i]*B[j]))_{i, j})^2$.
"""
function discriminant(B::Vector{T}) where T <: NumFieldOrderElem
  O = parent(B[1])
  n = degree(O)
  length(B) == 0 && error("Number of elements must be non-zero")
  length(B) != n && error("Number of elements must be $(n)")
  A = zero_matrix(base_ring(O), n, n)
  for i in 1:n
    el = tr(B[i]^2)
    A[i, i] = el
    for j in 1:n
      el = tr(B[i] * B[j])
      A[i, j] = el
      A[j, i] = el
    end
  end
  return det(A)
end

################################################################################
#
#  Hashing
#
################################################################################

Base.hash(x::NumFieldOrderElem, h::UInt) = Base.hash(x.elem_in_nf, h)

################################################################################
#
#  Equality
#
################################################################################

@doc raw"""
    ==(x::NumFieldOrderElem, y::NumFieldOrderElem) -> Bool

Returns whether $x$ and $y$ are equal.
"""
==(x::NumFieldOrderElem, y::NumFieldOrderElem) = parent(x) === parent(y) &&
                                            x.elem_in_nf == y.elem_in_nf

################################################################################
#
#  Minkowski embedding
#
################################################################################

@doc raw"""
    minkowski_map(a::NumFieldOrderElem, abs_tol::Int) -> Vector{ArbFieldElem}

Returns the image of $a$ under the Minkowski embedding.
Every entry of the array returned is of type `ArbFieldElem` with radius less then
`2^-abs_tol`.
"""
function minkowski_map(a::NumFieldOrderElem, abs_tol::Int = 32)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return minkowski_map(a.elem_in_nf, abs_tol)
end

################################################################################
#
#  Conjugates
#
################################################################################

@doc raw"""
    conjugates_arb(x::NumFieldOrderElem, abs_tol::Int) -> Vector{AcbFieldElem}

Compute the conjugates of $x$ as elements of type `AcbFieldElem`.
Recall that we order the complex conjugates
$\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
$\sigma_{i}(x) = \overline{\sigma_{i + s}(x)}$ for $r + 2 \leq i \leq r + s$.

Every entry $y$ of the array returned satisfies `radius(real(y)) < 2^-abs_tol`,
`radius(imag(y)) < 2^-abs_tol` respectively.
"""
function conjugates_arb(x::NumFieldOrderElem, abs_tol::Int = 32)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return conjugates_arb(x.elem_in_nf, abs_tol)
end

@doc raw"""
    conjugates_arb_log(x::NumFieldOrderElem, abs_tol::Int) -> Vector{ArbFieldElem}

Returns the elements
$(\log(\lvert \sigma_1(x) \rvert),\dotsc,\log(\lvert\sigma_r(x) \rvert),
\dotsc,2\log(\lvert \sigma_{r+1}(x) \rvert),\dotsc,
2\log(\lvert \sigma_{r+s}(x)\rvert))$ as elements of type `ArbFieldElem` radius
less then `2^-abs_tol`.
"""
function conjugates_arb_log(x::NumFieldOrderElem, abs_tol::Int = 32)
  return conjugates_arb_log(x.elem_in_nf, abs_tol)
end

################################################################################
#
#  T2
#
################################################################################

@doc raw"""
    t2(x::NumFieldOrderElem, abs_tol::Int = 32) -> ArbFieldElem

Return the $T_2$-norm of $x$. The radius of the result will be less than
`2^-abs_tol`.
"""
function t2(x::NumFieldOrderElem, abs_tol::Int = 32)
  return t2(x.elem_in_nf, abs_tol)
end

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule(::Type{S}, ::Type{U}) where {S <: NumFieldOrderElem, U <: Integer} = S

Nemo.promote_rule(::Type{S}, ::Type{ZZRingElem}) where {S <: NumFieldOrderElem} = S

#Nemo.promote_rule(::Type{AbsNumFieldOrderElem{S, T}}, ::Type{T}) where {S, T} = T

Nemo.promote_rule(::Type{T}, ::Type{AbsNumFieldOrderElem{S, T}}) where {S, T <: NumFieldElem} = T

Nemo.promote_rule(::Type{RelNumFieldOrderElem{S, T}}, ::Type{T}) where {S, T <: NumFieldElem} = T

Nemo.promote_rule(::Type{T}, ::Type{RelNumFieldOrderElem{S, T}}) where {S, T <: NumFieldElem} = T
