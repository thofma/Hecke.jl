################################################################################
#
#  Parent
#
################################################################################

@doc Markdown.doc"""
    parent(a::NumFieldOrdElem) -> NumFieldOrd

Returns the order of which $a$ is an element.
"""
parent(a::NumFieldOrdElem) = a.parent::parent_type(a)

################################################################################
#
#  Element in number field
#
################################################################################

@doc Markdown.doc"""
    elem_in_nf(a::NumFieldOrdElem) -> NumFieldElem

Returns the element $a$ considered as an element of the ambient number field.
"""
function elem_in_nf(a::NumFieldOrdElem; copy::Bool = true)
  if isdefined(a, :elem_in_nf)
    if copy
      return deepcopy(a.elem_in_nf)
    else
      return a.elem_in_nf
    end
  end
  error("Not a valid order element")
end

_elem_in_algebra(a::NumFieldOrdElem; copy::Bool = true) = elem_in_nf(a, copy = copy)

################################################################################
#
#  Special elements
#
################################################################################

zero(O::NumFieldOrd) = O(fmpz(0))

one(O::NumFieldOrd) = O(fmpz(1))

zero(a::NumFieldOrdElem) = parent(a)(0)

one(a::NumFieldOrdElem) = one(parent(a))

function zero!(a::NumFieldOrdElem)
  zero!(a.elem_in_nf)
  a.has_coord = false
  return a
end

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::NumFieldOrdElem) = isone(a.elem_in_nf)

iszero(a::NumFieldOrdElem) = iszero(a.elem_in_nf)

################################################################################
#
#  Unary operations
#
################################################################################

function -(a::NumFieldOrdElem)
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

function *(x::T, y::T) where T <: NumFieldOrdElem
  !check_parent(x, y) && error("Wrong parents")
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf*y.elem_in_nf
  return z
end

function +(x::T, y::T) where T <: NumFieldOrdElem
  !check_parent(x, y) && error("Wrong parents")
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  if x.has_coord && y.has_coord
    z.coordinates =
      [ x.coordinates[i] + y.coordinates[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

function -(x::T, y::T) where T <: NumFieldOrdElem
  !check_parent(x, y) && error("Wrong parents")
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y.elem_in_nf
  if x.has_coord && y.has_coord
    z.coordinates = [ x.coordinates[i] - y.coordinates[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

function divexact(x::T, y::T, check::Bool = true) where T <: NumFieldOrdElem
  !check_parent(x, y) && error("Wrong parents")
  a = divexact(x.elem_in_nf, y.elem_in_nf)
  if check
    if !in(a, parent(x))
      error("Quotient not an element of the order")
    end
  end
  z = parent(x)()
  z.elem_in_nf = a
  return z
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

for T in [Integer, fmpz]
  @eval begin
    function *(a::NumFieldOrdElem, b::$T)
      c = parent(a)()
      c.elem_in_nf = a.elem_in_nf*b
      if a.has_coord
        c.coordinates = map(x -> b*x, a.coordinates)
        c.has_coord = true
      end
      return c
    end

    *(a::$T, b::NumFieldOrdElem) = b*a

    function +(x::NumFieldOrdElem, y::$T)
      z = parent(x)()
      z.elem_in_nf = x.elem_in_nf + y
      return z
    end

    +(x::$T, y::NumFieldOrdElem) = y + x

    function -(x::NumFieldOrdElem, y::$T)
      z = parent(x)()
      z.elem_in_nf = x.elem_in_nf - y
      return z
    end

    function -(x::$T, y::NumFieldOrdElem)
      z = parent(y)()
      z.elem_in_nf = x - y.elem_in_nf
      return z
    end

    function divexact(a::NumFieldOrdElem, b::$T, check::Bool = true)
      t = divexact(a.elem_in_nf, b)
      if check
        if !in(t, parent(a))
          error("Quotient not an element of the order.")
        end
      end
      c  = parent(a)(t)
      return c
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
for T in [Integer, fmpz]
  @eval begin
    function ^(x::NumFieldOrdElem, y::$T)
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

@inline function add!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::NfAbsOrdElem)
  add!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

@inline function sub!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::NfAbsOrdElem)
  sub!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

@inline function mul!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::NfAbsOrdElem)
  mul!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

function addeq!(z::NfAbsOrdElem, x::NfAbsOrdElem)
  addeq!(z.elem_in_nf, x.elem_in_nf)
  if x.has_coord && z.has_coord
    for i in 1:degree(parent(z))
      add!(z.coordinates[i], z.coordinates[i], x.coordinates[i])
    end
  end
  return z
end

################################################################################
#
#  Unsafe ad hoc operations
#
################################################################################

# ad hoc
for T in [Integer, fmpz]
  @eval begin
    @inline function mul!(z::NumFieldOrdElem, x::NumFieldOrdElem, y::$T)
      z.elem_in_nf = mul!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    mul!(z::NumFieldOrdElem, x::$T, y::NumFieldOrdElem) = mul!(z, y, x)
  end
end

for T in [Integer, fmpz]
  @eval begin
    @inline function add!(z::NumFieldOrdElem, x::NumFieldOrdElem, y::$T)
      z.elem_in_nf = add!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    add!(z::NumFieldOrdElem, x::$T, y::NumFieldOrdElem) = add!(z, y, x)
  end
end

for T in [Integer, fmpz]
  @eval begin
    @inline function sub!(z::NumFieldOrdElem, x::NumFieldOrdElem, y::$T)
      z.elem_in_nf = sub!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    sub!(z::NumFieldOrdElem, x::$T, y::NumFieldOrdElem) = add!(z, y, x)
  end
end

################################################################################
#
#  Base cases for dot product of vectors
#
################################################################################

dot(x::NumFieldOrdElem, y::Integer) = x * y

dot(x::Integer, y::NumFieldOrdElem) = y * x

dot(x::NumFieldOrdElem, y::fmpz) = x * y

dot(x::fmpz, y::NumFieldOrdElem) = y * x


################################################################################
#
#  Trace
#
################################################################################

@doc Markdown.doc"""
    tr(a::NumFieldOrdElem)

Returns the trace of $a$ as an element of the base ring.
"""
function tr(a::NumFieldOrdElem)
  OK = parent(a)
  return base_ring(OK)(tr(a.elem_in_nf))
end

@doc Markdown.doc"""
    absolute_tr(a::NumFieldOrdElem) -> fmpz

Return the absolute trace as an integer.
"""
absolute_tr(a::NfAbsOrdElem) = tr(a)
absolute_tr(a::NfRelOrdElem) = absolute_tr(tr(a))

################################################################################
#
#  Norm
#
################################################################################

@doc Markdown.doc"""
    norm(a::NumFieldOrdElem)

Returns the norm of $a$ as an element in the base ring.
"""
function norm(a::NumFieldOrdElem)
  OK = parent(a)
  return base_ring(OK)(norm(a.elem_in_nf))
end

@doc Markdown.doc"""
    absolute_norm(a::NumFieldOrdElem) -> fmpz

Return the absolute norm as an integer.
"""
absolute_norm(a::NfAbsOrdElem) = norm(a)
absolute_norm(a::NfRelOrdElem) = absolute_norm(norm(a))

################################################################################
#
#  Discriminant
#
################################################################################

@doc Markdown.doc"""
    discriminant(B::Vector{NumFieldOrdElem})

Returns the discriminant of the family $B$ of algebraic numbers,
i.e. $det((tr(B[i]*B[j]))_{i, j})^2$.
"""
function discriminant(B::Vector{T}) where T <: NumFieldOrdElem
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

Base.hash(x::NumFieldOrdElem, h::UInt) = Base.hash(x.elem_in_nf, h)

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
    ==(x::NumFieldOrdElem, y::NumFieldOrdElem) -> Bool

Returns whether $x$ and $y$ are equal.
"""
==(x::NumFieldOrdElem, y::NumFieldOrdElem) = parent(x) === parent(y) &&
                                            x.elem_in_nf == y.elem_in_nf

################################################################################
#
#  Minkowski embedding
#
################################################################################

@doc Markdown.doc"""
    minkowski_map(a::NumFieldOrdElem, abs_tol::Int) -> Vector{arb}

Returns the image of $a$ under the Minkowski embedding.
Every entry of the array returned is of type `arb` with radius less then
`2^-abs_tol`.
"""
function minkowski_map(a::NumFieldOrdElem, abs_tol::Int = 32)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return minkowski_map(a.elem_in_nf, abs_tol)
end

################################################################################
#
#  Conjugates
#
################################################################################

@doc Markdown.doc"""
    conjugates_arb(x::NumFieldOrdElem, abs_tol::Int) -> Vector{acb}

Compute the conjugates of $x$ as elements of type `acb`.
Recall that we order the complex conjugates
$\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
$\sigma_{i}(x) = \overline{\sigma_{i + s}(x)}$ for $r + 2 \leq i \leq r + s$.

Every entry $y$ of the array returned satisfies `radius(real(y)) < 2^-abs_tol`,
`radius(imag(y)) < 2^-abs_tol` respectively.
"""
function conjugates_arb(x::NumFieldOrdElem, abs_tol::Int = 32)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return conjugates_arb(x.elem_in_nf, abs_tol)
end

@doc Markdown.doc"""
    conjugates_arb_log(x::NumFieldOrdElem, abs_tol::Int) -> Vector{arb}

Returns the elements
$(\log(\lvert \sigma_1(x) \rvert),\dotsc,\log(\lvert\sigma_r(x) \rvert),
\dotsc,2\log(\lvert \sigma_{r+1}(x) \rvert),\dotsc,
2\log(\lvert \sigma_{r+s}(x)\rvert))$ as elements of type `arb` radius
less then `2^-abs_tol`.
"""
function conjugates_arb_log(x::NumFieldOrdElem, abs_tol::Int = 32)
  return conjugates_arb_log(x.elem_in_nf, abs_tol)
end

################################################################################
#
#  T2
#
################################################################################

@doc Markdown.doc"""
    t2(x::NumFieldOrdElem, abs_tol::Int = 32) -> arb

Return the $T_2$-norm of $x$. The radius of the result will be less than
`2^-abs_tol`.
"""
function t2(x::NumFieldOrdElem, abs_tol::Int = 32)
  return t2(x.elem_in_nf, abs_tol)
end

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule(::Type{S}, ::Type{U}) where {S <: NumFieldOrdElem, U <: Integer} = S

Nemo.promote_rule(::Type{S}, ::Type{fmpz}) where {S <: NumFieldOrdElem} = S

Nemo.promote_rule(::Type{NfAbsOrdElem{S, T}}, ::Type{T}) where {S, T} = T

Nemo.promote_rule(::Type{T}, ::Type{NfAbsOrdElem{S, T}}) where {S, T} = T

Nemo.promote_rule(::Type{NfRelOrdElem{S, T}}, ::Type{T}) where {S, T} = T

Nemo.promote_rule(::Type{T}, ::Type{NfRelOrdElem{S, T}}) where {S, T} = T
