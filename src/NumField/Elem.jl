
################################################################################
#
#  Base case for dot products
#
################################################################################

dot(x::fmpz, y::NumFieldElem) = x * y

dot(x::Integer, y::NumFieldElem) = x * y

dot(x::NumFieldElem, y::Integer) = x * y

function dot(a::Array{<: NumFieldElem, 1}, b::Array{fmpz, 1})
  d = zero(parent(a[1]))
  t = zero(d)
  for i=1:length(a)
    mul!(t, a[i], b[i])
    add!(d, d, t)
  end
  return d
end

################################################################################
#
#  Integrality
#
################################################################################

isintegral(a::fmpq) = isone(denominator(a))

@doc Markdown.doc"""
    isintegral(a::NumFieldElem) -> Bool

> Returns whether $a$ is integral, that is, whether the minimal polynomial
> of $a$ has integral coefficients.
"""
function isintegral(a::NumFieldElem)
  f = minpoly(a)
  for i = 0:(degree(f) - 1)
    if !isintegral(coeff(f, i))
      return false
    end
  end
  return true
end

################################################################################
#
#  Random elements from arrays of nf_elem
#
################################################################################

@doc Markdown.doc"""
    rand(b::Vector{NumFieldElem}, r::UnitRange) -> NumFieldElem

> A random linear combination of elements in `b` with coefficients in `r`.
"""
function rand(b::Vector{<: NumFieldElem}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r)
  return s
end

@doc Markdown.doc"""
    rand(b::Vector{NumFieldElem}, r::UnitRange, terms::Int) -> NumFieldElem

> A random linear combination (with repetitions) of `terms` elements of `b`
> with coefficients in `r`.
"""
function rand(b::Vector{<: NumFieldElem}, r::UnitRange, terms::Int)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r, terms)
  return s
end

@doc Markdown.doc"""
    rand!(c::NumFieldElem, b::Vector{NumFieldElem},
          r::UnitRange, terms::Int) -> NumFieldElem

> Sets `c` to a random linear combination (with repetitions) of \code{terms}
> elements of `b` with coefficients in `r`. The element `c` is returned.
"""
function rand!(c::T, b::Vector{T}, r::UnitRange,
               terms::Int) where {T <: NumFieldElem}
  length(b) == 0 && error("Array must not be empty")
  (terms <= 0 || terms > length(b)) && error("Number of terms should be at least 1 and cannot exceed the length of the array")

  t = zero(parent(c))

  terms = min(terms, length(b))
  mul!(c, rand(b), rand(r))
  for i = 2:terms
    mul!(t, rand(b), rand(r))
    add!(c, t, c)
  end

  return c
end

@doc Markdown.doc"""
    rand(c::NumFieldElem, b::Vector{NumFieldElem}, r::UnitRange) -> NumFieldElem

> Sets `c` to a random linear combination of elements in `b` with coefficients
> in `r`. The element `c` is returned.
"""
function rand!(c::T, b::Vector{T}, r::UnitRange) where {T <: NumFieldElem}
  length(b) == 0 && error("Array must not be empty")

  mul!(c, b[1], rand(r))
  t = zero(parent(c))

  for i = 2:length(b)
    mul!(t, b[i], rand(r))
    add!(c, t, c)
  end

  return c
end

################################################################################
#
#  Basis matrix
#
################################################################################

@doc Markdown.doc"""
    basis_mat(v::Vector{NumFieldElem}) -> Mat

> Given a vector `v` of `n` elements of a number field `K` of degree `d`, this
> function returns an `n x d` matrix with entries in the base field of $K$,
>  where row `i` contains the > coefficients of `v[i]` with respect of the
> canonical basis of `K`.
"""
basis_mat(v::Vector{<: NumFieldElem})
