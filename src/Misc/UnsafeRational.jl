################################################################################
#
#  UnsafeRationals
#
################################################################################

# The ordinary Rational{Int} checks for overflow in every operations.
# UnsafeRational is like Rational, but with unsafe operations, that is, without
# the overflow checking.

import Base: Int128

################################################################################
#
#  Constructors and conversions
#
################################################################################

function UnsafeRational{T}(x::Int) where {T}
  return UnsafeRational{T}(T(x), one(T))
end

function UnsafeRational{T}(x::T) where {T}
  return UnsafeRational{T}(x, one(T))
end

function UnsafeRational{T}(x::Rational{<: Integer}) where {T}
  return UnsafeRational{T}(T(x.num), T(x.den))
end

function Int(x::UnsafeRational{T}) where {T}
  return Int(x.num)
end

Rational(x::UnsafeRational) = x.num//x.den


################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, x::UnsafeRational{T}) where T
  print(io, UnsafeRational{T}, "(", x.num, "//", x.den, ")")
end

################################################################################
#
#  Canonicalization functions
#
################################################################################

@inline function divgcd(x::Integer, y::Integer)
  g = gcd(x, y)
  return div(x, g), div(y, g)
end

@inline function divgcd(x::Int,y::Int)
  #g = gcd(x, y)
  if x < 0
    xx = -x
  else
    xx = x
  end
  if y < 0
    yy = -y
  else
    yy = y
  end
  g = ccall((:n_gcd, libflint), UInt, (UInt, UInt), xx, yy)
  return div(x, g), div(y, g)
end

################################################################################
#
#  Multiplication
#
################################################################################

@inline function Base.:(*)(x::UnsafeRational{T}, y::UnsafeRational{T}) where T
  xn,yd = divgcd(x.num,y.den)
  xd,yn = divgcd(x.den,y.num)
  z = UnsafeRational(xn * yn, xd * yd)
  #@assert Rational(x) * Rational(y) == Rational(z)
  return z
end

################################################################################
#
#  Addition
#
################################################################################

@inline function Base.:(+)(x::UnsafeRational{T}, y::UnsafeRational{T}) where T
  xd, yd = divgcd(x.den, y.den)
  s, t = x.num * yd + y.num * xd, x.den * yd
  sq, tq = divgcd(s, t)
  #@assert Rational(x) + Rational(y) == sq//tq
  return UnsafeRational{T}(sq, tq)
end

################################################################################
#
#  Division
#
################################################################################

@inline function Base.:(//)(x::UnsafeRational{T}, y::UnsafeRational{T}) where {T}
  xn,yn = divgcd(x.num,y.num)
  xd,yd = divgcd(x.den,y.den)
  z = UnsafeRational{T}(xn * yd, xd * yn)
  return z
end

################################################################################
#
#  Rounding
#
################################################################################

@inline function Base.floor(x::UnsafeRational{T}) where {T}
  z = UnsafeRational{T}(fld(x.num, x.den))
  return z
end

@inline function Base.ceil(x::UnsafeRational{T})where {T}
  z = UnsafeRational{T}(cld(x.num, x.den))
  return z
end

################################################################################
#
#  Ad hoc unary and binary operations
#
################################################################################

@inline function Base.:(*)(x::UnsafeRational{T}, y::Int) where {T}
  z = T(y)
  zn, zd = divgcd(x.den, z)
  z = UnsafeRational{T}(x.num * zd, zn)
  return z
end

@inline function Base.:(-)(x::UnsafeRational{T}, y::Int) where {T}
  z = x - UnsafeRational{T}(y)
  return z
end

@inline function Base.:(+)(x::UnsafeRational{T}, y::Int) where {T}
  z = x + UnsafeRational{T}(y)
  return z
end

@inline function Base.:(-)(x::UnsafeRational{T}, y::UnsafeRational{T}) where {T}
  z = x + (-y)
  return z
end

@inline function Base.:(-)(x::UnsafeRational{T}) where {T}
  z = UnsafeRational{T}(-x.num, x.den)
  return z
end

@inline is_negative(x::UnsafeRational) = x.num < 0

################################################################################
#
#  Comparison
#
################################################################################

@inline function Base.:(isless)(x::UnsafeRational{T}, y::Int) where {T}
  z = (x.num < x.den * y)
  return z
end

