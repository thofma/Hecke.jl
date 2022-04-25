
export FakeFracFldMat

################################################################################
#
#  FakeFracFldMat
#
################################################################################

mutable struct FakeFracFldMat
  num::MatElem
  den::RingElem
  rows::Int
  cols::Int

  function FakeFracFldMat()
    z = new()
    return z
  end

  function FakeFracFldMat(x::MatElem, y::RingElem, simplified::Bool = false)
    z = new()
    z.num = x
    z.den = y
    z.rows = nrows(x)
    z.cols = ncols(x)
    if !simplified
      simplify_content!(z)
    end
    return z
  end

  function FakeFracFldMat(x::Tuple{MatElem, RingElem}, simplified::Bool = false)
    z = new()
    z.num = x[1]
    z.den = x[2]
    z.rows = nrows(x[1])
    z.cols = ncols(x[1])
    if !simplified
      simplify_content!(z)
    end
    return z
  end

  # TODO: Maybe this should be a copy option
  function FakeFracFldMat(x::MatElem)
    z = new()
    z.num = x
    z.den = one(base_ring(x))
    z.rows = nrows(x)
    z.cols = ncols(x)
    return z
  end
end

################################################################################
#
#  FakeFracFldMat.jl : Model matrices of the fraction field of an integral domain R as matrices in R  with denominator in R
#
################################################################################

Base.iszero(x::FakeFracFldMat) = iszero(x.num)

function Base.numerator(x::FakeFracFldMat; copy::Bool = true)
  if copy
    return deepcopy(x.num)
  else
    return x.num
  end
end

function Base.denominator(x::FakeFracFldMat; copy::Bool = true)
  if copy
    return deepcopy(x.den)
  else
    return x.den
  end
end

Hecke.nrows(x::FakeFracFldMat) = nrows(x.num)

Hecke.ncols(x::FakeFracFldMat) = ncols(x.num)

function simplify_content!(x::FakeFracFldMat)
  c = content(x.num)
  c = gcd(c, x.den)
  if !isone(c)
    x.num = divexact(x.num, c)
    x.den = divexact(x.den, c)
  end
  y = canonical_unit(x.den)
  if !isone(y)
    mul!(x.den, x.den, y)
    mul!(x.num, x.num, y)
  end
end



################################################################################
#
#  Getindex
#
################################################################################

Base.getindex(a::FakeFracFldMat, i::Int, j::Int) = FractionField(base_ring(a))(a.num[i, j], a.den)


################################################################################
#
#  Unary operations
#
################################################################################

function Base.:(-)(x::FakeFracFldMat)
  return FakeFracFldMat(-x.num, x.den, true)
end

#TODO: may be possible to simplify more efficiently.
#The content of the numerator of the inverse may be non trivial!
function Base.inv(x::FakeFracFldMat)
  i, d_i = pseudo_inv(x.num)
  g = gcd(d_i, x.den)
  if isone(g)
    return FakeFracFldMat(i * x.den, d_i)
  elseif g == d_i
    return FakeFracFldMat(i * divexact(x.den, d_i))
  elseif g == x.den
    return FakeFracFldMat(i, divexact(d_i, x.den))
  else
    return FakeFracFldMat(i * divexact(x.den, g), divexact(d_i, g))
  end
end

################################################################################
#
#  Binary operations
#
################################################################################

function Base.:(+)(x::FakeFracFldMat, y::FakeFracFldMat)
  t = y.den * x.num + x.den * y.num
  d = x.den * y.den
  z = FakeFracFldMat(t, d)
  return z
end

function Base.:(*)(x::FakeFracFldMat, y::FakeFracFldMat)
  t = x.num * y.num
  d = x.den * y.den
  z = FakeFracFldMat(t, d)
  return z
end

function Hecke.mul!(z::FakeFracFldMat, x::FakeFracFldMat, y::FakeFracFldMat)
  @assert ncols(x) == nrows(y) "Wrong dimensions"
  @assert nrows(z) == nrows(x) "Wrong dimensions"
  @assert ncols(z) == ncols(y) "Wrong dimensions"
  mul!(z.num, x.num, y.num)
  mul!(z.den, x.den, y.den)
  simplify_content!(z)
  return z
end

################################################################################
#
#  Adhoc binary operations
#
################################################################################

function Base.:(*)(x::FakeFracFldMat, y::MatElem)
  t = x.num * y
  z = FakeFracFldMat(t, denominator(x))
  return z
end

function Base.:(*)(x::MatElem, y::FakeFracFldMat)
  t = x * y.num
  z = FakeFracFldMat(t, denominator(y))
  return z
end

function Base.:(*)(x::RingElem, y::FakeFracFldMat)
  g = gcd(x, y.den)
  if isone(g)
    return FakeFracFldMat(y.num * x, y.den, true)
  else
    return FakeFracFldMat(y.num * divexact(x, g), divexact(y.den, g), true)
  end
end

Base.:(*)(x::FakeFracFldMat, y::RingElem) = y * x

################################################################################
#
#  Comparison
#
################################################################################

Base.:(==)(x::FakeFracFldMat, y::FakeFracFldMat) = (x.num == y.num) && (x.den == y.den)

Base.isequal(x::FakeFracFldMat, y::FakeFracFldMat) = (x.num == y.num) && (x.den == y.den)

################################################################################
#
#  Determinant
#
################################################################################

function Hecke.det(x::FakeFracFldMat)
  nrows(x) != ncols(x) && error("Matrix must be square")

  return det(x.num)//(x.den)^nrows(x)
end

################################################################################
#
#  Rank
#
################################################################################

Hecke.rank(x::FakeFracFldMat) = rank(x.num)


################################################################################
#
#  Transpose
#
################################################################################

function Hecke.transpose(M::FakeFracFldMat)
  return FakeFracFldMat(transpose(numerator(M, copy = false)), denominator(M))
end

