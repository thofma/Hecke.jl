################################################################################
#
#  FakeFmpqMat.jl : Model fmpq_mat's as fmpz_mat's with denominator
#
################################################################################

export num, den

numerator(x::FakeFmpqMat) = deepcopy(x.num)

denominator(x::FakeFmpqMat) = deepcopy(x.den)

rows(x::FakeFmpqMat) = rows(x.num)

cols(x::FakeFmpqMat) = cols(x.num)

function simplify_content!(x::FakeFmpqMat)
  c = content(x.num)
  c = gcd(c, x.den)
  if c != 1 
    divexact!(x.num, x.num, c)
    divexact!(x.den, x.den, c)
  end
  y = canonical_unit(x.den)
  if !isone(y)
    mul!(x.den, x.den, y)
    mul!(x.num, x.num, y)
  end
end

################################################################################
#
#  Hashing
#
################################################################################

function hash(a::FakeFmpqMat, b::UInt)
  h = xor(Base.hash(a.num, b), Base.hash(a.den, b))
  h = xor(h, Base.hash(b))
  h = (h << 1) | (h >> (sizeof(Int)*8 - 1))
  return h
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::FakeFmpqMat)
  print(io, "FakeFmpqMat with numerator\n", x.num, "\nand denominator ", x.den)
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::FakeFmpqMat)
  z = parent(x)()
  z.num = -x.num
  return z
end

function inv(x::FakeFmpqMat)
  i, d_i = pseudo_inv(x.num)
  i *= x.den
  z = FakeFmpqMat(i,d_i)
  simplify_content!(z)
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(x::FakeFmpqMat, y::FakeFmpqMat)
  t = y.den*x.num + x.den*y.num
  d = x.den*y.den
  z = FakeFmpqMat(t,d)
  simplify_content!(z)
  return z
end

function *(x::FakeFmpqMat, y::FakeFmpqMat)
  t = x.num*y.num
  d = x.den * y.den
  z = FakeFmpqMat(t, d)
  simplify_content!(z)
  return z
end

function mul!(z::FakeFmpqMat, x::FakeFmpqMat, y::FakeFmpqMat)
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

function *(x::FakeFmpqMat, y::fmpz_mat)
  t = x.num*y
  z = FakeFmpqMat(t, denominator(x))
  simplify_content!(z)
  return z
end

function *(x::fmpz_mat, y::FakeFmpqMat)
  t = x*y.num
  z = FakeFmpqMat(t, denominator(y))
  simplify_content!(z)
  return z
end

################################################################################
#
#  Comparison
#
################################################################################

==(x::FakeFmpqMat, y::FakeFmpqMat) = (x.num == y.num) && (x.den == y.den)

################################################################################
#
#  Conversion
#
################################################################################

to_array(x::FakeFmpqMat) = (x.num, x.den)

function to_fmpz_mat(x::FakeFmpqMat)
  x.den != 1 && error("Denominator has to be 1")
  return numerator(x)
end

################################################################################
#
#  Hermite normal form for numerator
#
################################################################################

function hnf!(x::FakeFmpqMat)
  x.num = hnf(x.num)
end

function hnf(x::FakeFmpqMat, shape = :lowerleft)
  h = _hnf(x.num, shape)
  return FakeFmpqMat(h, denominator(x))
end

################################################################################
#
#  Sub
#
################################################################################

function sub(x::FakeFmpqMat, r::UnitRange{Int}, c::UnitRange{Int})
  z = FakeFmpqMat(sub(x.num, r, c), x.den)
  return z
end

function Base.deepcopy_internal(x::FakeFmpqMat, dict::ObjectIdDict)
  z = FakeFmpqMat()
  z.num = Base.deepcopy_internal(x.num, dict)
  z.den = Base.deepcopy_internal(x.den, dict)
  z.rows = rows(x)
  z.cols = cols(x)
  z.parent = FakeFmpqMatSpace(z.rows, z.cols)
  return z
end

################################################################################
#
#  Determinant
#
################################################################################

function det(x::FakeFmpqMat)
  rows(x) != cols(x) && error("Matrix must be square")
  
  return det(x.num)//(x.den)^rows(x)
end
