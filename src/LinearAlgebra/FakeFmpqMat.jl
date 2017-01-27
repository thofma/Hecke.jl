################################################################################
#
#  FakeFmpqMat.jl : Model fmpq_mat's as fmpz_mat's with denominator
#
################################################################################

export num, den

num(x::FakeFmpqMat) = x.num

den(x::FakeFmpqMat) = x.den

rows(x::FakeFmpqMat) = rows(x.num)

cols(x::FakeFmpqMat) = cols(x.num)

function simplify_content!(x::FakeFmpqMat)
  c = content(x.num)
  c = gcd(c, x.den)
  if c != 1 
    divexact!(x.num, x.num, c)
    x.den = div(x.den, c)
  end
  y = canonical_unit(x.den)
  if !isone(y)
    x.den *= y
    mul!(x.num, x.num, y)
  end
end

################################################################################
#
#  Hashing
#
################################################################################

function hash(a::FakeFmpqMat, b::UInt)
  h = Base.hash(num(a)) $ Base.hash(den(a))
  h = h $ Base.hash(b)
  h = (h << 1) | (h >> (sizeof(Int)*8 - 1))
  return h
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::FakeFmpqMat)
  print(io, "FakeFmpqMat with numerator\n", num(x), "\nand denominator ", den(x))
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
  i, d_i = pseudo_inv(num(x))
  i *= den(x)
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
  t = den(y)*num(x) + den(x)*num(y)
  d = den(x)*den(y)
  z = FakeFmpqMat(t,d)
  simplify_content!(z)
  return z
end

function *(x::FakeFmpqMat, y::FakeFmpqMat)
  t = num(x)*num(y)
  d = den(x)*den(y)
  z = FakeFmpqMat(t,d)
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
  z = FakeFmpqMat(t, den(x))
  simplify_content!(z)
  return z
end

function *(x::fmpz_mat, y::FakeFmpqMat)
  t = x*y.num
  z = FakeFmpqMat(t, den(y))
  simplify_content!(z)
  return z
end

################################################################################
#
#  Comparison
#
################################################################################

==(x::FakeFmpqMat, y::FakeFmpqMat) = (num(x) == num(y)) && (den(x) == den(y))

################################################################################
#
#  Conversion
#
################################################################################

to_array(x::FakeFmpqMat) = (x.num, x.den)

function to_fmpz_mat(x::FakeFmpqMat)
  den(x) != 1 && error("Denominator has to be 1")
  return num(x)
end

################################################################################
#
#  Hermite normal form for numerator
#
################################################################################

function hnf!(x::FakeFmpqMat)
  h = hnf(num(x))
  x.num = h
end

function hnf(x::FakeFmpqMat, shape = :lowerleft)
  h = _hnf(num(x), shape)
  return FakeFmpqMat(h,den(x))
end

################################################################################
#
#  Sub
#
################################################################################

function sub(x::FakeFmpqMat, r::UnitRange{Int}, c::UnitRange{Int})
  z = FakeFmpqMat(sub(num(x),r,c),den(x))
  return z
end

function Base.deepcopy_internal(x::FakeFmpqMat, dict::ObjectIdDict)
  z = FakeFmpqMat(deepcopy(num(x)), den(x))
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
