################################################################################
#
#  FakeFmpqMat.jl : Model fmpq_mat's as fmpz_mat's with denominator
#
################################################################################

export FakeFmpqMatSpace, FakeFmpqMat

export num, den

FakeFmpqMatSpaceID = ObjectIdDict()

type FakeFmpqMatSpace
  rows::Int
  cols::Int

  function FakeFmpqMatSpace(r::Int, c::Int)
    try
      return FakeFmpqMatSpaceID[r,c]
    catch
      z = new(r,c)
      FakeFmpqMatSpaceID[r,c] = z
      return z
    end
  end
end

type FakeFmpqMat
  num::fmpz_mat
  den::fmpz
  parent::FakeFmpqMatSpace
  rows::Int
  cols::Int

  function FakeFmpqMat(x::fmpz_mat, y::fmpz)
    z = new()
    z.num = x
    z.den = y
    z.rows = rows(x)
    z.cols = cols(x)
    simplify_content!(z)
    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end

  function FakeFmpqMat(x::Tuple{fmpz_mat, fmpz})
    z = new()
    z.num = x[1]
    z.den = x[2]
    z.rows = rows(x[1])
    z.cols = cols(x[1])
    simplify_content!(z)
    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end

  function FakeFmpqMat(x::fmpz_mat)
    z = new()
    z.num = x
    z.den = ZZ(1)
    z.rows = rows(x)
    z.cols = cols(x)
    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end
end

num(x::FakeFmpqMat) = x.num

den(x::FakeFmpqMat) = x.den

function simplify_content!(x::FakeFmpqMat)
  c = content(x.num)
  c = gcd(c, x.den)
  if c != 1 
    x.num = divexact(x.num, c)
    x.den = div(x.den, c)
  end
  y = canonical_unit(x.den)
  x.den *= y
  x.num *= y
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
  i, d_i = pseudo_inverse(num(x))
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
