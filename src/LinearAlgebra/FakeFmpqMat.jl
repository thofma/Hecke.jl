################################################################################
#
#  FakeFmpqMat.jl : Model fmpq_mat's as fmpz_mat's with denominator
#
################################################################################

iszero(x::FakeFmpqMat) = iszero(x.num)

is_square(x::FakeFmpqMat) = is_square(numerator(x))

function numerator(x::FakeFmpqMat; copy::Bool = true)
  if copy
    return deepcopy(x.num)
  else
    return x.num
  end
end

function denominator(x::FakeFmpqMat; copy::Bool = true)
  if copy
    return deepcopy(x.den)
  else
    return x.den
  end
end

nrows(x::FakeFmpqMat) = nrows(x.num)

ncols(x::FakeFmpqMat) = ncols(x.num)

function simplify_content!(x::FakeFmpqMat)
  c = content(x.num)
  gcd!(c, c, x.den)
  if !isone(c)
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
#  Getindex
#
################################################################################

Base.getindex(a::FakeFmpqMat, i::Int, j::Int) = fmpq(a.num[i, j], a.den)

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
  return FakeFmpqMat(-x.num, x.den, true)
end

#TODO: may be possible to simplify more efficiently.
#The content of the numerator of the inverse may be non trivial!
function inv(x::FakeFmpqMat)
  i, d_i = pseudo_inv(x.num)
  g = gcd(d_i, x.den)
  if isone(g)
    return FakeFmpqMat(i * x.den, d_i)
  elseif g == d_i
    return FakeFmpqMat(i * divexact(x.den, d_i))
  elseif g == x.den
    return FakeFmpqMat(i, divexact(d_i, x.den))
  else
    return FakeFmpqMat(i * divexact(x.den, g), divexact(d_i, g))
  end
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(x::FakeFmpqMat, y::FakeFmpqMat)
  t = y.den * x.num + x.den * y.num
  d = x.den * y.den
  z = FakeFmpqMat(t, d)
  return z
end

function *(x::FakeFmpqMat, y::FakeFmpqMat)
  t = x.num * y.num
  d = x.den * y.den
  z = FakeFmpqMat(t, d)
  return z
end

function mul!(z::FakeFmpqMat, x::FakeFmpqMat, y::FakeFmpqMat)
  @req ncols(x) == nrows(y) "Wrong dimensions"
  @req nrows(z) == nrows(x) "Wrong dimensions"
  @req ncols(z) == ncols(y) "Wrong dimensions"
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
  t = x.num * y
  z = FakeFmpqMat(t, denominator(x))
  return z
end

function *(x::fmpz_mat, y::FakeFmpqMat)
  t = x * y.num
  z = FakeFmpqMat(t, denominator(y))
  return z
end

function *(x::Integer, y::FakeFmpqMat)
  g = gcd(x, y.den)
  if isone(g)
    return FakeFmpqMat(y.num * x, y.den, true)
  else
    return FakeFmpqMat(y.num * divexact(x, g), divexact(y.den, g), true)
  end
end

function *(x::fmpz, y::FakeFmpqMat)
  g = gcd(x, y.den)
  if isone(g)
    return FakeFmpqMat(y.num * x, y.den, true)
  else
    return FakeFmpqMat(y.num * divexact(x, g), divexact(y.den, g), true)
  end
end

*(x::FakeFmpqMat, y::Integer) = y * x

*(x::FakeFmpqMat, y::fmpz) = y * x

function *(x::fmpq, y::FakeFmpqMat)
  n = numerator(x)
  d = denominator(x)
  g = gcd(n, y.den)
  if isone(g)
    return FakeFmpqMat(y.num * n, y.den * d, true)
  else
    return FakeFmpqMat(y.num * divexact(n, g), d * divexact(y.den, g), true)
  end
end

*(x::FakeFmpqMat, y::fmpq) = y * x

*(x::FakeFmpqMat, y::Rational{<:Integer}) = x * fmpq(y)

*(x::Rational{<:Integer}, y::FakeFmpqMat) = y * x

################################################################################
#
#  Comparison
#
################################################################################

==(x::FakeFmpqMat, y::FakeFmpqMat) = (x.num == y.num) && (x.den == y.den)

isequal(x::FakeFmpqMat, y::FakeFmpqMat) = (x.num == y.num) && (x.den == y.den)

################################################################################
#
#  Conversion
#
################################################################################

to_array(x::FakeFmpqMat) = (x.num, x.den)

function to_fmpz_mat(x::FakeFmpqMat)
  !isone(x.den) && error("Denominator has to be 1")
  return numerator(x)
end

function FakeFmpqMat(x::Vector{fmpq})
  dens = fmpz[denominator(x[i]) for i=1:length(x)]
  den = lcm(dens)
  M = zero_matrix(FlintZZ, 1, length(x))
  for i in 1:length(x)
    M[1,i] = numerator(x[i])*divexact(den, dens[i])
  end
  return FakeFmpqMat(M,den)
end

function fmpq_mat(x::FakeFmpqMat)
  z = fmpq(1, x.den) * fmpq_mat(x.num)
  return z
end

function fmpq_mat(x::fmpz_mat)
  z = zero_matrix(FlintQQ, nrows(x), ncols(x))
  ccall((:fmpq_mat_set_fmpz_mat, libflint), Nothing, (Ref{fmpq_mat}, Ref{fmpz_mat}), z, x)
  return z
end

function _fmpq_mat_to_fmpz_mat_den(x::fmpq_mat)
  z = zero_matrix(FlintZZ, nrows(x), ncols(x))
  d = fmpz()
  ccall((:fmpq_mat_get_fmpz_mat_matwise, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz}, Ref{fmpq_mat}), z, d, x)
  return z, d
end

################################################################################
#
#  Hermite normal form for numerator
#
################################################################################

function hnf!(x::FakeFmpqMat, shape = :lowerleft)
  x.num = _hnf(x.num, shape)
  return x
end

function hnf(x::FakeFmpqMat, shape = :lowerleft; triangular_top::Bool = false, compute_det::Bool = false)
  if triangular_top
    @assert ncols(x) <= nrows(x)
    z = one(FlintZZ)
    for i in 1:(ncols(x) - 1)
      for j in (i + 1):ncols(x)
        @assert iszero(x.num[i, j])
      end
    end
    for i in 1:ncols(x)
      z = mul!(z, z, x.num[i, i])
    end
    h = _hnf_modular_eldiv(x.num, z, shape)
  elseif compute_det
    d = det(numerator(x))
    h = _hnf_modular_eldiv(x.num, d, shape)
  else
    h = _hnf(x.num, shape)
  end
  return FakeFmpqMat(h, denominator(x))
end

function hnf_modular_eldiv(x::FakeFmpqMat, g::fmpz, shape = :lowerleft)
  h = _hnf_modular_eldiv(x.num, g, shape)
  return FakeFmpqMat(h, denominator(x))
end

function hnf!!(x::FakeFmpqMat, shape = :lowerleft)
  _hnf!(x.num, shape)
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

function Base.deepcopy_internal(x::FakeFmpqMat, dict::IdDict)
  z = FakeFmpqMat()
  z.num = Base.deepcopy_internal(x.num, dict)
  z.den = Base.deepcopy_internal(x.den, dict)
  z.rows = nrows(x)
  z.cols = ncols(x)
  return z
end

################################################################################
#
#  Zero row
#
################################################################################

function is_zero_row(M::FakeFmpqMat, i::Int)
  return is_zero_row(M.num, i)
end

################################################################################
#
#  Zero row
#
################################################################################

function is_zero_column(M::FakeFmpqMat, i::Int)
  return is_zero_column(M.num, i)
end

################################################################################
#
#  Determinant
#
################################################################################

function det(x::FakeFmpqMat)
  nrows(x) != ncols(x) && error("Matrix must be square")

  return det(x.num)//(x.den)^nrows(x)
end

################################################################################
#
#  Rank
#
################################################################################

rank(x::FakeFmpqMat) = rank(x.num)

################################################################################
#
#  vcat / hcat
#
################################################################################

function vcat(M::FakeFmpqMat, N::FakeFmpqMat)
  g = gcd(denominator(M, copy = false), denominator(N, copy = false))
  d1 = divexact(denominator(M, copy = false), g)
  d2 = divexact(denominator(N, copy = false), g)
  M1 = numerator(M, copy = false)*d2
  N1 = numerator(N, copy = false)*d1
  return FakeFmpqMat(vcat(M1, N1), g*d1*d2)
end

function reduce(::typeof(vcat), A::Vector{FakeFmpqMat})
  if length(A) == 1
    return A[1]
  end

  d = reduce(lcm, (denominator(a) for a in A), init = fmpz(1))
  res = zero_matrix(FlintZZ, sum(nrows, A), ncols(A[1]))
  k = 1
  for i in 1:length(A)
    _copy_matrix_into_matrix(res, k, 1, divexact(d, denominator(A[i])) * numerator(A[i], copy = false))
    k += nrows(A[i])
  end
  return FakeFmpqMat(res, d)
end

function hcat(M::FakeFmpqMat, N::FakeFmpqMat)
  g = gcd(denominator(M, copy = false), denominator(N, copy = false))
  d1 = divexact(denominator(M, copy = false), g)
  d2 = divexact(denominator(N, copy = false), g)
  M1 = numerator(M, copy = false)*d2
  N1 = numerator(N, copy = false)*d1
  return FakeFmpqMat(hcat(M1, N1), g*d1*d2)
end

################################################################################
#
#  Transpose
#
################################################################################

function transpose(M::FakeFmpqMat)
  return FakeFmpqMat(transpose(numerator(M, copy = false)), denominator(M))
end
