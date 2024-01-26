################################################################################
#
#  FakeFmpqMat.jl : Model QQMatrix's as ZZMatrix's with denominator
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

number_of_rows(x::FakeFmpqMat) = number_of_rows(x.num)

number_of_columns(x::FakeFmpqMat) = number_of_columns(x.num)

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

Base.getindex(a::FakeFmpqMat, i::Int, j::Int) = QQFieldElem(a.num[i, j], a.den)

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

function *(x::FakeFmpqMat, y::ZZMatrix)
  t = x.num * y
  z = FakeFmpqMat(t, denominator(x))
  return z
end

function *(x::ZZMatrix, y::FakeFmpqMat)
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

function *(x::ZZRingElem, y::FakeFmpqMat)
  g = gcd(x, y.den)
  if isone(g)
    return FakeFmpqMat(y.num * x, y.den, true)
  else
    return FakeFmpqMat(y.num * divexact(x, g), divexact(y.den, g), true)
  end
end

*(x::FakeFmpqMat, y::Integer) = y * x

*(x::FakeFmpqMat, y::ZZRingElem) = y * x

function *(x::QQFieldElem, y::FakeFmpqMat)
  n = numerator(x)
  d = denominator(x)
  g = gcd(n, y.den)
  if isone(g)
    return FakeFmpqMat(y.num * n, y.den * d, true)
  else
    return FakeFmpqMat(y.num * divexact(n, g), d * divexact(y.den, g), true)
  end
end

*(x::FakeFmpqMat, y::QQFieldElem) = y * x

*(x::FakeFmpqMat, y::Rational{<:Integer}) = x * QQFieldElem(y)

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

function FakeFmpqMat(x::Vector{QQFieldElem})
  dens = ZZRingElem[denominator(x[i]) for i=1:length(x)]
  den = lcm(dens)
  M = zero_matrix(FlintZZ, 1, length(x))
  for i in 1:length(x)
    M[1,i] = numerator(x[i])*divexact(den, dens[i])
  end
  return FakeFmpqMat(M,den)
end

function QQMatrix(x::FakeFmpqMat)
  z = QQFieldElem(1, x.den) * QQMatrix(x.num)
  return z
end

function _fmpq_mat_to_fmpz_mat_den(x::QQMatrix)
  z = zero_matrix(FlintZZ, nrows(x), ncols(x))
  d = ZZRingElem()
  ccall((:fmpq_mat_get_fmpz_mat_matwise, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZRingElem}, Ref{QQMatrix}), z, d, x)
  return z, d
end

function _fmpq_mat_to_fmpz_mat_den!(z::ZZMatrix, d::ZZRingElem, x::QQMatrix)
  ccall((:fmpq_mat_get_fmpz_mat_matwise, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZRingElem}, Ref{QQMatrix}), z, d, x)
end

function _fmpq_mat_set_fmpz_mat_div_fmpz!(z::QQMatrix, x::ZZMatrix, y::ZZRingElem)
  ccall((:fmpq_mat_set_fmpz_mat_div_fmpz, libflint), Nothing, (Ref{QQMatrix}, Ref{ZZMatrix}, Ref{ZZRingElem}), z, x, y)
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

function __hnf(x::FakeFmpqMat)
  FakeFmpqMat(Nemo.__hnf(x.num), x.den)
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

function hnf_modular_eldiv(x::FakeFmpqMat, g::ZZRingElem; shape = :lowerleft, cutoff::Bool = false)
  h = _hnf_modular_eldiv(x.num, g, shape)
  if cutoff
    # Since we are modular, we are in the full rank situation
    n = nrows(x)
    m = ncols(x)
    if shape === :lowerleft
      h = sub(h, (n - m + 1):n, 1:m)
    else
      h = sub(h, 1:m, 1:m)
    end
  end

  return FakeFmpqMat(h, denominator(x))
end

function hnf_modular_eldiv!(x::FakeFmpqMat, g::ZZRingElem; shape = :lowerleft, cutoff::Bool = false)
  h = hnf_modular_eldiv!(x.num, g, shape)
  # Since we are modular, we are in the full rank situation
  if cutoff
    n = nrows(x)
    m = ncols(x)
    if shape === :lowerleft
      x = sub(h, (n - m + 1):n, 1:m)
    else
      x = sub(h, 1:m, 1:m)
    end
  end
  return x
end

function _hnf_modular_iterative_eldiv(x::Vector{FakeFmpqMat}, g::ZZRingElem, shape = :lowerleft, cutoff::Bool = false)
end

function hnf!!(x::FakeFmpqMat, shape = :lowerleft)
  _hnf!(x.num, shape)
end

################################################################################
#
#  Sub
#
################################################################################

function sub(x::FakeFmpqMat, r::AbstractUnitRange{Int}, c::AbstractUnitRange{Int})
  z = FakeFmpqMat(sub(x.num, r, c), deepcopy(x.den))
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

  d = reduce(lcm, (denominator(a) for a in A), init = ZZRingElem(1))
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

################################################################################
#
#  Is triangular
#
################################################################################

is_upper_triangular(M::FakeFmpqMat) = is_upper_triangular(numerator(M, copy = false))

is_lower_triangular(M::FakeFmpqMat) = is_lower_triangular(numerator(M, copy = false))
