################################################################################
#
#  Base case for dot products
#
################################################################################

dot(x::fmpz, y::nf_elem) = x*y

dot(x::nf_elem, y::fmpz) = x*y

################################################################################
#
#  Random elements from arrays of nf_elem
#
################################################################################

doc"""
***
    rand(b::Array{nf_elem,1}, r::UnitRange)

A random linear combination of elements in `b` with coefficients in `r`.
"""
function rand(b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r)
  return s
end

doc"""
***
    rand(b::Array{nf_elem,1}, r::UnitRange, terms::Int) -> nf_elem

A random linear combination (with repetitions) of \code{terms} elements of `b`
with coefficients in `r`.
"""
function rand(b::Array{nf_elem,1}, r::UnitRange, terms::Int)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r, terms)
  return s
end

function rand!(c::nf_elem, b::Array{nf_elem,1}, r::UnitRange, terms::Int)
  length(b) == 0 && error("Array must not be empty")
  (terms<=0 || terms > length(b)) && error("Number of terms should be at least 1 and cannot exceed the length of the array")

  t = zero(parent(b[1]))

  terms = min(terms, length(b))
  mul!(c, rand(b), rand(r))
  for i = 2:terms
    mul!(t, rand(b), rand(r))
    add!(c, t, c)
  end

  return c
end

function rand!(c::nf_elem, b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")

  mul!(c, b[1], rand(r))
  t = zero(b[1].parent)

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

function basis_mat(A::Array{nf_elem, 1})
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))

  M = zero_matrix(FlintZZ, n, d)

  deno = one(FlintZZ)
  dummy = one(FlintZZ)

  for i in 1:n
    deno = lcm(deno, denominator(A[i]))
  end

  for i in 1:n
    elem_to_mat_row!(M, i, dummy, A[i])
    temp_den = divexact(deno, dummy)
    for j in 1:d
      M[i, j] = mul!(M[i, j], M[i, j], temp_den)
    end
  end
  return FakeFmpqMat(M, deno)
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

doc"""
***
    charpoly(a::nf_elem) -> fmpq_poly

The characteristic polynomial of a.
"""
function charpoly(a::nf_elem, Qx::FmpqPolyRing = parent(parent(a).pol))
  f = charpoly(Qx, representation_matrix(a))
  return f
end

################################################################################
#
#  Minimal polynomial
#
################################################################################

doc"""
***
  minpoly(a::nf_elem) -> fmpq_poly

> The minimal polynomial of a.
"""
function minpoly(a::nf_elem, Qx::FmpqPolyRing = parent(parent(a).pol))
  f = minpoly(Qx, representation_matrix(a))
  return f
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function set_den!(a::nf_elem, d::fmpz)
  ccall((:nf_elem_set_den, :libflint), Void,
        (Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
        a, d, parent(a))
end

function divexact!(z::nf_elem, x::nf_elem, y::fmpz)
  ccall((:nf_elem_scalar_div_fmpz, :libantic), Void,
        (Ref{nf_elem}, Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
        z, x, y, parent(x))
  return z
end
