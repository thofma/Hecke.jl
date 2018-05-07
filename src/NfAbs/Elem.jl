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
#  Powering with fmpz
#
################################################################################

function ^(x::nf_elem, y::fmpz)
  # TODO: try to coerce y to UInt
  if y < 0
    return inv(x)^(-y)
  elseif y == 0
    return parent(x)(1)
  elseif y == 1
    return deepcopy(x)
  elseif mod(y, 2) == 0
    z = x^(div(y, 2))
    return z*z
  elseif mod(y, 2) == 1
    return x^(y-1) * x
  end
end



################################################################################
#
#  Unsafe operations
#
################################################################################

function sub!(a::nf_elem, b::nf_elem, c::nf_elem)
   ccall((:nf_elem_sub, :libantic), Void,
         (Ref{nf_elem}, Ref{nf_elem}, Ref{nf_elem}, Ref{AnticNumberField}),
         a, b, c, a.parent)
end

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

function gen!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_gen, :libantic), Void,
         (Ptr{nf_elem}, Ptr{AnticNumberField}), &r, &a)
   return r
end

function one!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_one, :libantic), Void,
         (Ptr{nf_elem}, Ptr{AnticNumberField}), &r, &a)
   return r
end

function one(r::nf_elem)
   a = parent(r)
   return one(a)
end

function zero(r::nf_elem)
   return zero(parent(r))
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

# TODO: Remove this once we use Nemo >0.8.6
*(a::nf_elem, b::Integer) = a * fmpz(b)

################################################################################
#
#  Norm div
#
################################################################################

doc"""
***
   norm_div(a::nf_elem, d::fmpz, nb::Int) -> fmpz

Computes divexact(norm(a), d) provided the result has at most `nb` bits.
Typically, $a$ is in some ideal and $d$ is the norm of the ideal.
"""
function norm_div(a::nf_elem, d::fmpz, nb::Int)
   z = fmpq()
   # TODO:
   #CF the resultant code has trouble with denominators,
   #   this "solves" the problem, but it should probably be
   #   adressed in c
   @assert nb > 0
   de = denominator(a)
   n = degree(parent(a))
   ccall((:nf_elem_norm_div, :libantic), Void,
         (Ref{fmpq}, Ref{nf_elem}, Ref{AnticNumberField}, Ref{fmpz}, UInt),
         z, (a*de), a.parent, (d*de^n), UInt(nb))
   return z
end

