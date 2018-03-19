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
#  Representation matrix
#
################################################################################

function representation_mat_fmpq_mat(a::nf_elem)
  d = degree(parent(a))
  t = gen(parent(a))
  b = deepcopy(a)
  N = zero_matrix(FlintQQ, d, d)
  M = zero_matrix(FlintZZ, 1, d)
  dummy = zero(FlintZZ)
  for i in 1:(d - 1)
    elem_to_mat_row!(M, 1, dummy, b)
    for j in 1:d
      N[i, j] = fmpq(M[1, j], dummy)
    end
    mul!(b, t, b)
  end
  elem_to_mat_row!(M, 1, dummy, b)
  for j in 1:d
    N[d, j] = fmpq(M[1, j], dummy)
  end
  return N
end

doc"""
  representation_mat(a::nf_elem) -> fmpz_mat

The right regular representation of a, i.e. the matrix representing
the multiplication map $x \mapsto ax$ on the number field.
denominator(a) must be one
"""
function representation_mat(a::nf_elem)
  @assert denominator(a) == 1
  dummy = fmpz(0)
  n = degree(a.parent)
  M = zero_matrix(FlintZZ, n, n)
  t = gen(a.parent)
  b = deepcopy(a)
  for i = 1:n-1
    elem_to_mat_row!(M, i, dummy, b)
    mul!(b, b, t) ## TODO: CF: should write and use mul_gen which is faster
  end
  elem_to_mat_row!(M, n, dummy, b)
  return M
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

function set_den!(a::nf_elem, d::fmpz)
  ccall((:nf_elem_set_den, :libflint), Void,
        (Ptr{nf_elem}, Ptr{fmpz}, Ptr{AnticNumberField}),
        &a, &d, &parent(a))
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

doc"""
***
  charpoly(a::nf_elem) -> fmpz_poly
  charpoly(a::NfOrdElem) -> fmpz_poly

> The characteristic polynomial of a.
"""
function charpoly(a::nf_elem)
  d = denominator(a)
  Zx = PolynomialRing(FlintZZ, string(parent(parent(a).pol).S))[1]
  f = charpoly(Zx, representation_mat(d*a))
  f =  f(gen(parent(f))*d)
  return divexact(f, content(f))
end

function charpoly(a::NfOrdElem)
  return charpoly(number_field(parent(a))(a))
end

################################################################################
#
#  Minimal polynomial
#
################################################################################

doc"""
***
  minpoly(a::nf_elem) -> fmpz_poly
  minpoly(a::NfOrdElem) -> fmpz_poly

> The minimal polynomial of a.
"""
function minpoly(a::nf_elem)
  d = denominator(a)
  Zx = PolynomialRing(FlintZZ, string(parent(parent(a).pol).S))[1]
  f = minpoly(Zx, representation_mat(d*a))
  f = f(gen(parent(f))*d)
  return divexact(f, content(f))
end

function minpoly(a::NfOrdElem)
  return minpoly(number_field(parent(a))(a))
end

