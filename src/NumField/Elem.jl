export coordinates, absolute_coordinates, absolute_norm, absolute_tr

################################################################################
#
#
#
################################################################################

isunit(a::NumFieldElem) = !iszero(a)

canonical_unit(a::NumFieldElem) = a

################################################################################
#
#  Base case for dot products
#
################################################################################

dot(x::fmpz, y::NumFieldElem) = x * y

dot(x::Integer, y::NumFieldElem) = x * y

dot(x::NumFieldElem, y::Integer) = x * y

function dot(a::Array{<: NumFieldElem, 1}, b::Array{fmpz, 1})
  d = zero(parent(a[1]))
  t = zero(d)
  for i=1:length(a)
    mul!(t, a[i], b[i])
    add!(d, d, t)
  end
  return d
end

################################################################################
#
#  Parent
#
################################################################################

@doc Markdown.doc"""
    parent(a::NumFieldElem) -> NumField

Given an element `a` of a number field $K$, this function returns $K$.
"""
parent(a::NumFieldElem)

################################################################################
#
#  Integrality
#
################################################################################

isintegral(a::fmpq) = isone(denominator(a))

@doc Markdown.doc"""
    isintegral(a::NumFieldElem) -> Bool

Returns whether `a` is integral, that is, whether the minimal polynomial of $a$
has integral coefficients.
"""
function isintegral(a::NumFieldElem)
  f = minpoly(a)
  for i = 0:(degree(f) - 1)
    if !isintegral(coeff(f, i))
      return false
    end
  end
  return true
end

################################################################################
#
#  Random elements from arrays of number field elements
#
################################################################################

@doc Markdown.doc"""
    rand(b::Vector{NumFieldElem}, r::UnitRange) -> NumFieldElem

A random linear combination of elements in `b` with coefficients in `r`.
"""
function rand(b::Vector{<: NumFieldElem}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r)
  return s
end

@doc Markdown.doc"""
    rand(b::Vector{NumFieldElem}, r::UnitRange, terms::Int) -> NumFieldElem

A random linear combination (with repetitions) of `terms` elements of `b`
with coefficients in `r`.
"""
function rand(b::Vector{<: NumFieldElem}, r::UnitRange, terms::Int)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r, terms)
  return s
end

@doc Markdown.doc"""
    rand!(c::NumFieldElem, b::Vector{NumFieldElem},
          r::UnitRange, terms::Int) -> NumFieldElem

Sets `c` to a random linear combination (with repetitions) of \code{terms}
elements of `b` with coefficients in `r`. The element `c` is returned.
"""
function rand!(c::T, b::Vector{T}, r::UnitRange,
               terms::Int) where {T <: NumFieldElem}
  length(b) == 0 && error("Array must not be empty")
  (terms <= 0 || terms > length(b)) && error("Number of terms should be at least 1 and cannot exceed the length of the array")

  t = zero(parent(c))

  terms = min(terms, length(b))
  mul!(c, rand(b), rand(r))
  for i = 2:terms
    mul!(t, rand(b), rand(r))
    add!(c, t, c)
  end

  return c
end

@doc Markdown.doc"""
    rand!(c::NumFieldElem, b::Vector{NumFieldElem}, r::UnitRange) -> NumFieldElem

Sets `c` to a random linear combination of elements in `b` with coefficients
in `r`. The element `c` is returned.
"""
function rand!(c::T, b::Vector{T}, r::UnitRange) where {T <: NumFieldElem}
  length(b) == 0 && error("Array must not be empty")

  mul!(c, b[1], rand(r))
  t = zero(parent(c))

  for i = 2:length(b)
    t = mul!(t, b[i], rand(r))
    c = add!(c, t, c)
  end

  return c
end

################################################################################
#
#  Basis matrix
#
################################################################################

@doc Markdown.doc"""
    basis_matrix(v::Vector{NumFieldElem}) -> Mat

Given a vector `v` of `n` elements of a number field `K` of degree `d`, this
function returns an `n x d` matrix with entries in the base field of $K$,
 where row `i` contains the > coefficients of `v[i]` with respect of the
canonical basis of `K`.
"""
basis_matrix(v::Vector{<: NumFieldElem})

################################################################################
#
#  Characteristic polynomial
#
################################################################################

@doc Markdown.doc"""
    charpoly(a::NumFieldElem) -> PolyElem

Given a number field element `a` of a number field `K`, this function returns
the characteristic polynomial of `a` over the base field of `K`.
"""
charpoly(::NumFieldElem)

@doc Markdown.doc"""
    absolute_charpoly(a::NumFieldElem) -> PolyElem

Given a number field element `a` of a number field `K`, this function returns
the characteristic polynomial of `a` over the rationals $\mathbf{Q}$.
"""
absolute_charpoly(::NumFieldElem)

@doc Markdown.doc"""
    minpoly(a::NumFieldElem) -> PolyElem

Given a number field element `a` of a number field `K`, this function returns
the minimal polynomial of `a` over the base field of `K`.
"""
minpoly(::NumFieldElem)

@doc Markdown.doc"""
    absolute_minpoly(a::NumFieldElem) -> PolyElem

Given a number field element `a` of a number field `K`, this function returns
the minimal polynomial of `a` over the rationals $\mathbf{Q}$.
"""
absolute_minpoly(::NumFieldElem)

################################################################################
#
#  Powering with fmpz
#
################################################################################

function ^(x::NumFieldElem, y::fmpz)
  if fits(Int, y)
    return x^Int(y)
  end

  return _power(x, y)
end

# We test once if it fits, otherwise we would have to check for every ^-call
function _power(x::NumFieldElem, y::fmpz)
  res = parent(x)()
  if y < 0
    res = _power(inv(x), -y)
  elseif y == 0
    res = parent(x)(1)
  elseif y == 1
    res = deepcopy(x)
  elseif mod(y, 2) == 0
    z = _power(x, div(y, 2))
    res = z*z
  else
    res = _power(x, y - 1) * x
  end
  return res
end

################################################################################
#
#  SimpleNumFieldElem
#
################################################################################

@doc Markdown.doc"""
    coeff(a::SimpleNumFieldElem, i::Int) -> FieldElem

Given a number field element `a` of a simple number field extension `L/K`, this
function returns the `i`-th coefficient of `a`, when expanded in the canonical
power basis of `L`. The result is an element of `K`.
"""
coeff(::SimpleNumFieldElem, ::Int)

# copy does not do anything (so far), this is only for compatibility with coeffs(::AbsAlgAssElem)

@doc Markdown.doc"""
    coeffs(a::SimpleNumFieldElem, i::Int) -> Vector{FieldElem}

Given a number field element `a` of a simple number field extension `L/K`, this
function returns the coefficients of `a`, when expanded in the canonical
power basis of `L`.
"""
function coeffs(a::SimpleNumFieldElem; copy::Bool = false)
  return [ coeff(a, i) for i = 0:degree(parent(a)) - 1 ]
end

@doc Markdown.doc"""
    (L::SimpleNumField)(c::Vector) -> SimpleNumFieldElem

Given a simple number field extension `L/K` and a vector of elements that are
coercible to `K`, this functions returns the element of `L` with coefficients
`c`.
"""
(K::SimpleNumField)(c::Vector)

function (K::AnticNumberField)(c::Vector{fmpq})
  @assert length(c) == degree(K)
  return K(parent(K.pol)(c))
end

function (L::NfRel{T})(a::Vector{T}) where T
  z = NfRelElem{T}(parent(L.pol)(a))
  z.parent = L
  return z
end

for F in [AnticNumberField, NfRel]
  @eval begin
    function (L::$F)(a::Vector)
      length(a) != degree(L) && throw(error("Vector must have length ($(length(a))) equal to the degree ($(degree(L)))"))
      K = base_field(L)
      aprom = Vector{elem_type(K)}(undef, degree(L))
      for i in 1:degree(L)
        aprom[i] = K(a[i])
      end
      return L(aprom)
    end
  end
end

################################################################################
#
#  Norm and trace
#
################################################################################

@doc Markdown.doc"""
    tr(a::NumFieldElem) -> NumFieldElem

Returns the trace of an element $a$ of a number field extension `L/K`. This
will be an element of `K`.
"""
tr(::NumFieldElem)

@doc Markdown.doc"""
    norm(a::NumFieldElem) -> NumFieldElem

Returns the norm of an element $a$ of a number field extension `L/K`. This
will be an element of `K`.
"""
norm(::NumFieldElem)


function _elem_tr_to(a::NumFieldElem{T}, k::S) where {S, T}
  if parent(a) isa T
    @assert parent(a) == k
    return a
  else
    return _elem_tr_to(tr(a), k)
  end
end

function _elem_norm_to(a, k::T) where {T}
  if parent(a) isa T
    @assert parent(a) == k
    return a
  else
    return _elem_norm_to(norm(a), k)
  end
end

@doc Markdown.doc"""
    tr(a::NumFieldElem, k::NumField) -> NumFieldElem

Returns the trace of an element $a$ of a number field `L` with respect to
a subfield $k$ of $L$. This will be an element of `k`.
"""
function tr(a::NumFieldElem, k::NumField)
  _elem_tr_to(a, k)
end

tr(a::NumFieldElem, ::FlintRationalField) = _elem_tr_to(a, FlintQQ)

@doc Markdown.doc"""
    norm(a::NumFieldElem, k::NumField) -> NumFieldElem

Returns the norm of an element $a$ of a number field `L` with respect to
a subfield $k$ of $L$. This will be an element of `k`.
"""
function norm(a::NumFieldElem, k::NumField)
  _elem_norm_to(a, k)
end

norm(a::NumFieldElem, ::FlintRationalField) = _elem_norm_to(a, FlintQQ)

@doc Markdown.doc"""
    absolute_tr(a::NumFieldElem) -> fmpq

Given a number field element $a$, returns the absolute trace of $a$.
"""
function absolute_tr(a::NfRelElem)
  return tr(a, FlintQQ)
end

absolute_tr(a::nf_elem) = tr(a)

absolute_tr(x::fmpq) = x

@doc Markdown.doc"""
    absolute_norm(a::NumFieldElem) -> fmpq

Given a number field element $a$, returns the absolute norm of $a$.
"""
function absolute_norm(a::T) where T <: Union{NfRelElem, NfRelNSElem}
  return norm(a, FlintQQ)
end

absolute_norm(a::T) where T <: Union{nf_elem, NfAbsNSElem} = norm(a)

absolute_norm(a::fmpq) = a

################################################################################
#
#  Polynomials
#
################################################################################

@doc Markdown.doc"""
    norm(f::PolyElem{<:NumFieldElem}) -> PolyElem

Returns the norm of $f$, that is, the product of all conjugates of $f$ taken
coefficientwise.
"""
function norm(f::PolyElem{<: NumFieldElem})
  K = base_ring(f)
  P = polynomial_to_power_sums(f, degree(f)*degree(K))
  PQ = elem_type(base_field(K))[tr(x) for x in P]
  return power_sums_to_polynomial(PQ)
end

function isirreducible(f::PolyElem{<: NumFieldElem})
  # TODO (easy): We can do better then this. First do a squarefree factorization
  lf = factor(f)
  return sum(values(lf.fac)) == 1
end

function factor(f::PolyElem{<: NumFieldElem})
  K = base_ring(f)
  Ka, rel_abs, _ = absolute_field(K)

  function map_poly(P::Ring, mp::Map, f::Generic.Poly)
    return P([mp(coeff(f, i)) for i=0:degree(f)])
  end

  fa = map_poly(PolynomialRing(Ka, "T", cached=false)[1], pseudo_inv(rel_abs), f)
  lf = factor(fa)
  res = Fac(map_poly(parent(f), rel_abs, lf.unit), Dict(map_poly(parent(f), rel_abs, k)=>v for (k,v) = lf.fac))

  return res
end

function roots(f::PolyElem{<: NumFieldElem})
  lf = factor(f)
  @assert degree(unit(lf)) == 0
  scale = inv(coeff(unit(lf), 0))
  return elem_type(base_ring(f))[-constant_coefficient(x)*scale for x = keys(lf.fac) if degree(x) == 1]
end

################################################################################
#
#
#
################################################################################

@doc Markdown.doc"""
    representation_matrix(a::NumFieldElem) -> MatElem
 
Returns the representation matrix of $a$, that is, the matrix representing
multiplication with $a$ with respect to the canonical basis of the parent of $a$.
"""
representation_matrix(a::NumFieldElem)

################################################################################
#
#
#
################################################################################

@doc Markdown.doc"""
    gen(L::SimpleNumField) -> NumFieldElem

Given a simple number field $L = K[x]/(x)$ over $K$, this functions returns the
class of $x$, which is the canonical primitive element of $L$ over $K$.
"""
gen(::SimpleNumField)

@doc Markdown.doc"""
    gens(L::NonSimpleNumField) -> Vector{NumFieldElem}

Given a non-simple number field $L = K[x_1,\dotsc,x_n]/(f_1,\dotsc,f_n)$ over
$K$, this functions returns the list $\bar x_1,\dotsc,\bar x_n$.
"""
gens(::NonSimpleNumField)

################################################################################
#
#  Coordinates
#
################################################################################
@doc Markdown.doc"""
    coordinates(x::NumFieldElem{T}) -> Vector{T}

Given an element $x$ in a number field $K$, this function returns the coordinates of $x$
with respect to the basis of $K$ (the output of the 'basis' function).
"""
coordinates(::NumFieldElem)

function coordinates(a::nf_elem)
  K = parent(a)
  v = Vector{fmpq}(undef, degree(K))
  for i = 1:length(v)
    v[i] = coeff(a, i-1)
  end
  return v
end

function coordinates(a::NfAbsNSElem)
  adata = data(a)
  K = parent(a)
  v = Vector{fmpq}(undef, degree(K))
  for i = 1:length(v)
    v[i] = fmpq(0)
  end
  for j in 1:length(adata)
    exps = exponent_vector(adata, j)
    k = monomial_to_index(K, exps)
    v[k] = coeff(adata, j)
  end
  return v
end

function coordinates(a::NfRelElem{T}) where T
  K = parent(a)
  k = base_field(K)
  v = Vector{T}(undef, degree(K))
  for i = 1:length(v)
    v[i] = coeff(data(a), i-1)
  end
  return v
end

function coordinates(a::NfRelNSElem{T}) where T
  K = parent(a)
  k = base_field(K)
  v = Vector{T}(undef, degree(K))
  for j = 1:length(v)
    v[j] = zero(k)
  end
  for j = 1:length(a.data)
    v[monomial_to_index(j, a)] = a.data.coeffs[j]
  end
  return v
end

################################################################################
#
#  Absolute coordinates
#
################################################################################

@doc Markdown.doc"""
    coordinates(x::NumFieldElem{T}) -> Vector{T}

Given an element $x$ in a number field $K$, this function returns the coordinates of $x$
with respect to the basis of $K$ over the rationals (the output of the 'absolute_basis' function).
"""
absolute_coordinates(::NumFieldElem)

function absolute_coordinates(a::nf_elem)
  return coordinates(a)
end

function absolute_coordinates(a::NfAbsNSElem)
  return coordinates(a)
end

function absolute_coordinates(a::T) where T <: Union{NfRelElem, NfRelNSElem}
  K = parent(a)
  v = Vector{fmpq}(undef, absolute_degree(K))
  va = coordinates(a)
  ind = 1
  for i = 1:length(va)
    vi = absolute_coordinates(va[i])
    for j = 1:length(vi)
      v[ind] = vi[j]
      ind += 1
    end
  end
  return v
end

