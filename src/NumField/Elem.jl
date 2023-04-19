export coordinates, absolute_coordinates, absolute_norm, absolute_tr,
       absolute_minpoly

################################################################################
#
#
#
################################################################################

is_unit(a::NumFieldElem) = !iszero(a)

canonical_unit(a::NumFieldElem) = a

################################################################################
#
#  Base case for dot products
#
################################################################################

dot(x::ZZRingElem, y::NumFieldElem) = x * y

dot(x::Integer, y::NumFieldElem) = x * y

dot(x::NumFieldElem, y::Integer) = x * y

function dot(a::Vector{<: NumFieldElem}, b::Vector{ZZRingElem})
  d = zero(parent(a[1]))
  t = zero(d)
  for i=1:length(a)
    mul!(t, a[i], b[i])
    add!(d, d, t)
  end
  return d
end

function dot(a::Vector{NfAbsNSElem}, b::Vector{ZZRingElem})
  Qxy = parent(a[1].data)
  d = zero(Qxy)
  t = zero(Qxy)
  for i = 1:length(a)
    if !iszero(b[i])
      mul!(t, a[i].data, b[i])
      add!(d, d, t)
    end
  end
  return parent(a[1])(d)
end

################################################################################
#
#  Parent
#
################################################################################

# Covered by the general ring interface

################################################################################
#
#  Integrality
#
################################################################################

is_integral(a::QQFieldElem) = isone(denominator(a))

@doc doc"""
    is_integral(a::NumFieldElem) -> Bool

Returns whether $a$ is integral, that is, whether the minimal polynomial of $a$
has integral coefficients.
"""
function is_integral(a::NumFieldElem)
  K = parent(a)
  if is_maximal_order_known(K)
    OK = maximal_order(K)
    return a in OK
  end
  f = minpoly(a)
  for i in 0:(degree(f) - 1)
    if !is_integral(coeff(f, i))
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

## rand(::Vector{NumFieldElem}, ::UnitRange)

@doc doc"""
    rand([rng::AbstractRNG], b::Vector{NumFieldElem}, r::UnitRange) -> NumFieldElem
    rand([rng::AbstractRNG], make(F::NumField, b::Vector{NumFieldElem}, r::UnitRange)) -> NumFieldElem

A random linear combination of elements in `b`, with parent `F` and coefficients in `r`.
"""
rand(b::Vector{<: NumFieldElem}, r::UnitRange) = rand(Random.GLOBAL_RNG, b, r)

function rand(rng::AbstractRNG, b::Vector{<: NumFieldElem}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")
  return rand(rng, make(parent(b[1]), b, r))
end

function rand(rng::AbstractRNG,
              sp::SamplerTrivial{<:Make3{<:NumFieldElem{T},<:NumField{T},
                                         <:Vector{<:NumFieldElem{T}},<:UnitRange}}) where {T}
  return rand!(rng, zero(sp[][1]), sp)
end


## rand(::Vector{<: NumFieldElem}, ::UnitRange, ::Int)

@doc doc"""
    rand([rng::AbstractRNG], b::Vector{NumFieldElem}, r::UnitRange, terms::Int) -> NumFieldElem
    rand([rng::AbstractRNG],
         make(F::NumField, b::Vector{NumFieldElem}, r::UnitRange, terms::Int)) -> NumFieldElem

A random linear combination (with repetitions) of `terms` elements of `b`
with parent `F` and coefficients in `r`.
"""
function rand(b::Vector{<: NumFieldElem}, r::UnitRange, terms::Int)
  return rand(Random.GLOBAL_RNG, b, r, terms)
end

function rand(rng::AbstractRNG, b::Vector{<: NumFieldElem}, r::UnitRange, terms::Int)
  length(b) == 0 && error("Array must not be empty")
  return rand(rng, make(parent(b[1]), b, r, terms))
end

function rand(rng::AbstractRNG,
              sp::SamplerTrivial{<:Make4{<:NumFieldElem{T},<:NumField{T},
                                         <:Vector{<:NumFieldElem{T}},<:UnitRange,Int}}) where {T}
  return rand!(rng, zero(sp[][1]), sp)
end


## rand!(::NumFieldElem, ::Vector{NumFieldElem}, ::UnitRange, terms::Int)

@doc doc"""
    rand!([rng::AbstractRNG], c::NumFieldElem, b::Vector{NumFieldElem},
          r::UnitRange, terms::Int) -> NumFieldElem
    rand!([rng::AbstractRNG], c::NumFieldElem,
          make(F::NumField, b::Vector{NumFieldElem}, r::UnitRange, terms::Int)) -> NumFieldElem

Sets `c` to a random linear combination (with repetitions) of \code{terms}
elements of `b` with coefficients in `r`. The element `c` is returned.
In the second form, `F` must be the parent of `c`.
"""
function rand!(c::T, b::Vector{T}, r::UnitRange, terms::Int) where {T <: NumFieldElem}
  rand!(Random.GLOBAL_RNG, c, b, r, terms)
end

function rand!(rng::AbstractRNG, c::T, b::Vector{T}, r::UnitRange, terms::Int) where {T <: NumFieldElem}
  return rand!(rng, c, make(parent(c), b, r, terms))
end

function rand!(rng::AbstractRNG, c::NumFieldElem{T},
               sp::SamplerTrivial{<:Make4{<:NumFieldElem{T},<:NumField{T},
                                          <:Vector{<:NumFieldElem{T}},<:UnitRange,Int}}) where {T}
  F, b, r, terms = sp[][1:end]

  length(b) == 0 && error("Array must not be empty")
  0 < terms <= length(b) || error("Number of terms should be at least 1 and cannot exceed the length of the array")
  F == parent(c) || error("incompatible parent and element")

  t = zero(F)

  mul!(c, rand(rng, b), rand(rng, r))
  for i = 2:terms
    mul!(t, rand(rng, b), rand(rng, r))
    add!(c, t, c)
  end

  return c
end


## rand!(::NumFieldElem, ::Vector{NumFieldElem}, ::UnitRange)

@doc doc"""
    rand!(c::NumFieldElem, b::Vector{NumFieldElem}, r::UnitRange) -> NumFieldElem
    rand!(c::NumFieldElem, make(F::NumField, b::Vector{NumFieldElem}, r::UnitRange)) -> NumFieldElem

Sets `c` to a random linear combination of elements in `b` with coefficients
in `r`. The element `c` is returned.
In the second form, `F` must be the parent of `c`.
"""
function rand!(c::T, b::Vector{T}, r::UnitRange) where {T <: NumFieldElem}
  return rand!(GLOBAL_RNG, c, b, r)
end

function rand!(rng::AbstractRNG, c::T, b::Vector{T}, r::UnitRange) where {T <: NumFieldElem}
  return rand!(rng, c, make(parent(c), b, r))
end

RandomExtensions.maketype(F::NumField{T}, ::Vector{<:NumFieldElem{T}}, ::UnitRange, ::Int...) where {T} = elem_type(F)

function rand!(rng::AbstractRNG, c::NumFieldElem{T},
               sp::SamplerTrivial{<:Make3{<:NumFieldElem{T},<:NumField{T},
                                          <:Vector{<:NumFieldElem{T}},<:UnitRange}}) where {T}
  F, b, r = sp[][1:end]

  length(b) == 0 && error("Array must not be empty")
  F == parent(c) || error("incompatible parent and element")

  mul!(c, b[1], rand(rng, r))
  t = zero(F)

  for i = 2:length(b)
    t = mul!(t, b[i], rand(rng, r))
    c = add!(c, t, c)
  end

  return c
end

################################################################################
#
#  Basis matrix
#
################################################################################

@doc doc"""
    basis_matrix(v::Vector{NumFieldElem}) -> Mat

Given a vector $v$ of $n$ elements of a number field $K$ of degree $d$, this
function returns an $n \times d$ matrix with entries in the base field of $K$, where
row $i$ contains the coefficients of $v[i]$ with respect of the canonical
basis of $K$.
"""
basis_matrix(v::Vector{<: NumFieldElem})

################################################################################
#
#  Characteristic polynomial
#
################################################################################

@doc doc"""
    charpoly(a::NumFieldElem) -> PolyElem

Given a number field element $a$ of a number field $K$, this function returns
the characteristic polynomial of $a$ over the base field of $K$.
"""
charpoly(::NumFieldElem)

@doc doc"""
    absolute_charpoly(a::NumFieldElem) -> PolyElem

Given a number field element $a$ of a number field $K$, this function returns
the characteristic polynomial of $a$ over the rationals $\mathbf{Q}$.
"""
absolute_charpoly(::NumFieldElem)

@doc doc"""
    minpoly(a::NumFieldElem) -> PolyElem

Given a number field element $a$ of a number field $K$, this function returns
the minimal polynomial of $a$ over the base field of $K$.
"""
minpoly(::NumFieldElem)

@doc doc"""
    absolute_minpoly(a::NumFieldElem) -> PolyElem

Given a number field element $a$ of a number field $K$, this function returns
the minimal polynomial of $a$ over the rationals $\mathbf{Q}$.
"""
absolute_minpoly(::NumFieldElem)

################################################################################
#
#  Powering with ZZRingElem
#
################################################################################

function ^(x::NumFieldElem, y::ZZRingElem)
  if fits(Int, y)
    return x^Int(y)
  end

  return _power(x, y)
end

# We test once if it fits, otherwise we would have to check for every ^-call
function _power(x::NumFieldElem, y::ZZRingElem)
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

@doc doc"""
    coeff(a::SimpleNumFieldElem, i::Int) -> FieldElem

Given a number field element `a` of a simple number field extension `L/K`, this
function returns the `i`-th coefficient of `a`, when expanded in the canonical
power basis of `L`. The result is an element of `K`.
"""
coeff(::SimpleNumFieldElem, ::Int)

# copy does not do anything (so far), this is only for compatibility with coefficients(::AbsAlgAssElem)

@doc doc"""
    coefficients(a::SimpleNumFieldElem, i::Int) -> Vector{FieldElem}

Given a number field element `a` of a simple number field extension `L/K`, this
function returns the coefficients of `a`, when expanded in the canonical
power basis of `L`.
"""
function coefficients(a::SimpleNumFieldElem; copy::Bool = false)
  return [ coeff(a, i) for i = 0:degree(parent(a)) - 1 ]
end

@doc doc"""
    (L::SimpleNumField)(c::Vector) -> SimpleNumFieldElem

Given a simple number field extension `L/K` and a vector of elements that are
coercible to `K`, this functions returns the element of `L` with coefficients
`c`.
"""
(K::SimpleNumField)(c::Vector)

function (K::AnticNumberField)(c::Vector{QQFieldElem})
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

@doc doc"""
    tr(a::NumFieldElem) -> NumFieldElem

Returns the trace of an element $a$ of a number field extension $L/K$. This
will be an element of $K$.
"""
tr(::NumFieldElem)

@doc doc"""
    norm(a::NumFieldElem) -> NumFieldElem

Returns the norm of an element $a$ of a number field extension $L/K$. This
will be an element of $K$.
"""
norm(::NumFieldElem)


function _elem_tr_to(a, k::T) where {T}
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

@doc doc"""
    tr(a::NumFieldElem, k::NumField) -> NumFieldElem

Returns the trace of an element $a$ of a number field $L$ with respect to
a subfield $k$ of $L$. This will be an element of $k$.
"""
function tr(a::NumFieldElem, k::NumField)
  return _elem_tr_to(a, k)
end

tr(a::NumFieldElem, ::QQField) = _elem_tr_to(a, FlintQQ)

@doc doc"""
    norm(a::NumFieldElem, k::NumField) -> NumFieldElem

Returns the norm of an element $a$ of a number field $L$ with respect to
a subfield $k$ of $L$. This will be an element of $k$.
"""
function norm(a::NumFieldElem, k::NumField)
  _elem_norm_to(a, k)
end

norm(a::NumFieldElem, ::QQField) = _elem_norm_to(a, FlintQQ)

@doc doc"""
    absolute_tr(a::NumFieldElem) -> QQFieldElem

Given a number field element $a$, returns the absolute trace of $a$.
"""
function absolute_tr(a::T) where T <: NumFieldElem
  return absolute_tr(tr(a))
end

absolute_tr(a::nf_elem) = tr(a)

absolute_tr(a::NfAbsNSElem) = tr(a)

absolute_tr(x::QQFieldElem) = x

@doc doc"""
    absolute_norm(a::NumFieldElem) -> QQFieldElem

Given a number field element $a$, returns the absolute norm of $a$.
"""
function absolute_norm(a::T) where T <: NumFieldElem
  return absolute_norm(norm(a))
end

absolute_norm(a::T) where T <: Union{nf_elem, NfAbsNSElem} = norm(a)

absolute_norm(a::QQFieldElem) = a

################################################################################
#
#  Polynomials
#
################################################################################

@doc doc"""
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

function norm(f::PolyElem{<:NumFieldElem}, k::NumField)
  K = base_ring(f)
  P = polynomial_to_power_sums(f, degree(f)*degree(K))
  PQ = elem_type(base_field(K))[tr(x, k) for x in P]
  return power_sums_to_polynomial(PQ)
end

norm(a::QQPolyRingElem) = a

absolute_norm(a::QQPolyRingElem) = a

function absolute_norm(f::PolyElem{nf_elem})
  return norm(f)
end

function absolute_norm(f::PolyElem{<: NumFieldElem})
  return absolute_norm(norm(f))
end

function is_irreducible(f::PolyElem{<: NumFieldElem})
  # TODO (easy): We can do better then this. First do a squarefree factorization
  lf = factor(f)
  return sum(values(lf.fac)) == 1
end

function AbstractAlgebra.factor(f::PolyElem{<: NumFieldElem})
  K = base_ring(f)
  Ka, mKa = absolute_simple_field(K)

  fKa = map_coefficients(inv(mKa), f)
  lf = factor(fKa)
  res = Fac(map_coefficients(mKa, lf.unit, parent = parent(f)), Dict(map_coefficients(mKa, k, parent = parent(f)) => v for (k,v) = lf.fac))

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

@doc doc"""
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

@doc doc"""
    gen(L::SimpleNumField) -> NumFieldElem

Given a simple number field $L = K[x]/(f)$ over $K$, this functions returns the
class of $x$, which is the canonical primitive element of $L$ over $K$.
"""
gen(::SimpleNumField)

@doc doc"""
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

@doc doc"""
    coordinates(x::NumFieldElem{T}) -> Vector{T}

Given an element $x$ in a number field $K$, this function returns the coordinates of $x$
with respect to the basis of $K$ (the output of the 'basis' function).
"""
coordinates(::NumFieldElem)

function coordinates(a::nf_elem)
  K = parent(a)
  v = Vector{QQFieldElem}(undef, degree(K))
  for i = 1:length(v)
    v[i] = coeff(a, i-1)
  end
  return v
end

function coordinates(a::NfAbsNSElem)
  adata = data(a)
  K = parent(a)
  v = Vector{QQFieldElem}(undef, degree(K))
  for i = 1:length(v)
    v[i] = QQFieldElem(0)
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

@doc doc"""
    absolute_coordinates(x::NumFieldElem{T}) -> Vector{T}

Given an element $x$ in a number field $K$, this function returns the coordinates of $x$
with respect to the basis of $K$ over the rationals (the output of the [`absolute_basis`](@ref) function).
"""
absolute_coordinates(::NumFieldElem)

function absolute_coordinates(a::NumFieldElem{QQFieldElem})
  return coordinates(a)
end

function absolute_coordinates(a::T) where T <: Union{NfRelElem, NfRelNSElem}
  K = parent(a)
  v = Vector{QQFieldElem}(undef, absolute_degree(K))
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

################################################################################
#
#  Denominator
#
################################################################################

function denominator!(z::ZZRingElem, a::nf_elem)
   ccall((:nf_elem_get_den, libantic), Nothing,
         (Ref{ZZRingElem}, Ref{nf_elem}, Ref{AnticNumberField}),
         z, a, a.parent)
   return z
end

################################################################################
#
#  Valuation
#
################################################################################

@doc raw"""
    valuation(a::NumFieldElem, p::NfOrdIdl) -> ZZRingElem

Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
such that $a$ is contained in $\mathfrak p^i$.
"""
function valuation(::NumFieldElem, p) end

################################################################################
#
#   Support
#
################################################################################

function support(a::NumFieldElem{QQFieldElem}, R::NfAbsOrd = maximal_order(parent(a)))
  @assert nf(R) == parent(a)
  return support(a * R)
end

function support(a::NumFieldElem, R::NfRelOrd = maximal_order(parent(a)))
  @assert nf(R) == parent(a)
  return support(a * R)
end

################################################################################
#
#   Absolute minpoly
#
################################################################################

function minpoly(a::T, ::QQField) where T <: Union{NfRelNSElem, NfRelElem}
  f = minpoly(a)
  n = absolute_norm(f)
  g = gcd(n, derivative(n))
  if isone(g)
    return n
  end
  n = divexact(n, g)
  return n
end

absolute_minpoly(a::nf_elem) = minpoly(a)
absolute_minpoly(a::NfAbsNS) = minpoly(a)

absolute_minpoly(a::T) where T <: Union{NfRelNSElem, NfRelElem} = minpoly(a, FlintQQ)
