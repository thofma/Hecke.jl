export absolute_degree, absolute_discriminant

################################################################################
#
#  Base field
#
################################################################################

@doc doc"""
    base_field(L::NumField) -> NumField

Given a number field $L/K$ this function returns the base field $K$.
For absolute extensions this returns $\mathbf{Q}$.
"""
base_field(::NumField)

_base_ring(K::NumField) = base_field(K)

_base_ring(::FlintRationalField) = FlintQQ

################################################################################
#
#  Predicates
#
################################################################################

export is_absolute

@doc doc"""
    is_absolute(L::NumField) -> Bool

Returns whether $L$ is an absolute extension, that is, whether the base field
of $L$ is $\mathbf{Q}$.
"""
is_absolute(::NumField)

is_absolute(::NumField) = false

is_absolute(::NumField{fmpq}) = true

################################################################################
#
#  Degree
#
################################################################################

@doc doc"""
    degree(L::NumField) -> Int

Given a number field $L/K$, this function returns the degree of $L$ over $K$.

# Examples

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = NumberField(x^2 - 2, "a");

julia> degree(K)
2
```
"""
degree(A::NumField)

dim(K::NumField) = degree(K)

################################################################################
#
#  Absolute degree
#
################################################################################

@doc doc"""
    absolute_degree(L::NumField) -> Int

Given a number field $L/K$, this function returns the degree of $L$ over
$\mathbf Q$.
"""
function absolute_degree(A::NumField)
  return absolute_degree(base_field(A)) * degree(A)
end

function absolute_degree(K::NumField{fmpq})
  return degree(K)
end

absolute_degree(::FlintRationalField) = 1

################################################################################
#
#  Is simple extension
#
################################################################################

@doc doc"""
    is_simple(L::NumField) -> Bool

Given a number field $L/K$ this function returns whether $L$ is simple, that is,
whether $L/K$ is defined by a univariate polynomial.
"""
is_simple(a::NumField)

################################################################################
#
#  Number field creation
#
################################################################################

@doc doc"""
    NumberField(f::Poly{NumFieldElem}, s::String;
                cached::Bool = false, check::Bool = false) -> NumField, NumFieldElem

Given an irreducible polynomial $f \in K[x]$ over some number field $K$, this
function creates the simple number field $L = K[x]/(f)$ and returns $(L, b)$,
where $b$ is the class of $x$ in $L$. The string `s` is used only for printing
the primitive element $b$.

- `check`: Controls whether irreducibility of $f$ is checked.
- `cached`: Controls whether the result is cached.

# Examples

```jldoctest
julia> K, a = quadratic_field(5);

julia> Kt, t = K["t"];

julia> L, b = NumberField(t^3 - 3, "b");
```
"""
function _doc_stub_nf end

# To work around a bug in the built documentation.

abstract type DocuDummy end

@doc (@doc _doc_stub_nf)
NumberField(::DocuDummy)

@doc (@doc _doc_stub_nf)
NumberField(f::PolyElem{<: NumFieldElem}, s::String;
            cached::Bool = false, check::Bool = false)

################################################################################
#
#  Is commutative
#
################################################################################

is_commutative(K::NumField) = true
is_commutative(::FlintRationalField) = true

################################################################################
#
#  Normal basis
#
################################################################################

@doc doc"""
    normal_basis(L::NumField) -> NumFieldElem

Given a normal number field $L/K$, this function returns an element $a$ of $L$,
such that the orbit of $a$ under the Galois group of $L/K$ is an $K$-basis
of $L$.
"""
function normal_basis(L::NumField)
  n = degree(L)
  K = base_field(L)
  Aut = automorphisms(L)

  @req length(Aut) != degree(L) "The field must be normal over its base field"

  A = zero_matrix(K, n, n)
  r = one(L)
  while true
    r = rand(basis(L), -n:n)
    for i = 1:n
      y = Aut[i](r)
      for j = 1:n
        A[i,j] = coeff(y, j - 1)
      end
    end
    if rank(A) == n
      break
    end
  end
  return r
end

function is_normal_basis_generator(a::NumFieldElem)
  L = parent(a)
  n = degree(L)
  K = base_field(L)
  Aut = automorphisms(L)

  @req length(Aut) != degree(L) "The field must be normal over its base field"

  A = zero_matrix(K, n, n)
  for i = 1:n
    y = Aut[i](a)
    for j = 1:n
      A[i,j] = coeff(y, j - 1)
    end
  end
  return rank(A) == n
end

#trivia to make life easier

gens(L::SimpleNumField{T}) where {T} = [gen(L)]

function gen(L::SimpleNumField{T}, i::Int) where {T}
  i == 1 || error("index must be 1")
  return gen(L)
end

gen(L::NonSimpleNumField{T}, i::Int) where {T} = L(gen(parent(L.pol[1]), i))

function Base.getindex(L::SimpleNumField{T}, i::Int) where {T}
  if i == 0
    return one(L)
  elseif i == 1
    return gen(L)
  else
    error("index has to be 0 or 1")
  end
end

ngens(L::SimpleNumField{T}) where {T} = 1

function Base.getindex(L::NonSimpleNumField{T}, i::Int) where {T}
  i == 0 && return one(L)
  return gen(L, i)
end

function is_cached(L::AnticNumberField)
  if haskey(Nemo.AnticNumberFieldID, (parent(L.pol), L.pol, L.S))
    return Nemo.AnticNumberFieldID[parent(L.pol), L.pol, L.S] === L
  end
  return false
end

function is_cached(L::NfRel)
  if haskey(NfRelID, (parent(L.pol), L.pol, L.S))
    return NfRelID[parent(L.pol), L.pol, L.S] === L
  end
  return false
end

is_cached(L::NonSimpleNumField) = false

export set_var!, set_vars!

#the Symbol is part of the key for caching, hence it should be be changed
@doc doc"""
    set_var!(L::SimpleNumField, s::String)
    set_var!(L::SimpleNumField, s::Symbol)

Sets the name used when printing the primitive element of $L$.
This can only be set on fields constructed using `cached = false`.
"""
function set_var!(L::SimpleNumField{T}, s::String) where {T}
  is_cached(L) && error("cannot set the name in a cached field")
  L.S = Symbol(s)
  nothing
end

function set_var!(L::SimpleNumField{T}, s::Symbol) where {T}
  is_cached(L) && error("cannot set the name in a cached field")
  L.S = s
  nothing
end

@doc doc"""
    set_vars!(L::NonSimpleNumField{T}, a::String)
    set_vars!(L::NonSimpleNumField{T}, a::Symbol)

Sets the string printed for each generator of the field. If the string contains
'#', then the hash-character is replaced by the index, otherwise, the index is
appended to the string.  Eg. `set_vars!(L, "g[#]")` will make the generators
print like array elements.
"""
function set_vars!(L::NonSimpleNumField{T}, a::Symbol) where {T}
  return set_vars!(L, String(a))
end

function set_vars!(L::NonSimpleNumField{T}, a::String) where {T}
  n = ngens(L)
  if occursin('#', a)
    S = [replace(a, '#'=>"$i") for i=1:n]
  else
    S = ["$a$i" for i=1:n]
  end
  return set_vars!(L, S)
end

@doc doc"""
    set_vars!(L::NonSimpleNumField{T}, a::Vector{String})
    set_vars!(L::NonSimpleNumField{T}, a::Vector{Symbol})

Set the printing names for the generators to the string specified in
the array. The length has to be exactly `ngens(L)`.
"""
function set_vars!(L::NonSimpleNumField{T}, a::Vector{String}) where {T}
  length(a) == ngens(L) || error("need to have as many strings as generators")
  L.S = [Symbol(s) for s = a]
  nothing
end

function set_vars!(L::NonSimpleNumField{T}, a::Vector{Symbol}) where {T}
  length(a) == ngens(L) || error("need to have as many strings as generators")
  L.S = a
  nothing
end

is_cyclotomic_type(K::NonSimpleNumField{T}) where {T} = false, fmpz(1)
is_cyclotomic_type(K::NfRel) = false, fmpz(1)
function is_cyclotomic_type(L::AnticNumberField)
  f = get_attribute(L, :cyclo)
  if f === nothing
    return false, fmpz(1)
  end
  return true, f
end

is_quadratic_type(K::NonSimpleNumField{T}) where {T} = false, fmpz(1)
is_quadratic_type(K::NfRel) = false, fmpz(1)
function is_quadratic_type(L::AnticNumberField)
  f = get_attribute(L, :show)
  if f === Hecke.show_quad
    return true, numerator(-coeff(L.pol, 0))
  end
  return false, fmpz(1)
end

################################################################################
#
#  Absolute basis
#
################################################################################

@doc doc"""
    absolute_basis(K::NumField) -> Vector{NumFieldElem}

Returns an array of elements that form a basis of $K$ (as a vector space)
over the rationals.
"""
absolute_basis(::NumField)

function absolute_basis(K::NumField)
  k = base_field(K)
  kabs = absolute_basis(k)
  B = basis(K)
  res = Vector{elem_type(K)}(undef, absolute_degree(K))
  ind = 1
  for b in basis(K)
    for bb in kabs
      res[ind] = bb * b
      ind += 1
    end
  end
  return res
end

function absolute_basis(K::NumField{fmpq})
  return basis(K)
end

################################################################################
#
#  Discriminant sign
#
################################################################################

@doc doc"""
    discriminant_sign(K::NumField) -> Int

Returns the sign of the discriminant of the maximal order of $K$.
"""
function discriminant_sign(K::NumField)
# Compute the sign using Brill's theorem
  _, s = signature(K)
  if mod(s, 2) == 0
    return 1
  else
    return -1
  end
end

################################################################################
#
#  Unit group rank
#
################################################################################

@doc Markdown.doc"""
    unit_group_rank(K::NumField) -> Int

Return the rank of the unit group of any order of $K$.
"""
function unit_group_rank(K::NumField)
  r1, r2 = signature(K)
  return r1 + r2 - 1
end

################################################################################
#
#  Signature
#
################################################################################

@doc doc"""
    signature(K::NumField)

Return the signature of the number field of $K$.

# Examples
```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = NumberField(x^2 - 2, "a");

julia> signature(K)
(2, 0)
```
"""
function signature(K::NumField) end

################################################################################
#
#  Infinite places
#
################################################################################

@doc Markdown.doc"""
    infinite_places(K::NumField) -> Vector{Plc}

This function returns all infinite places of $K$.

# Examples

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = NumberField(x^2 - 2, "a");

julia> infinite_places(K)
2-element Vector{InfPlc}:
 Real place of
Number field over Rational Field with defining polynomial x^2 - 2
corresponding to the root [-1.414213562373095049 +/- 3.90e-19]
 Real place of
Number field over Rational Field with defining polynomial x^2 - 2
corresponding to the root [1.414213562373095049 +/- 3.90e-19]
```
"""
function infinite_places(::NumField) end

@doc doc"""
    isreal(P::Plc)

Return whether the embedding into $\mathbf{C}$ defined by $P$ is real or not.
"""
function isreal(::Plc) end

@doc Markdown.doc"""
    is_complex(P::Plc) -> Bool

Return whether the embedding into $\mathbf{C}$ defined by $P$ is complex or not.
"""
function is_complex(::Plc) end

################################################################################
#
#  Is abelian
#
################################################################################

@doc doc"""
    is_abelian(L::NumField) -> Bool

Check if the number field $L/K$ is abelian over $K$.  The function is
probabilistic and assumes GRH.
"""
function is_abelian(::NumField) end

################################################################################
#
#  Automorphisms
#
################################################################################

@doc doc"""
    automorphisms(L::NumField) -> Vector{NumFieldMor}

Given a number field $L/K$, return a list of all $K$-automorphisms of $L$.
"""
function automorphisms(L::NumField) end

################################################################################
#
#  Appears as a base_field?
#
################################################################################

function _appears_as_base_field(K::NumField, L::NumField)
  if K === base_field(L)
    return true
  else
    return _appears_as_base_field(K, base_field(L))
  end
end

function _appears_as_base_field(K::NumField, ::AnticNumberField)
  return false
end

function _appears_as_base_field(K::NumField, ::NfAbsNS)
  return false
end
