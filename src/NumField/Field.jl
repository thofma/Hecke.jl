################################################################################
#
#  Base field
#
################################################################################

@doc Markdown.doc"""
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

export isabsolute

@doc Markdown.doc"""
    isabsolute(L::NumField) -> Bool

Returns whether $L$ is an absolute extension, that is, whether the base field
of $L$ is $\mathbf{Q}$.
"""
isabsolute(::NumField)

isabsolute(::NumField) = false

isabsolute(::NumField{fmpq}) = true

@doc Markdown.doc"""
    elem_type(L::NumField) -> Type

Returns the type of the elements of $L$.
"""
elem_type(::NumField)

################################################################################
#
#  Degree
#
################################################################################

@doc Markdown.doc"""
    degree(L::NumField) -> Int 

Given a number field $L/K$, this function returns the degree of $L$ over $K$.
"""
degree(A::NumField)

dim(K::NumField) = degree(K)

################################################################################
#
#  Absolute degree
#
################################################################################

@doc Markdown.doc"""
    absolute_degree(L::NumField) -> Int 

Given a number field $L/K$, this function returns the degree of $L$ over
$\mathbf Q$.
"""
function absolute_degree(A::NumField)
  b = base_field(A)
  if isa(b, NumField)
    return absolute_degree(base_field(A)) * degree(A)
  else
    return degree(A)
  end
end

################################################################################
#
#  Is simple extension
#
################################################################################

@doc Markdown.doc"""
    issimple(L::NumField) -> Bool

Given a number field $L/K$ this function returns whether $L$ is simple, that is,
whether $L/K$ is defined by a univariate polynomial$.
"""
issimple(a::NumField)

################################################################################
#
#  Number field creation
#
################################################################################

@doc Markdown.doc"""
    NumberField(f::Poly{NumFieldElem}, s::String;
                cached::Bool = false, check::Bool = false) -> NumField, NumFieldElem

Given an irreducible polynomial $f \in K[x]$ over some number field $K$, this
function creates the simple number field $L = K[x]/(x)$ and returns $(L, b)$,
where $b$ is the class of $x$ in $L$. The string `s` is used only for printing
the primitive element $b$.

Testing that $f$ is irreducible can be disabled by setting the keyword argument
`check` to `false`.
"""
NumberField(f::PolyElem{<:NumFieldElem}, s::String;
            cached::Bool = false, check::Bool = false) 

################################################################################
#
#  Is commutative
#
################################################################################

iscommutative(K::NumField) = true
iscommutative(::FlintRationalField) = true

################################################################################
#
#  Absolute field
#
################################################################################

@doc Markdown.doc"""
    absolute_field(L::NumField) -> NumField, Map

Given a number field $L$, this function returns an absolute simple number field
$M/\mathbf{Q}$ together with a $\mathbf{Q}$-linear isomorphism $M \to K$.
"""
absolute_field(::NumField)

################################################################################
# 
#  Normal basis
#
################################################################################

@doc Markdown.doc"""
    normal_basis(L::NumField) -> NumFieldElem

Given a normal number field $L/K$, this function returns an element $a$ of $L$,
such that the orbit of $a$ under the Galois group of $L/K$ is an $K$-basis
of $L$.
"""
function normal_basis(L::NumField)
  n = degree(L)
  K = base_field(L)
  Aut = automorphisms(L)

  length(Aut) != degree(L) && error("The field is not normal over the rationals!")

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

function isnormal_basis_generator(a::NumFieldElem)
  L = parent(a)
  n = degree(L)
  K = base_field(L)
  Aut = automorphisms(L)

  length(Aut) != degree(L) && error("The field is not normal over the rationals!")

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

function iscached(L::AnticNumberField)
  if haskey(Nemo.AnticNumberFieldID, (parent(L.pol), L.pol, L.S))
    return Nemo.AnticNumberFieldID[parent(L.pol), L.pol, L.S] === L
  end
  return false
end

function iscached(L::NfRel)
  if haskey(NfRelID, (parent(L.pol), L.pol, L.S))
    return NfRelID[parent(L.pol), L.pol, L.S] === L
  end
  return false
end

iscached(L::NonSimpleNumField) = false

export set_var!, set_vars!

#the Symbol is part of the key for caching, hence it should be be changed
@doc Markdown.doc"""
    set_var!(L::SimpleNumField, s::String)
    set_var!(L::SimpleNumField, s::Symbol)

Sets the name used when printing the primitive element of $L$.
This can only be set on fields constructed using `cached = false`
"""
function set_var!(L::SimpleNumField{T}, s::String) where {T}
  iscached(L) && error("cannot set the name in a cached field")
  L.S = Symbol(s)
  nothing
end

function set_var!(L::SimpleNumField{T}, s::Symbol) where {T}
  iscached(L) && error("cannot set the name in a cached field")
  L.S = s
  nothing
end
@doc Markdown.doc"""
    set_vars!(L::NonSimpleNumField{T}, a::String)
    set_vars!(L::NonSimpleNumField{T}, a::Symbol)

Sets the string printed for each generator of the field. If the
string contains '#', then the hash-character is replaced by the index,
otherwise, the index is appended to the string.
Eg. `set_vars!(L, "g[#]")` will make the generators print like
array elements.
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

@doc Markdown.doc"""
    set_vars!(L::NonSimpleNumField{T}, a::Array{String, 1})
    set_vars!(L::NonSimpleNumField{T}, a::Array{Symbol, 1})

Set the printing names for the generators to the string specified in
the array. The length has to be exactly `ngens(L)`
"""
function set_vars!(L::NonSimpleNumField{T}, a::Array{String, 1}) where {T}
  length(a) == ngens(L) || error("need to have as many strings as generators")
  L.S = [Symbol(s) for s = a]
  nothing
end

function set_vars!(L::NonSimpleNumField{T}, a::Array{Symbol, 1}) where {T}
  length(a) == ngens(L) || error("need to have as many strings as generators")
  L.S = a
  nothing
end

iscyclotomic_type(K::NonSimpleNumField{T}) where {T} = false, fmpz(1)
iscyclotomic_type(K::NfRel) = false, fmpz(1)
function iscyclotomic_type(L::AnticNumberField)
  f = get_special(L, :cyclo)
  if f === nothing
    return false, fmpz(1)
  end
  return true, f
end

isquadratic_type(K::NonSimpleNumField{T}) where {T} = false, fmpz(1)
isquadratic_type(K::NfRel) = false, fmpz(1)
function isquadratic_type(L::AnticNumberField)
  f = get_special(L, :show)
  if f === Hecke.show_quad
    return true, numerator(-coeff(L.pol, 0))
  end
  return false, fmpz(1)
end






