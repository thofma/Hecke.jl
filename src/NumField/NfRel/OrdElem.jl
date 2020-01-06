################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::NfRelOrdElem, dict::IdDict)
  z = parent(x)()
  z.elem_in_nf = Base.deepcopy_internal(x.elem_in_nf, dict)
  if x.has_coord
    z.has_coord = true
    z.coordinates = Base.deepcopy_internal(x.coordinates, dict)
  end
  return z
end

################################################################################
#
#  Parent object overloading
#
################################################################################

@doc Markdown.doc"""
      (O::NfRelOrd)(a::NumFieldElem, check::Bool = true) -> NfRelOrdElem

Given an element $a$ of the ambient number field of $\mathcal O$, this
function coerces the element into $\mathcal O$. If `check` is `true`
it will be checked that $a$ is contained in $\mathcal O$.
"""
function (O::NfRelOrd)(a::NumFieldElem{T}, check::Bool = true) where T
  if check
    x, y = _check_elem_in_order(a, O)
    !x && error("Number field element not in the order.")
    return NfRelOrdElem{T}(O, deepcopy(a), y)
  else
    return NfRelOrdElem{T}(O, deepcopy(a))
  end
end

@doc Markdown.doc"""
      (O::NfRelOrd)(a::NfRelOrdElem, check::Bool = true) -> NfRelOrdElem

Given an element $a$ of some order in the ambient number field of
$\mathcal O$, this function coerces the element into $\mathcal O$.
If `check` is `true` it will be checked that $a$ is contained in
$\mathcal O$.
"""
(O::NfRelOrd)(a::NfRelOrdElem{T}, check::Bool = true) where {T} = O(nf(O)(a.elem_in_nf), check)

function (O::NfRelOrd)(a::Vector{T}, check::Bool = true) where T
  t = nf(O)()
  basis = basis_nf(O, copy = false)
  for i = 1:degree(O)
    t += a[i]*basis[i]
  end
  s = O(t, check)
  s.coordinates = a
  s.has_coord = true
  return s
end

(O::NfRelOrd)(a::NfOrdElem, check::Bool = true) = O(nf(O)(a.elem_in_nf), check)

(O::NfRelOrd)(a::Union{fmpz, Integer}) = O(nf(O)(a))

@doc Markdown.doc"""
      (O::NfRelOrd)() -> NfRelOrdElem

Constructs a new element of $\mathcal O$ which is set to $0$.
"""
(O::NfRelOrd{T, S})() where {T, S} = NfRelOrdElem{T}(O)

################################################################################
#
#  Parent
#
################################################################################

@doc Markdown.doc"""
      parent(a::NfRelOrdElem) -> NfRelOrd

Returns the order of which $a$ is an element.
"""
parent(x::NfRelOrdElem{T}) where {T <: NumFieldElem{S} where {S}} = x.parent

parent(x::NfRelOrdElem{nf_elem}) = x.parent

################################################################################
#
#  Element in number field
#
################################################################################

@doc Markdown.doc"""
      elem_in_nf(a::NfRelOrdElem) -> NumFieldElem

Returns the element $a$ considered as an element of the ambient number field.
"""

function elem_in_nf(a::NfRelOrdElem; copy::Bool = true)
  if isdefined(a, :elem_in_nf)
    if copy
      return deepcopy(a.elem_in_nf)
    else
      return a.elem_in_nf
    end
  end
  error("Not a valid order element.")
end

_elem_in_algebra(a; copy::Bool = true) = elem_in_nf(a, copy = copy)

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(a::NfRelOrdElem)
  if a.has_coord
    return nothing
  else
    x, y = _check_elem_in_order(a.elem_in_nf, parent(a))
    !x && error("Not a valid order element.")
    a.coordinates = y
    a.has_coord = true
    return nothing
  end
end

################################################################################
#
#  Coordinates
#
################################################################################

@doc Markdown.doc"""
      coordinates(a::NfRelOrdElem{T}) -> Vector{T}

Returns the coefficient vector of $a$.
"""
function coordinates(a::NfRelOrdElem; copy::Bool = true)
  assure_has_coord(a)
  if copy
    return deepcopy(a.coordinates)
  else
    return a.coordinates
  end
end

################################################################################
#
#  Equality
#
################################################################################

==(a::Hecke.NfRelOrdElem, b::Hecke.NfRelOrdElem) = parent(a) == parent(b) && a.elem_in_nf == b.elem_in_nf

################################################################################
#
#  Special elements
#
################################################################################

@doc Markdown.doc"""
      zero(O::NfRelOrd) -> NfRelOrdElem

Returns the zero element of $\mathcal O$.
"""
zero(O::NfRelOrd) = O(0)

@doc Markdown.doc"""
      one(O::NfRelOrd) -> NfRelOrdElem

Returns the one element of $\mathcal O$.
"""
one(O::NfRelOrd) = O(1)

@doc Markdown.doc"""
      zero(a::NfRelOrdElem) -> NfRelOrdElem

Returns the zero element of the parent of $a$.
"""
zero(a::NfRelOrdElem) = parent(a)(0)

@doc Markdown.doc"""
      one(a::NfRelOrdElem) -> NfRelOrdElem

Returns the one element of the parent of $a$.
"""

one(a::NfRelOrdElem) = parent(a)(1)

################################################################################
#
#  isone/iszero
#
################################################################################

@doc Markdown.doc"""
      isone(a::NfRelOrd) -> Bool

Tests if $a$ is one.
"""

isone(a::NfRelOrdElem) = isone(a.elem_in_nf)

@doc Markdown.doc"""
      iszero(a::NfRelOrd) -> Bool

Tests if $a$ is zero.
"""

iszero(a::NfRelOrdElem) = iszero(a.elem_in_nf)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfRelOrdElem)
  print(io, a.elem_in_nf)
end

################################################################################
#
#  Unary operations
#
################################################################################

@doc Markdown.doc"""
      -(a::NfRelOrdElem) -> NfRelOrdElem

Returns the additive inverse of $a$.
"""
function -(a::NfRelOrdElem)
  b = parent(a)()
  b.elem_in_nf = - a.elem_in_nf
  if a.has_coord
    b.coordinates = map(x -> -x, a.coordinates)
    b.has_coord = true
  end
  return b
end

################################################################################
#
#  Binary operations
#
################################################################################

@doc Markdown.doc"""
      *(a::NfRelOrdElem, b::NfRelOrdElem) -> NfRelOrdElem

Returns $a \cdot b$.
"""
function *(a::NfRelOrdElem, b::NfRelOrdElem)
  check_parent(a, b)
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf*b.elem_in_nf
  return c
end

@doc Markdown.doc"""
      +(a::NfRelOrdElem, b::NfRelOrdElem) -> NfRelOrdElem

Returns $a + b$.
"""
function +(a::NfRelOrdElem, b::NfRelOrdElem)
  check_parent(a, b)
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf + b.elem_in_nf
  if a.has_coord && b.has_coord
    c.coordinates = [ a.coordinates[i] + b.coordinates[i] for i = 1:degree(parent(a))]
    c.has_coord = true
  end
  return c
end

@doc Markdown.doc"""
      -(a::NfRelOrdElem, b::NfRelOrdElem) -> NfRelOrdElem

Returns $a - b$.
"""
function -(a::NfRelOrdElem, b::NfRelOrdElem)
  check_parent(a, b)
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf - b.elem_in_nf
  if a.has_coord && b.has_coord
    c.coordinates = [ a.coordinates[i] - b.coordinates[i] for i = 1:degree(parent(a))]
    c.has_coord = true
  end
  return c
end

@doc Markdown.doc"""
      divexact(a::NfRelOrdElem, b::NfRelOrdElem, check::Bool) -> NfRelOrdElem

Returns $a/b$. It is assumed that $a/b$ is an element of the same order
as $a$.
"""
function divexact(a::NfRelOrdElem, b::NfRelOrdElem, check::Bool = true)
  t = divexact(a.elem_in_nf, b.elem_in_nf)
  if check
    if !in(t, parent(a))
      error("Quotient not an element of the order.")
    end
  end
  c = parent(a)(t)
  return c
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

for T in [Integer, fmpz]
  @eval begin
    @doc Markdown.doc"""
              *(a::NfRelOrdElem, b::Union{Integer, fmpz}) -> NfRelOrdElem

    > Returns $a \cdot b$.
    """
    function *(a::NfRelOrdElem, b::$T)
      c = parent(a)()
      c.elem_in_nf = a.elem_in_nf*b
      if a.has_coord
        c.coordinates = map(x -> b*x, a.coordinates)
        c.has_coord = true
      end
      return c
    end

    *(a::$T, b::NfRelOrdElem) = b*a

    @doc Markdown.doc"""
              divexact(a::NfRelOrdElem, b::Union{Integer, fmpz}, check::Bool) -> NfRelOrdElem

    > Returns $a/b$. It is assumed that $a/b$ is an element of the same order
    > as $a$.
    """
    function divexact(a::NfRelOrdElem, b::$T, check::Bool = true)
      t = divexact(a.elem_in_nf, b)
      if check
        if !in(t, parent(a))
          error("Quotient not an element of the order.")
        end
      end
      c  = parent(a)(t)
      return c
    end
  end
end

################################################################################
#
#  Exponentiation
#
################################################################################

@doc Markdown.doc"""
    ^(a::NfRelOrdElem, b::Union{fmpz, Int}) -> NfRelOrdElem

Returns $a^b$.
"""
function ^(a::NfRelOrdElem, b::Union{fmpz, Int})
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf^b
  return c
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function add!(c::NfRelOrdElem, a::NfRelOrdElem, b::NfRelOrdElem)
  c.elem_in_nf = add!(c.elem_in_nf, a.elem_in_nf, b.elem_in_nf)
  c.has_coord = false
  return c
end

function mul!(c::NfRelOrdElem, a::NfRelOrdElem, b::NfRelOrdElem)
  c.elem_in_nf = mul!(c.elem_in_nf, a.elem_in_nf, b.elem_in_nf)
  c.has_coord = false
  return c
end

################################################################################
#
#  Trace
#
################################################################################

@doc Markdown.doc"""
      tr(a::NfRelOrdElem{T}) -> T

Returns the trace of $a$.
"""
tr(a::NfRelOrdElem) = base_ring(parent(a))(tr(a.elem_in_nf))

################################################################################
#
#  Norm
#
################################################################################

@doc Markdown.doc"""
      norm(a::NfRelOrdElem{T}) -> T

Returns the norm of $a$.
"""
norm(a::NfRelOrdElem) = base_ring(parent(a))(norm(a.elem_in_nf))

norm(a::NfRelOrdElem, k::Union{ NfRel, AnticNumberField, NfRelNS, FlintRationalField }) = norm(a.elem_in_nf, k)

absolute_norm(a::NfRelOrdElem) = FlintZZ(absolute_norm(a.elem_in_nf))

################################################################################
#
#  Conversion
#
################################################################################

(K::NfRel)(a::NfRelOrdElem) = elem_in_nf(a)

(K::NfRelNS)(a::NfRelOrdElem) = elem_in_nf(a)

################################################################################
#
#  Representation matrix
#
################################################################################

function representation_matrix(a::NfRelOrdElem)
  O = parent(a)
  A = representation_matrix(elem_in_nf(a))
  A = basis_matrix(O, copy = false)*A*basis_mat_inv(O, copy = false)
  return A
end
