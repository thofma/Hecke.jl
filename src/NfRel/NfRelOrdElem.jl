mutable struct NfRelOrdElem{T} <: RingElem
  parent#::NfRelOrd{T, S} # I don't want to drag the S around
  elem_in_nf::RelativeElement{T}
  elem_in_basis::Vector{T}
  has_coord::Bool

  function NfRelOrdElem{T}(O::NfRelOrd{T}) where {T}
    z = new{T}()
    z.parent = O
    z.elem_in_nf = zero(nf(O))
    z.elem_in_basis = Vector{T}(degree(O))
    z.has_coord = false
    return z
  end

  function NfRelOrdElem{T}(O::NfRelOrd{T}, a::RelativeElement{T}) where {T}
    z = new{T}()
    z.parent = O
    z.elem_in_nf = a
    z.elem_in_basis = Vector{T}(degree(O))
    z.has_coord = false
    return z
  end

  function NfRelOrdElem{T}(O::NfRelOrd{T}, a::RelativeElement{T}, arr::Vector{T}) where {T}
    z = new{T}()
    z.parent = O
    z.elem_in_nf = a
    z.elem_in_basis = arr
    z.has_coord = true
    return z
  end
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::NfRelOrdElem, dict::ObjectIdDict)
  z = parent(x)()
  z.elem_in_nf = Base.deepcopy_internal(x.elem_in_nf, dict)
  if x.has_coord
    z.has_coord = true
    z.elem_in_basis = Base.deepcopy_internal(x.elem_in_basis, dict)
  end
  return z
end

################################################################################
#
#  Parent object overloading
#
################################################################################

doc"""
***
      (O::NfRelOrd)(a::RelativeElement, check::Bool = true) -> NfRelOrdElem

> Given an element $a$ of the ambient number field of $\mathcal O$, this
> function coerces the element into $\mathcal O$. If `check` is `true`
> it will be checked that $a$ is contained in $\mathcal O$.
"""
function (O::NfRelOrd)(a::RelativeElement{T}, check::Bool = true) where T
  if check
    x, y = _check_elem_in_order(a, O)
    !x && error("Number field element not in the order.")
    return NfRelOrdElem{T}(O, deepcopy(a), y)
  else
    return NfRelOrdElem{T}(O, deepcopy(a))
  end
end

doc"""
***
      (O::NfRelOrd)(a::NfRelOrdElem, check::Bool = true) -> NfRelOrdElem

> Given an element $a$ of some order in the ambient number field of
> $\mathcal O$, this function coerces the element into $\mathcal O$.
> If `check` is `true` it will be checked that $a$ is contained in
> $\mathcal O$.
"""
function (O::NfRelOrd)(a::NfRelOrdElem{T}, check::Bool = true) where T
  b = nf(parent(a))(a)
  return O(b, check)
end

(O::NfRelOrd)(a::Union{fmpz, Integer}) = O(nf(O)(a))

doc"""
***
      (O::NfRelOrd)() -> NfRelOrdElem

> Constructs a new element of $\mathcal O$ which is set to $0$.
"""
(O::NfRelOrd{T, S})() where {T, S} = NfRelOrdElem{T}(O)

################################################################################
#
#  Parent
#
################################################################################

doc"""
***
      parent(a::NfRelOrdElem) -> NfRelOrd

> Returns the order of which $a$ is an element.
"""
parent(x::NfRelOrdElem{RelativeElement{T}}) where {T} = x.parent::NfRelOrd{RelativeElement{T}, NfRelOrdFracIdl{T}}

parent(x::NfRelOrdElem{nf_elem}) = x.parent::NfRelOrd{nf_elem, NfOrdFracIdl}

################################################################################
#
#  Element in number field
#
################################################################################

doc"""
***
      elem_in_nf(a::NfRelOrdElem) -> RelativeElement

> Returns the element $a$ considered as an element of the ambient number field.
"""

function elem_in_nf(a::NfRelOrdElem)
  if isdefined(a, :elem_in_nf)
    return deepcopy(a.elem_in_nf)
  end
  error("Not a valid order element.")
end

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
    a.elem_in_basis = y
    a.has_coord = true
    return nothing
  end
end

################################################################################
#
#  Coordinates
#
################################################################################

doc"""
***
      elem_in_basis(a::NfRelOrdElem{T}) -> Vector{T}

> Returns the coefficient vector of $a$.
"""
function elem_in_basis(a::NfRelOrdElem, copy::Type{Val{T}} = Val{true}) where T
  assure_has_coord(a)
  if copy == Val{true}
    return deepcopy(a.elem_in_basis)
  else
    return a.elem_in_basis
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

doc"""
***
      zero(O::NfRelOrd) -> NfRelOrdElem

> Returns the zero element of $\mathcal O$.
"""
zero(O::NfRelOrd) = O(0)

doc"""
***
      one(O::NfRelOrd) -> NfRelOrdElem

> Returns the one element of $\mathcal O$.
"""
one(O::NfRelOrd) = O(1)

doc"""
***
      zero(a::NfRelOrdElem) -> NfRelOrdElem

> Returns the zero element of the parent of $a$.
"""
zero(a::NfRelOrdElem) = parent(a)(0)

doc"""
***
      one(a::NfRelOrdElem) -> NfRelOrdElem

> Returns the one element of the parent of $a$.
"""

one(a::NfRelOrdElem) = parent(a)(1)

################################################################################
#
#  isone/iszero
#
################################################################################

doc"""
***
      isone(a::NfRelOrd) -> Bool

> Tests if $a$ is one.
"""

isone(a::NfRelOrdElem) = isone(a.elem_in_nf)

doc"""
***
      iszero(a::NfRelOrd) -> Bool

> Tests if $a$ is zero.
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

doc"""
***
      -(a::NfRelOrdElem) -> NfRelOrdElem

> Returns the additive inverse of $a$.
"""
function -(a::NfRelOrdElem)
  b = parent(a)()
  b.elem_in_nf = - a.elem_in_nf
  if a.has_coord
    b.elem_in_basis = map(x -> -x, a.elem_in_basis)
    b.has_coord = true
  end
  return b
end

################################################################################
#
#  Binary operations
#
################################################################################

doc"""
***
      *(a::NfRelOrdElem, b::NfRelOrdElem) -> NfRelOrdElem

> Returns $a \cdot b$.
"""
function *(a::NfRelOrdElem, b::NfRelOrdElem)
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf*b.elem_in_nf
  return c
end

doc"""
***
      +(a::NfRelOrdElem, b::NfRelOrdElem) -> NfRelOrdElem

> Returns $a + b$.
"""
function +(a::NfRelOrdElem, b::NfRelOrdElem)
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf + b.elem_in_nf
  if a.has_coord && b.has_coord
    c.elem_in_basis = [ a.elem_in_basis[i] + b.elem_in_basis[i] for i = 1:degree(parent(a))]
    c.has_coord = true
  end
  return c
end

doc"""
***
      -(a::NfRelOrdElem, b::NfRelOrdElem) -> NfRelOrdElem

> Returns $a - b$.
"""
function -(a::NfRelOrdElem, b::NfRelOrdElem)
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf - b.elem_in_nf
  if a.has_coord && b.has_coord
    c.elem_in_basis = [ a.elem_in_basis[i] - b.elem_in_basis[i] for i = 1:degree(parent(a))]
    c.has_coord = true
  end
  return c
end

doc"""
***
      divexact(a::NfRelOrdElem, b::NfRelOrdElem, check::Bool) -> NfRelOrdElem

> Returns $a/b$. It is assumed that $a/b$ is an element of the same order
> as $a$.
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
    doc"""
    ***
          *(a::NfRelOrdElem, b::Union{Integer, fmpz}) -> NfRelOrdElem

    > Returns $a \cdot b$.
    """
    function *(a::NfRelOrdElem, b::$T)
      c = parent(a)()
      c.elem_in_nf = a.elem_in_nf*b
      if a.has_coord
        c.elem_in_basis = map(x -> b*x, a.elem_in_basis)
        c.has_coord = true
      end
      return c
    end

    *(a::$T, b::NfRelOrdElem) = b*a

    doc"""
    ***
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

doc"""
***
    ^(a::NfRelOrdElem, b::Union{fmpz, Int}) -> NfRelOrdElem

> Returns $a^b$.
"""
function ^(a::NfRelOrdElem, b::Union{fmpz, Int})
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf^b
  return c
end

################################################################################
#
#  Trace
#
################################################################################

doc"""
***
      trace(a::NfRelOrdElem{T}) -> T

> Returns the trace of $a$.
"""
trace(a::NfRelOrdElem) = trace(a.elem_in_nf)

################################################################################
#
#  Norm
#
################################################################################

doc"""
***
      norm(a::NfRelOrdElem{T}) -> T

> Returns the norm of $a$.
"""
norm(a::NfRelOrdElem) = norm(a.elem_in_nf)

################################################################################
#
#  Conversion
#
################################################################################

(K::NfRel)(a::NfRelOrdElem) = elem_in_nf(a)

(K::NfRel_ns)(a::NfRelOrdElem) = elem_in_nf(a)

