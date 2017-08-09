type NfRelOrdElem{T} <: RingElem
  parent#::NfRelOrd{T, S} # I don't want to drag the S around
  elem_in_nf::NfRelElem{T}
  elem_in_basis::Vector{T}
  has_coord::Bool

  function NfRelOrdElem(O::NfRelOrd{T})
    z = new()
    z.parent = O
    z.elem_in_nf = zero(nf(O))
    z.elem_in_basis = Vector{T}(degree(O))
    z.has_coord = false
    return z
  end

  function NfRelOrdElem(O::NfRelOrd{T}, a::NfRelElem{T})
    z = new()
    z.parent = O
    z.elem_in_nf = a
    z.elem_in_basis = Vector{T}(degree(O))
    z.has_coord = false
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

function (O::NfRelOrd){T}(a::NfRelElem{T})
  # checks
  return NfRelOrdElem{T}(O, deepcopy(a))
end

(O::NfRelOrd)(a::Union{fmpz, Integer}) = O(nf(O)(a))

(O::NfRelOrd)() = O(nf(O)(0))

################################################################################
#
#  Parent
#
################################################################################

parent{T}(x::NfRelOrdElem{NfRelElem{T}}) = x.parent::NfRelOrd{NfRelElem{T}, NfRelOrdFracIdl{T}}

parent(x::NfRelOrdElem{nf_elem}) = x.parent::NfRelOrd{nf_elem, NfOrdFracIdl}

################################################################################
#
#  Element in number field
#
################################################################################

function elem_in_nf(a::NfRelOrdElem)
  if isdefined(a, :elem_in_nf)
    return deepcopy(a.elem_in_nf)
  end
  error("Not a valid order element")
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

one(O::NfRelOrd) = O(1)

zero(O::NfRelOrd) = O(0)

one(a::NfRelOrdElem) = parent(a)(1)

zero(a::NfRelOrdElem) = parent(a)(0)

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::NfRelOrdElem) = isone(a.elem_in_nf)

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

function *(a::NfRelOrdElem, b::NfRelOrdElem)
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf*b.elem_in_nf
  return c
end

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

################################################################################
#
#  Trace
#
################################################################################

trace(a::NfRelOrdElem) = trace(a.elem_in_nf)

################################################################################
#
#  Conversion
#
################################################################################

(K::NfRel)(a::NfRelOrdElem) = elem_in_nf(a)



# in, elem_in_basis

