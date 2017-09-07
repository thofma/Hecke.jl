mutable struct NfRelOrdFracIdlSet{T, S}
  order::NfRelOrd{T, S}

  function NfRelOrdFracIdlSet{T, S}(O::NfRelOrd{T, S}) where {T, S}
    a = new(O)
    return a
  end
end

mutable struct NfRelOrdFracIdl{T, S}
  order::NfRelOrd{T, S}
  parent::NfRelOrdFracIdlSet{T, S}
  num::NfRelOrdIdl{T, S}
  den_abs::NfOrdElem # used if T == nf_elem
  den_rel::NfRelOrdElem # used otherwise

  norm
  has_norm::Bool

  function NfRelOrdFracIdl{T, S}(O::NfRelOrd{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdFracIdlSet{T, S}(O)
    z.has_norm = false
    return z
  end

  function NfRelOrdFracIdl{nf_elem, S}(O::NfRelOrd{nf_elem, S}, a::NfRelOrdIdl{nf_elem, S}, d::NfOrdElem) where S
    z = new{nf_elem, S}()
    z.order = O
    z.parent = NfRelOrdFracIdlSet{nf_elem, S}(O)
    z.num = a
    z.den_abs = d
    z.has_norm = false
    return z
  end

  function NfRelOrdFracIdl{T, S}(O::NfRelOrd{T, S}, a::NfRelOrdIdl{T, S}, d::NfRelOrdElem) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdFracIdlSet{T, S}(O)
    z.num = a
    z.den_rel = d
    z.has_norm = false
    return z
  end
end

################################################################################
#
#  Basic field access
#
################################################################################

doc"""
***
    order(a::NfRelOrdFracIdl) -> NfRelOrd

> Returns the order of $a$.
"""
order(a::NfRelOrdFracIdl) = a.order

doc"""
***
    nf(a::NfRelOrdFracIdl) -> NfRel

> Returns the number field, of which $a$ is an fractional ideal.
"""
nf(a::NfRelOrdFracIdl) = nf(order(a))

################################################################################
#
#  Parent
#
################################################################################

parent(a::NfRelOrdFracIdl) = a.parent

################################################################################
#
#  Numerator and denominator
#
################################################################################

num(a::NfRelOrdFracIdl) = a.num

den(a::NfRelOrdFracIdl{nf_elem, S}) where {S} = a.den_abs

den(a::NfRelOrdFracIdl{T, S}) where {S, T} = a.den_rel

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, s::NfRelOrdFracIdlSet)
  print(io, "Set of fractional ideals of ")
  print(io, s.order)
end

function show(io::IO, a::NfRelOrdFracIdl)
  print(io, "Fractional ideal of (")
  print(io, order(a), ")\n")
  print(io, "with basis pseudo-matrix\n")
  print(io, basis_pmat(num(a)), "\n")
  print(io, "and denominator ", den(a))
end

################################################################################
#
#  Construction
#
################################################################################

doc"""
***
    frac_ideal(O::NfRelOrd, a::NfRelOrdIdl, d::NfOrdElem) -> NfRelOrdFracIdl
    frac_ideal(O::NfRelOrd, a::NfRelOrdIdl, d::NfRelOrdElem) -> NfRelOrdFracIdl

> Creates the fractional ideal $a/d$ of $\mathcal O$.
"""
function frac_ideal(O::NfRelOrd{nf_elem, S}, a::NfRelOrdIdl{nf_elem, S}, d::NfOrdElem) where S
  return NfRelOrdFracIdl{nf_elem, S}(O, a, d)
end

function frac_ideal(O::NfRelOrd{T, S}, a::NfRelOrdIdl{T, S}, d::NfRelOrdElem{T}) where {T, S}
  return NfRelOrdFracIdl{T, S}(O, a, d)
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::NfRelOrdFracIdl{T, S}, dict::ObjectIdDict) where {T, S}
  z = NfRelOrdFracIdl{T, S}(a.order)
  for x in fieldnames(a)
    if x != :order && x != :parent && isdefined(a, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(a, x), dict))
    end
  end
  z.order = a.order
  z.parent = a.parent
  return z
end

################################################################################
#
#  Equality
#
################################################################################

doc"""
***
    ==(a::NfOrdRelFracIdl, b::NfRelOrdFracIdl) -> Bool

> Returns whether $a$ and $b$ are equal.
"""
function ==(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl)
  order(a) != order(b) && return false
  return den(a) == den(b) && num(a) == num(b)
end

################################################################################
#
#  Norm
#
################################################################################

function assure_has_norm(a::NfRelOrdFracIdl)
  if a.has_norm
    return nothing
  end
  n = norm(num(a))
  d = den(a)^degree(order(a))
  a.norm = n*inv(nf(parent(den(a)))(d))
  a.has_norm = true
  return nothing
end

doc"""
***
    norm(a::NfRelOrdFracIdl{T, S}) -> S

> Returns the norm of $a$
"""
function norm(a::NfRelOrdFracIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_norm(a)
  if copy == Val{true}
    return deepcopy(a.norm)
  else
    return a.norm
  end
end

################################################################################
#
#  Ideal addition
#
################################################################################

doc"""
***
    +(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl) -> NfRelOrdFracIdl

> Returns $a + b$.
"""
function +(a::NfRelOrdFracIdl{T, S}, b::NfRelOrdFracIdl{T, S}) where {T, S}
  K = nf(parent(den(a)))
  da = K(den(a))
  db = K(den(b))
  d = divexact(da*db, gcd(da, db))
  ma = divexact(d, da)
  mb = divexact(d, db)
  c = ma*num(a) + mb*num(b)
  return NfRelOrdFracIdl{T, S}(order(a), c, parent(den(a))(d))
end

################################################################################
#
#  Ideal multiplication
#
################################################################################

doc"""
    *(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl)

> Returns $a \cdot b$.
"""
function *(a::NfRelOrdFracIdl{T, S}, b::NfRelOrdFracIdl{T, S}) where {T, S}
  return NfRelOrdFracIdl{T, S}(order(a), num(a)*num(b), den(a)*den(b))
end
