################################################################################
#
#          NfOrd/Elem.jl : Elements of orders of number fields
#
# This file is part of hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

export ==, +, -, *, ^, add!, conjugates_arb, conjugates_arb_log, discriminant,
       divexact, elem_in_nf, coordinates, isone, iszero, minkowski_map, mod,
       mul!, norm, one, parent, powermod, rand, rand!, representation_matrix,
       show, trace, t2, zero

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::NfAbsOrdElem{S, T}, dict::IdDict) where {S, T}
  z = parent(x)()
  z.elem_in_nf = Base.deepcopy_internal(x.elem_in_nf, dict)
  if x.has_coord
    z.has_coord = true
    z.coordinates = Base.deepcopy_internal(x.coordinates, dict)::Vector{fmpz}
  end
  return z
end

################################################################################
#
#  Conversion from matrix
#
################################################################################

function elem_from_mat_row(O::NfAbsOrd, M::fmpz_mat, i::Int, d::fmpz = fmpz(1))
  return O(fmpz[M[i, j] for j=1:degree(O)])
end

################################################################################
#
#  Parent object overloading
#
################################################################################

@doc Markdown.doc"""
      (O::NfOrd)(a::nf_elem, check::Bool = true) -> NfAbsOrdElem

Given an element $a$ of the ambient number field of $\mathcal O$, this
function coerces the element into $\mathcal O$. It will be checked that $a$
is contained in $\mathcal O$ if and only if `check` is `true`.
"""
(O::NfAbsOrd{S, T})(a::T, check::Bool = true) where {S, T} = begin
  if nf(O) !== parent(a)
    throw(error("Underlying number fields not equal"))
  end
  if check
    (x, y) = _check_elem_in_order(a,O)
    !x && error("Number field element not in the order")
    return NfAbsOrdElem(O, deepcopy(a), y)
  else
    return NfAbsOrdElem(O, deepcopy(a))
  end
end

@doc Markdown.doc"""
      (O::NfOrd)(a::NfAbsOrdElem, check::Bool = true) -> NfAbsOrdElem

Given an element $a$ of some order in the ambient number field of
$\mathcal O$, this function coerces the element into $\mathcal O$. It
will be checked that $a$ is contained in $\mathcal O$ if and only if
`check` is `true`.
"""
(O::NfAbsOrd{S, T})(a::NfAbsOrdElem{S, T}, check::Bool = true) where {S, T} = begin
  b = nf(parent(a))(a)
  if check
    (x, y) = _check_elem_in_order(b,O)
    !x && error("Number field element not in the order")
    return NfAbsOrdElem(O, deepcopy(b), y)
  else
    return NfAbsOrdElem(O, deepcopy(b))
  end
end

(O::NfAbsOrd{S, T})(a::T, arr::Vector{fmpz}, check::Bool = false) where {S, T} = begin
  if check
    (x, y) = _check_elem_in_order(a,O)
    (!x || arr != y ) && error("Number field element not in the order")
    return NfAbsOrdElem(O, deepcopy(a), y)
  else
    return NfAbsOrdElem(O, deepcopy(a), deepcopy(arr))
  end
end

@doc Markdown.doc"""
      (O::NfOrd)(a::Union{fmpz, Integer}) -> NfAbsOrdElem

Given an element $a$ of type `fmpz` or `Integer`, this
function coerces the element into $\mathcal O$. It will be checked that $a$
is contained in $\mathcal O$ if and only if `check` is `true`.
"""
(O::NfAbsOrd)(a::Union{fmpz, Integer}) = begin
  return NfAbsOrdElem(O, nf(O)(a))
end

@doc Markdown.doc"""
      (O::NfOrd)(arr::Array{fmpz, 1})

Returns the element of $\mathcal O$ with coefficient vector `arr`.
"""
(O::NfAbsOrd)(arr::Array{fmpz, 1}) = begin
  return NfAbsOrdElem(O, deepcopy(arr))
end

@doc Markdown.doc"""
      (O::NfOrd)(arr::Array{Integer, 1})

Returns the element of $\mathcal O$ with coefficient vector `arr`.
"""
(O::NfAbsOrd)(arr::Array{S, 1}) where {S <: Integer} = begin
  return NfAbsOrdElem(O, deepcopy(arr))
end

@doc Markdown.doc"""
      (O::NfOrd)() -> NfAbsOrdElem

This function constructs a new element of $\mathcal O$ which is set to $0$.
"""
(O::NfAbsOrd)() = NfAbsOrdElem(O)

################################################################################
#
#  Parent
#
################################################################################

@doc Markdown.doc"""
    parent(a::NfAbsOrdElem) -> NfOrd

Returns the order of which $a$ is an element.
"""
parent(a::NfAbsOrdElem) = a.parent

################################################################################
#
#  Parent check
#
################################################################################

function check_parent(x::NfAbsOrdElem{S, T}, y::NfAbsOrdElem{S, T}) where {S, T}
  return parent(x) === parent(y)
end

################################################################################
#
#  Element in number field
#
################################################################################

@doc Markdown.doc"""
    elem_in_nf(a::NfAbsOrdElem) -> nf_elem

Returns the element $a$ considered as an element of the ambient number field.
"""
function elem_in_nf(a::NfAbsOrdElem; copy::Bool = true)
  if isdefined(a, :elem_in_nf)
    if copy
      return deepcopy(a.elem_in_nf)
    else
      return a.elem_in_nf
    end
  end
  error("Not a valid order element")
end

_elem_in_algebra(a::NfAbsOrdElem; copy::Bool = true) = elem_in_nf(a, copy = copy)

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(a::NfAbsOrdElem)
  if a.has_coord
    return nothing
  else
    (x, y) = _check_elem_in_order(a.elem_in_nf, parent(a))
    !x && error("Not a valid order element")
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
    coordinates(a::NfAbsOrdElem) -> Array{fmpz, 1}

Returns the coefficient vector of $a$.
"""
function coordinates(a::NfAbsOrdElem; copy::Bool = true)
  assure_has_coord(a)
  @hassert :NfOrd 2 a == dot(a.coordinates, basis(parent(a), copy = false))
  if copy
    return deepcopy(a.coordinates)
  else
    return a.coordinates
  end
end

################################################################################
#
#  Discriminant
#
################################################################################

@doc Markdown.doc"""
    discriminant(B::Array{NfAbsOrdElem, 1}) -> fmpz

Returns the discriminant of the family $B$.
"""
function discriminant(B::Array{NfAbsOrdElem{S, T}, 1}) where {S, T}
  length(B) == 0 && error("Number of elements must be non-zero")
  length(B) != degree(parent(B[1])) &&
        error("Number of elements must be $(degree(parent(B[1])))")
  O = parent(B[1])
  A = zero_matrix(FlintZZ, degree(O), degree(O))
  for i in 1:degree(O)
    el = tr(B[i]^2)
    A[i, i] = el
    for j in 1:degree(O)
      el = tr(B[i] * B[j])
      A[i, j] = el
      A[j, i] = el
    end
  end
  return det(A)
end

################################################################################
#
#  Hashing
#
################################################################################

Base.hash(x::NfAbsOrdElem, h::UInt) = Base.hash(x.elem_in_nf, h)

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
    ==(x::NfAbsOrdElem, y::NfAbsOrdElem) -> Bool

Returns whether $x$ and $y$ are equal.
"""
 ==(x::NfAbsOrdElem, y::NfAbsOrdElem) = parent(x) === parent(y) &&
                                            x.elem_in_nf == y.elem_in_nf

################################################################################
#
#  Characteristic and minimal polynomial
#
################################################################################
@doc Markdown.doc"""
    charpoly(a::NfAbsOrdElem) -> fmpz_poly

    charpoly(a::NfAbsOrdElem, FlintZZ) -> fmpz_poly
The characteristic polynomial of $a$.
"""
function charpoly(a::NfAbsOrdElem, Zx::FmpzPolyRing = FmpzPolyRing(FlintZZ, :x, false))
  return Zx(charpoly(elem_in_nf(a)))
end

@doc Markdown.doc"""
    minpoly(a::NfAbsOrdElem) -> fmpz_poly
The minimal polynomial of $a$.
"""
function minpoly(a::NfAbsOrdElem, Zx::FmpzPolyRing = FmpzPolyRing(FlintZZ, :x, false))
  return Zx(minpoly(elem_in_nf(a)))
end

################################################################################
#
#  Special elements
#
################################################################################

@doc Markdown.doc"""
    zero(O::NfOrd) -> NfAbsOrdElem

Returns the zero element of $\mathcal O$.
"""
zero(O::NfAbsOrd) = O(fmpz(0))

@doc Markdown.doc"""
    one(O::NfOrd) -> NfAbsOrdElem

Returns the one element of $\mathcal O$.
"""
one(O::NfAbsOrd) = O(fmpz(1))

@doc Markdown.doc"""
    zero(a::NfAbsOrdElem) -> NfAbsOrdElem

Returns the zero element of the parent of $a$.
"""
zero(a::NfAbsOrdElem) = parent(a)(0)

@doc Markdown.doc"""
    one(O::NfOrd) -> NfAbsOrdElem

Returns the one element of the parent of $a$.
"""
one(a::NfAbsOrdElem) = one(parent(a))

################################################################################
#
#  isone/iszero
#
################################################################################

@doc Markdown.doc"""
    isone(a::NfOrd) -> Bool

Tests if $a$ is one.
"""
isone(a::NfAbsOrdElem) = isone(a.elem_in_nf)

@doc Markdown.doc"""
    iszero(a::NfOrd) -> Bool

Tests if $a$ is zero.
"""
iszero(a::NfAbsOrdElem) = iszero(a.elem_in_nf)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfAbsOrdElem)
  print(io, a.elem_in_nf)
end

################################################################################
#
#  Unary operations
#
################################################################################

@doc Markdown.doc"""
    -(x::NfAbsOrdElem) -> NfAbsOrdElem

Returns the additive inverse of $x$.
"""
function -(x::NfAbsOrdElem)
  z = parent(x)()
  z.elem_in_nf = - x.elem_in_nf
  if x.has_coord
    z.coordinates = map(y -> -y, x.coordinates)
    z.has_coord = true
  end
  return z
end

###############################################################################
#
#  Binary operations
#
###############################################################################

@doc Markdown.doc"""
    *(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem

Returns $x \cdot y$.
"""
function *(x::NfAbsOrdElem{S, T}, y::NfAbsOrdElem{S, T}) where {S, T}
  !check_parent(x, y) && error("Wrong parents")
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf*y.elem_in_nf
  return z
end

@doc Markdown.doc"""
    +(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem

Returns $x + y$.
"""
function +(x::NfAbsOrdElem, y::NfAbsOrdElem)
  !check_parent(x, y) && error("Wrong parents")
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  if x.has_coord && y.has_coord
    z.coordinates =
      [ x.coordinates[i] + y.coordinates[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

@doc Markdown.doc"""
    -(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem

Returns $x - y$.
"""
function -(x::NfAbsOrdElem, y::NfAbsOrdElem)
  !check_parent(x, y) && error("Wrong parents")
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y.elem_in_nf
  if x.has_coord && y.has_coord
    z.coordinates =
      [ x.coordinates[i] - y.coordinates[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

@doc Markdown.doc"""
    divexact(x::NfAbsOrdElem, y::NfAbsOrdElem, check::Bool) -> NfAbsOrdElem

Returns $x/y$. It is assumed that $x/y$ is an element of the same order
as $x$.
"""
function divexact(x::NfAbsOrdElem, y::NfAbsOrdElem, check::Bool = true)
  !check_parent(x, y) && error("Wrong parents")
  a = divexact(x.elem_in_nf, y.elem_in_nf)
  if check
    if !in(a, parent(x))
      error("Quotient not an element of the order")
    end
  end
  z = parent(x)()
  z.elem_in_nf = a
  return z
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

function *(x::NfAbsOrdElem, y::Integer)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf * y
  if x.has_coord
    z.coordinates = map(z -> y*z, x.coordinates)
    z.has_coord = true
  end
  return z
end

*(x::Integer, y::NfAbsOrdElem) = y * x

function *(x::NfAbsOrdElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf * y
  if x.has_coord
    z.coordinates = map(z -> y*z, x.coordinates)
    z.has_coord = true
  end
  return z
end

*(x::fmpz, y::NfAbsOrdElem) = y * x

for T in [Integer, fmpz]
  @eval begin
    function +(x::NfAbsOrdElem, y::$T)
      z = parent(x)()
      z.elem_in_nf = x.elem_in_nf + y
      return z
    end

    +(x::$T, y::NfAbsOrdElem) = y + x

    function -(x::NfAbsOrdElem, y::$T)
      z = parent(x)()
      z.elem_in_nf = x.elem_in_nf - y
      return z
    end

    function -(x::$T, y::NfAbsOrdElem)
      z = parent(y)()
      z.elem_in_nf = x - y.elem_in_nf
      return z
    end
  end
end

################################################################################
#
#  Adhoc exact division
#
################################################################################

for T in [Integer, fmpz]
  @eval begin
    function divexact(x::NfAbsOrdElem, y::$T, check::Bool = true)
      a = divexact(x.elem_in_nf, y)
      if check
        if !in(a, parent(x))
          error("Quotient not an element of the order")
        end
      end
      z = parent(x)()
      z.elem_in_nf = a
      return z
    end
  end
end

################################################################################
#
#  Adhoc division
#
################################################################################

function //(x::nf_elem, y::NfOrdElem)
  check_parent(x, y.elem_in_nf)
  return x//y.elem_in_nf
end

function //(y::NfOrdElem, x::nf_elem)
  check_parent(x, y.elem_in_nf)
  return y.elem_in_nf//x
end

################################################################################
#
#  Exponentiation
#
################################################################################

@doc Markdown.doc"""
    ^(x::NfAbsOrdElem, y::Int)

Returns $x^y$.
"""
function ^(x::NfAbsOrdElem, y::Int)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf^y
  return z
end

################################################################################
#
#  Modular reduction
#
################################################################################

@doc Markdown.doc"""
    mod(a::NfAbsOrdElem, m::Union{fmpz, Int}) -> NfAbsOrdElem

Reduces the coefficient vector of $a$ modulo $m$ and returns the corresponding
element. The coefficient vector of the result will have entries $x$ with
$0 \leq x \leq m$.
"""
function mod(a::NfAbsOrdElem, m::Union{fmpz, Int})
  d = degree(parent(a))
  ar = coordinates(a)
  for i in 1:d
    ar[i] = mod(a.coordinates[i], m)
  end
  return NfAbsOrdElem(parent(a), ar) # avoid making a copy of ar
end


################################################################################
#
#  Modular exponentiation
#
################################################################################

@doc Markdown.doc"""
    powermod(a::NfAbsOrdElem, i::fmpz, m::Union{fmpz, Int}) -> NfAbsOrdElem

Returns an element $a^i$ modulo $m$.
"""
function powermod(a::NfAbsOrdElem, i::fmpz, p::fmpz)

  #if contains_equation_order(parent(a))#This doesn't work!
  if isdefining_polynomial_nice(nf(parent(a)))
    return powermod_fast(a, i, p)
  else
    return powermod_gen(a, i, p)
  end
end

function powermod_gen(a::NfAbsOrdElem, i::fmpz, p::fmpz)
  if i == 0
    return one(parent(a))
  end
  if i == 1
    b = mod(a,p)
    return b
  end
  if mod(i,2) == 0
    j = div(i, 2)
    b = powermod(a, j, p)
    b = b^2
    b = mod(b,p)
    return b
  end
  b = mod(a * powermod(a, i - 1, p), p)
  return b
end


function powermod_fast(a::NfAbsOrdElem, i::fmpz, p::fmpz)
  if i == 0
    return one(parent(a))
  end
  if i == 1
    bb = mod(a, p)
    return bb
  end

  b = a.elem_in_nf
  d = denominator(b)
  f, e = ppio(d, p) # f = p^k, and e is a unit mod p
  b *= e
  e = invmod(e, p)
  e = powmod(e, i, p)

  y = one(parent(b))
  while i > 1
    if iszero(b)
      return zero(parent(a))
    end
    if iseven(i)
      b = mod(b*b, p)
    else
      y = mod(b*y, p)
      b = mod(b*b, p)
    end
    i = div(i, 2)
  end
  b = mod(b*y, p)

  return mod(parent(a)(b)*e, p)
end

function powermod_fast(a::NfAbsOrdElem{NfAbsNS, NfAbsNSElem}, i::fmpz, p::fmpz)
  if i == 0
    return one(parent(a))
  end
  if i == 1
    bb = mod(a, p)
    return bb
  end

  b = a.elem_in_nf
  d = denominator(b)
  f, e = ppio(d, p) # f = p^k, and e is a unit mod p
  b *= e
  e = invmod(e, p)
  e = powmod(e, i, p)

  y = one(parent(b))
  while i > 1
    if iszero(b)
      return zero(parent(a))
    end
    if iseven(i)
      mul!(b, b, b)
      mod!(b, p)
      #b = mod(b*b, p)
    else
      mul!(y, b, y)
      mod!(y, p)
      #y = mod(b*y, p)
      mul!(b, b, b)
      mod!(b, p)
      #b = mod(b*b, p)
    end
    i = div(i, 2)
  end
  mul!(b, b, y)
  mod!(b, p)
  #b = mod(b*y, p)

  return mod(parent(a)(b*e), p)
end

@doc Markdown.doc"""
    powermod(a::NfAbsOrdElem, i::fmpz, m::Union{fmpz, Int}) -> NfAbsOrdElem

Returns an element $a^i$ modulo $m$.
"""
function powermod(a::NfOrdElem, i::fmpz, I::NfOrdIdl)
  if i == 0
    return one(parent(a))
  end
  b = mod(a, I)
  if i == 1
    return b
  end
  if iszero(b)
    return b
  end
  y = one(parent(b))
  while i > 1
    if iseven(i)
      b = mod(b*b, I)
    else
      y = mod(b*y, I)
      b = mod(b*b, I)
    end
    i = div(i, 2)
  end
  b = mod(b*y, I)

  return mod(b, I)
end


@doc Markdown.doc"""
    powermod(a::NfAbsOrdElem, i::Integer, m::Integer) -> NfAbsOrdElem

Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfAbsOrdElem, i::Integer, m::Integer) = powermod(a, fmpz(i), fmpz(m))

@doc Markdown.doc"""
    powermod(a::NfAbsOrdElem, i::fmpz, m::Integer) -> NfAbsOrdElem

Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfAbsOrdElem, i::fmpz, m::Integer)  = powermod(a, i, fmpz(m))

@doc Markdown.doc"""
    powermod(a::NfAbsOrdElem, i::Integer, m::fmpz) -> NfAbsOrdElem

Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfAbsOrdElem, i::Integer, m::fmpz)  = powermod(a, fmpz(i), m)

################################################################################
#
#  Representation matrices
#
################################################################################

@doc Markdown.doc"""
    representation_matrix(a::NfAbsOrdElem) -> fmpz_mat

Returns the representation matrix of the element $a$.
"""
function representation_matrix(a::NfAbsOrdElem)
  O = parent(a)
  assure_has_basis_matrix(O)
  assure_has_basis_mat_inv(O)
  A = representation_matrix(a, nf(O))
  mul!(A, O.basis_matrix, A)
  mul!(A, A, O.basis_mat_inv)
  !(A.den == 1) && error("Element not in order")
  return A.num
end

@doc Markdown.doc"""
    representation_matrix(a::NfAbsOrdElem, K::AnticNumberField) -> FakeFmpqMat

Returns the representation matrix of the element $a$ considered as an element
of the ambient number field $K$. It is assumed that $K$ is the ambient number
field of the order of $a$.
"""
function representation_matrix(a::NfAbsOrdElem{S, T}, K::S) where {S, T}
  nf(parent(a)) != K && error("Element not in this field")
  A, d = Nemo.representation_matrix_q(a.elem_in_nf)
  A.base_ring = FlintZZ
  z = FakeFmpqMat(A, d)
  return z
end

@doc Markdown.doc"""
    representation_matrix_mod(a::NfAbsOrdElem, d::fmpz) -> fmpz_mat

Returns the representation matrix of the element $a$ with entries reduced mod $d$.
"""
function representation_matrix_mod(a::NfAbsOrdElem, d::fmpz)
  O = parent(a)
  A, den = representation_matrix_q(elem_in_nf(a))
  BM = basis_matrix(O, copy = false)
  BMinv = basis_mat_inv(O, copy = false)
  d2 = BM.den * BMinv.den * den
  d2c, d2nc = ppio(d2, d)
  d1 = d * d2c
  if fits(Int, d1)
    R = ResidueRing(FlintZZ, Int(d1), cached = false)
    AR = map_entries(R, A)
    BMR = map_entries(R, BM.num)
    BMinvR = map_entries(R, BMinv.num)
    mul!(AR, BMR, AR)
    mul!(AR, AR, BMinvR)
    inver = invmod(d2nc, d1)
    mul!(AR, AR, R(inver))
    dv = R(d2c)
    for i = 1:nrows(AR)
      for j = 1:ncols(AR)
        if !iszero(AR[i, j])
          AR[i, j] = divexact(AR[i, j], dv)
        end
      end
    end
    res = lift!(A, AR)
    mod!(res, d)
    return res
  else
    RR = ResidueRing(FlintZZ, d1, cached = false)
    ARR = map_entries(RR, A)
    BMRR = map_entries(RR, BM.num)
    
    mul!(ARR, BMRR, ARR) 
    #=  
    c = gcd(lift(content(ARR)), d1)
    if !isone(c)
      d3 = divexact(d1, c)
      RR = ResidueRing(FlintZZ, d3, cached = false)
      for i = 1:nrows(ARR)
        for j = 1:ncols(ARR)
          if !iszero(ARR[i, j])
            ARR[i, j] = divexact(ARR[i, j], c)
          end
        end
      end
      ARR = map_entries(RR, lift(ARR))
      BMinvRR = map_entries(RR, BMinv.num)
      dv = RR(divexact(d2c, gcd(d2c, c)))
    else
    =#
      dv = RR(d2c)
      BMinvRR = map_entries(RR, BMinv.num)
    #end
    mul!(ARR, ARR, BMinvRR)
    inver = invmod(d2nc, d1)
    #mul!(ARR, ARR, RR(inver))
    ARR *= inver
    for i = 1:nrows(ARR)
      for j = 1:ncols(ARR)
        if !iszero(ARR[i, j])
          ARR[i, j] = divexact(ARR[i, j], dv)
        end
      end
    end
    res1 = lift(ARR)
    mod!(res1, d)
    return res1
  end
  #=
  A1 = A 
  mod!(A1, d1)
  M1 = mod(BM.num, d1)
  mul!(A1, M1, A1)
  M2 = mod(BMinv.num, d1)
  mul!(A1, A1, M2)
  mod!(A1, d1)
  divexact!(A1, A1, d2c)
  inver = invmod(d2nc, d1)
  mul!(A1, A1, inver)
  mod!(A1, d)
  return A1
  =#
end

################################################################################
#
#  Trace
#
################################################################################

@doc Markdown.doc"""
    tr(a::NfAbsOrdElem) -> fmpz

Returns the trace of $a$.
"""
function tr(a::NfAbsOrdElem)
  return FlintZZ(tr(a.elem_in_nf))
end

################################################################################
#
#  Norm
#
################################################################################

@doc Markdown.doc"""
    norm(a::NfAbsOrdElem) -> fmpz

Returns the norm of $a$.
"""
function norm(a::NfAbsOrdElem)
  return FlintZZ(norm(a.elem_in_nf))
end

################################################################################
#
#  Random element generation
#
################################################################################

# TODO: Make this faster, don't allocate the ar array ...
function rand!(z::NfAbsOrdElem{S, T}, B::Vector{NfAbsOrdElem{S, T}}, R) where {S, T}
  O = parent(z)
  y = O()
  for i in 1:degree(O)
    mul!(y, rand(R), B[i])
    add!(z, z, y)
  end
  return z
end

function rand!(z::NfAbsOrdElem, O::NfAbsOrd, R::UnitRange{T}) where T <: Integer
  y = O()
  ar = rand(R, degree(O))
  B = basis(O, copy = false)
  for i in 1:degree(O)
    mul!(y, rand(R), B[i])
    add!(z, z, y)
  end
  return z
end

@doc Markdown.doc"""
    rand(O::NfOrd, R::UnitRange{Integer}) -> NfAbsOrdElem

Computes a coefficient vector with entries uniformly distributed in `R` and returns
the corresponding element of the order.
"""
function rand(O::NfOrd, R::UnitRange{T}) where T <: Integer
  z = O()
  rand!(z, O, R)
  return z
end

function rand!(z::NfAbsOrdElem, O::NfOrd, n::Union{Integer, fmpz})
  return rand!(z, O, -n:n)
end

@doc Markdown.doc"""
    rand(O::NfOrd, n::Union{Integer, fmpz}) -> NfAbsOrdElem

Computes a coefficient vector with entries uniformly distributed in
$\{-n,\dotsc,-1,0,1,\dotsc,n\}$ and returns the corresponding element of the
order $\mathcal O$.
"""
function rand(O::NfOrd, n::Integer)
  return rand(O, -n:n)
end

function rand(O::NfOrd, n::fmpz)
  z = O()
  rand!(z, O, BigInt(n))
  return z
end

function rand!(z::NfAbsOrdElem, O::NfOrd, n::fmpz)
  return rand!(z, O, BigInt(n))
end

################################################################################
#
#  Unsafe operations
#
################################################################################

@inline function add!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::NfAbsOrdElem)
  add!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

@inline function sub!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::NfAbsOrdElem)
  sub!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

@inline function mul!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::NfAbsOrdElem)
  mul!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

function addeq!(z::NfAbsOrdElem, x::NfAbsOrdElem)
  addeq!(z.elem_in_nf, x.elem_in_nf)
  if x.has_coord && z.has_coord
    for i in 1:degree(parent(z))
      add!(z.coordinates[i], z.coordinates[i], x.coordinates[i])
    end
  end
  return z
end

################################################################################
#
#  Unsafe ad hoc operations
#
################################################################################

# ad hoc
for T in [Integer, fmpz]
  @eval begin
    @inline function mul!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::$T)
      z.elem_in_nf = mul!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    mul!(z::NfAbsOrdElem, x::$T, y::NfAbsOrdElem) = mul!(z, y, x)
  end
end

for T in [Integer, fmpz]
  @eval begin
    @inline function add!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::$T)
      z.elem_in_nf = add!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    add!(z::NfAbsOrdElem, x::$T, y::NfAbsOrdElem) = add!(z, y, x)
  end
end

for T in [Integer, fmpz]
  @eval begin
    @inline function sub!(z::NfAbsOrdElem, x::NfAbsOrdElem, y::$T)
      z.elem_in_nf = sub!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    sub!(z::NfAbsOrdElem, x::$T, y::NfAbsOrdElem) = add!(z, y, x)
  end
end

################################################################################
#
#  Base cases for dot product of vectors
#
################################################################################

dot(x::NfAbsOrdElem, y::Integer) = x * y

dot(x::Integer, y::NfAbsOrdElem) = y * x

dot(x::NfAbsOrdElem, y::fmpz) = x * y

dot(x::fmpz, y::NfAbsOrdElem) = y * x

################################################################################
#
#  Conversion
#
################################################################################

(K::AnticNumberField)(x::NfAbsOrdElem{AnticNumberField, nf_elem}) = elem_in_nf(x)

(K::NfAbsNS)(x::NfAbsOrdElem{NfAbsNS, NfAbsNSElem}) = elem_in_nf(x)

################################################################################
#
#  Minkowski embedding
#
################################################################################

@doc Markdown.doc"""
    minkowski_map(a::NfAbsOrdElem, abs_tol::Int) -> Array{arb, 1}

Returns the image of $a$ under the Minkowski embedding.
Every entry of the array returned is of type `arb` with radius less then
`2^-abs_tol`.
"""
function minkowski_map(a::NfAbsOrdElem, abs_tol::Int = 32)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return minkowski_map(a.elem_in_nf, abs_tol)
end

################################################################################
#
#  Conjugates
#
################################################################################

@doc Markdown.doc"""
    conjugates_arb(x::NfAbsOrdElem, abs_tol::Int) -> Array{acb, 1}

Compute the conjugates of `x` as elements of type `acb`.
Recall that we order the complex conjugates
$\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
$\sigma_{i}(x) = \overline{\sigma_{i + s}(x)}$ for $r + 2 \leq i \leq r + s$.
>
Every entry `y` of the array returned satisfies `radius(real(y)) < 2^-abs_tol`,
`radius(imag(y)) < 2^-abs_tol` respectively.
"""
function conjugates_arb(x::NfAbsOrdElem, abs_tol::Int = 32)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return conjugates_arb(x.elem_in_nf, abs_tol)
end

@doc Markdown.doc"""
    conjugates_arb_log(x::NfAbsOrdElem, abs_tol::Int) -> Array{arb, 1}

Returns the elements
$(\log(\lvert \sigma_1(x) \rvert),\dotsc,\log(\lvert\sigma_r(x) \rvert),
\dotsc,2\log(\lvert \sigma_{r+1}(x) \rvert),\dotsc,
2\log(\lvert \sigma_{r+s}(x)\rvert))$ as elements of type `arb` radius
less then `2^-abs_tol`.
"""
function conjugates_arb_log(x::NfAbsOrdElem, abs_tol::Int = 32)
  return conjugates_arb_log(x.elem_in_nf, abs_tol)
end

################################################################################
#
#  T2
#
################################################################################

@doc Markdown.doc"""
    t2(x::NfAbsOrdElem, abs_tol::Int = 32) -> arb

Return the $T_2$-norm of $x$. The radius of the result will be less than
`2^-abs_tol`.
"""
function t2(x::NfAbsOrdElem, abs_tol::Int = 32)
  return t2(x.elem_in_nf, abs_tol)
end

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule(::Type{NfAbsOrdElem{S, T}}, ::Type{U}) where {S, T, U <: Integer} = NfAbsOrdElem{S, T}

Nemo.promote_rule(::Type{NfAbsOrdElem{S, T}}, ::Type{fmpz}) where {S, T} = NfAbsOrdElem{S, T}

Nemo.promote_rule(::Type{NfAbsOrdElem{S, T}}, ::Type{T}) where {S, T} = T

Nemo.promote_rule(::Type{T}, ::Type{NfAbsOrdElem{S, T}}) where {S, T} = T

################################################################################
#
#  Factorization
#
################################################################################

@doc Markdown.doc"""
    factor(a::NfOrdElem) -> Fac{NfOrdElem}

Computes a factorization of `a` into irreducible elements. The return value
is a factorization `fac`, which satisfies `a = unit(fac) * prod(p^e for (p, e)
in fac)`.

The function requires that `a` is non-zero and that all prime ideals containing
`a` are principal, which is for example satisfied if class group of the order
of `a` is trivial.
"""
function factor(a::NfOrdElem)
  iszero(a) && throw(error("Element must be non-zero"))
  OK = parent(a)
  I = a * OK
  D = Dict{NfOrdElem, Int}()
  u = a
  for (p, e) in factor(I)
    b, c = isprincipal(p)
    !b && throw(error("Prime ideal dividing the element not principal"))
    D[c] = e
    u = divexact(u, c^e)
  end
  return Nemo.Fac(u, D)
end
