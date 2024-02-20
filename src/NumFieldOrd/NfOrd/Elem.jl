################################################################################
#
#          AbsSimpleNumFieldOrder/Elem.jl : Elements of orders of number fields
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

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::AbsNumFieldOrderElem{S, T}, dict::IdDict) where {S, T}
  z = parent(x)()
  z.elem_in_nf = Base.deepcopy_internal(x.elem_in_nf, dict)
  if x.has_coord
    z.has_coord = true
    z.coordinates = Base.deepcopy_internal(x.coordinates, dict)::Vector{ZZRingElem}
  end
  return z
end

################################################################################
#
#  Conversion from matrix
#
################################################################################

function elem_from_mat_row(O::AbsNumFieldOrder, M::ZZMatrix, i::Int, d::ZZRingElem = ZZRingElem(1))
  return O(ZZRingElem[M[i, j] for j=1:degree(O)])
end

################################################################################
#
#  Parent object overloading
#
################################################################################

@doc raw"""
      (O::NumFieldOrder)(a::NumFieldElem, check::Bool = true) -> NumFieldOrderElem

Given an element $a$ of the ambient number field of $\mathcal O$, this
function coerces the element into $\mathcal O$. It will be checked that $a$
is contained in $\mathcal O$ if and only if `check` is `true`.
"""
(O::AbsNumFieldOrder{S, T})(a::T, check::Bool = true) where {S, T} = begin
  if nf(O) !== parent(a)
    error("Underlying number fields not equal")
  end
  if check
    (x, y) = _check_elem_in_order(a,O)
    !x && error("Number field element not in the order")
    return AbsNumFieldOrderElem(O, deepcopy(a), y)
  else
    return AbsNumFieldOrderElem(O, deepcopy(a))
  end
end

@doc raw"""
      (O::NumFieldOrder)(a::NumFieldOrderElem, check::Bool = true) -> NumFieldOrderElem

Given an element $a$ of some order in the ambient number field of
$\mathcal O$, this function coerces the element into $\mathcal O$. It
will be checked that $a$ is contained in $\mathcal O$ if and only if
`check` is `true`.
"""
(O::AbsNumFieldOrder{S, T})(a::AbsNumFieldOrderElem{S, T}, check::Bool = true) where {S, T} = begin
  b = nf(parent(a))(a)
  if check
    (x, y) = _check_elem_in_order(b,O)
    !x && error("Number field element not in the order")
    return AbsNumFieldOrderElem(O, deepcopy(b), y)
  else
    return AbsNumFieldOrderElem(O, deepcopy(b))
  end
end

(O::AbsNumFieldOrder{S, T})(a::T, arr::Vector{ZZRingElem}, check::Bool = false) where {S, T} = begin
  if check
    (x, y) = _check_elem_in_order(a,O)
    (!x || arr != y ) && error("Number field element not in the order")
    return AbsNumFieldOrderElem(O, deepcopy(a), y)
  else
    return AbsNumFieldOrderElem(O, deepcopy(a), deepcopy(arr))
  end
end

(O::AbsNumFieldOrder{S, T})(a::T, arr::ZZMatrix, check::Bool = false) where {S, T} = begin
  if check
    (x, y) = _check_elem_in_order(a,O)
    (!x || arr != y ) && error("Number field element not in the order")
    return AbsNumFieldOrderElem(O, deepcopy(a), y)
  else
    return AbsNumFieldOrderElem(O, deepcopy(a), deepcopy(arr))
  end
end

@doc raw"""
      (O::NumFieldOrder)(a::IntegerUnion) -> NumFieldOrderElem

Given an element $a$ of type `ZZRingElem` or `Integer`, this
function coerces the element into $\mathcal O$.
"""
(O::AbsNumFieldOrder)(a::IntegerUnion) = begin
  return AbsNumFieldOrderElem(O, nf(O)(a))
end

@doc raw"""
      (O::AbsNumFieldOrder)(arr::Vector{ZZRingElem})

Returns the element of $\mathcal O$ with coefficient vector `arr`.
"""
(O::AbsNumFieldOrder)(arr::Vector{ZZRingElem}) = begin
  return AbsNumFieldOrderElem(O, deepcopy(arr))
end

(O::AbsNumFieldOrder)(arr::ZZMatrix) = begin
  return AbsNumFieldOrderElem(O, arr)
end

@doc raw"""
      (O::AbsNumFieldOrder)(arr::Vector{Integer})

Returns the element of $\mathcal O$ with coefficient vector `arr`.
"""
(O::AbsNumFieldOrder)(arr::Vector{S}) where {S <: Integer} = begin
  return AbsNumFieldOrderElem(O, deepcopy(arr))
end

(O::AbsNumFieldOrder)() = AbsNumFieldOrderElem(O)

################################################################################
#
#  Parent check
#
################################################################################

function check_parent(x::AbsNumFieldOrderElem{S, T}, y::AbsNumFieldOrderElem{S, T}) where {S, T}
  return parent(x) === parent(y)
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(a::AbsNumFieldOrderElem)
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

@doc raw"""
    coordinates(a::AbsNumFieldOrderElem) -> Vector{ZZRingElem}

Returns the coefficient vector of $a$ with respect to the basis of the order.
"""
function coordinates(a::AbsNumFieldOrderElem; copy::Bool = true)
  assure_has_coord(a)
  @hassert :AbsNumFieldOrder 2 a == dot(a.coordinates, basis(parent(a), copy = false))
  if copy
    return deepcopy(a.coordinates)
  else
    return a.coordinates
  end
end

################################################################################
#
#  Characteristic and minimal polynomial
#
################################################################################

@doc raw"""
    charpoly(a::AbsNumFieldOrderElem) -> ZZPolyRingElem
    charpoly(a::AbsNumFieldOrderElem, FlintZZ) -> ZZPolyRingElem

The characteristic polynomial of $a$.
"""
function charpoly(a::AbsNumFieldOrderElem, Zx::ZZPolyRing = ZZPolyRing(FlintZZ, :x, false))
  return Zx(charpoly(elem_in_nf(a)))
end

@doc raw"""
    minpoly(a::AbsNumFieldOrderElem) -> ZZPolyRingElem

The minimal polynomial of $a$.
"""
function minpoly(a::AbsNumFieldOrderElem, Zx::ZZPolyRing = ZZPolyRing(FlintZZ, :x, false))
  return Zx(minpoly(elem_in_nf(a)))
end

################################################################################
#
#  String I/O
#
################################################################################

function AbstractAlgebra.expressify(a::AbsNumFieldOrderElem; context = nothing)
  return AbstractAlgebra.expressify(a.elem_in_nf, context = context)
end

function show(io::IO, x::AbsNumFieldOrderElem)
  print(io, AbstractAlgebra.obj_to_string(x, context = io))
end

################################################################################
#
#  Adhoc division
#
################################################################################

function //(x::AbsSimpleNumFieldElem, y::AbsSimpleNumFieldOrderElem)
  check_parent(x, y.elem_in_nf)
  return x//y.elem_in_nf
end

function //(y::AbsSimpleNumFieldOrderElem, x::AbsSimpleNumFieldElem)
  check_parent(x, y.elem_in_nf)
  return y.elem_in_nf//x
end

################################################################################
#
#  Modular reduction
#
################################################################################

function mod(a::AbsNumFieldOrderElem, m::Union{ZZRingElem, Int})
  d = degree(parent(a))
  ar = coordinates(a)
  for i in 1:d
    ar[i] = mod(a.coordinates[i], m)
  end
  return AbsNumFieldOrderElem(parent(a), ar) # avoid making a copy of ar
end


################################################################################
#
#  Modular exponentiation
#
################################################################################

function powermod(a::AbsNumFieldOrderElem, i::ZZRingElem, p::ZZRingElem)

  if is_defining_polynomial_nice(nf(parent(a))) && contains_equation_order(parent(a))
    return powermod_fast(a, i, p)
  else
    return powermod_gen(a, i, p)
  end
end

function powermod_gen(a::AbsNumFieldOrderElem, i::ZZRingElem, p::ZZRingElem)
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


function powermod_fast(a::AbsNumFieldOrderElem, i::ZZRingElem, p::ZZRingElem)
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
  e = powermod(e, i, p)

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

function powermod_fast(a::AbsNumFieldOrderElem{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}, i::ZZRingElem, p::ZZRingElem)
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
  e = powermod(e, i, p)

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

function powermod(a::AbsSimpleNumFieldOrderElem, i::ZZRingElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
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


powermod(a::AbsNumFieldOrderElem, i::Integer, m::Integer) = powermod(a, ZZRingElem(i), ZZRingElem(m))

powermod(a::AbsNumFieldOrderElem, i::ZZRingElem, m::Integer)  = powermod(a, i, ZZRingElem(m))

powermod(a::AbsNumFieldOrderElem, i::Integer, m::ZZRingElem)  = powermod(a, ZZRingElem(i), m)

################################################################################
#
#  Representation matrices
#
################################################################################

@doc raw"""
    representation_matrix(a::AbsNumFieldOrderElem) -> ZZMatrix

Returns the representation matrix of the element $a$.
"""
function representation_matrix(a::AbsNumFieldOrderElem)
  O = parent(a)
  assure_has_basis_matrix(O)
  assure_has_basis_mat_inv(O)
  A = representation_matrix(a, nf(O))
  mul!(A, O.basis_matrix, A)
  mul!(A, A, O.basis_mat_inv)
  !(A.den == 1) && error("Element not in order")
  return A.num
end

@doc raw"""
    representation_matrix(a::AbsNumFieldOrderElem, K::AbsSimpleNumField) -> FakeFmpqMat

Returns the representation matrix of the element $a$ considered as an element
of the ambient number field $K$. It is assumed that $K$ is the ambient number
field of the order of $a$.
"""
function representation_matrix(a::AbsNumFieldOrderElem{S, T}, K::S) where {S, T}
  nf(parent(a)) != K && error("Element not in this field")
  A, d = Nemo.representation_matrix_q(a.elem_in_nf)
  z = FakeFmpqMat(A, d)
  return z
end

@doc raw"""
    representation_matrix_mod(a::AbsNumFieldOrderElem, d::ZZRingElem) -> ZZMatrix

Returns the representation matrix of the element $a$ with entries reduced mod $d$.
"""
function representation_matrix_mod(a::AbsNumFieldOrderElem, d::ZZRingElem)
  O = parent(a)
  A, den = representation_matrix_q(elem_in_nf(a))
  BM = basis_matrix(FakeFmpqMat, O, copy = false)
  BMinv = basis_mat_inv(FakeFmpqMat, O, copy = false)
  d2 = BM.den * BMinv.den * den
  d2c, d2nc = ppio(d2, d)
  d1 = d * d2c
  if fits(Int, d1)
    R = residue_ring(FlintZZ, Int(d1), cached = false)[1]
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
    RR = residue_ring(FlintZZ, d1, cached = false)[1]
    ARR = map_entries(RR, A)
    BMRR = map_entries(RR, BM.num)
    mul!(ARR, BMRR, ARR)
    dv = RR(d2c)
    BMinvRR = map_entries(RR, BMinv.num)
    mul!(ARR, ARR, BMinvRR)
    inver = invmod(d2nc, d1)
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
end


################################################################################
#
#  Random element generation
#
################################################################################

# TODO: Make this faster, don't allocate the ar array ...
function rand!(z::AbsNumFieldOrderElem{S, T}, B::Vector{AbsNumFieldOrderElem{S, T}}, R) where {S, T}
  O = parent(z)
  y = O()
  for i in 1:degree(O)
    y = mul!(y, rand(R), B[i])
    z = add!(z, z, y)
  end
  return z
end

function rand!(z::AbsNumFieldOrderElem, O::AbsNumFieldOrder, R::AbstractUnitRange{T}) where T <: Integer
  y = O()
  B = basis(O, copy = false)
  for i in 1:degree(O)
    y = mul!(y, rand(R), B[i])
    z = add!(z, z, y)
  end
  return z
end

@doc raw"""
    rand(O::AbsSimpleNumFieldOrder, R::AbstractUnitRange{Integer}) -> AbsNumFieldOrderElem

Computes a coefficient vector with entries uniformly distributed in `R` and returns
the corresponding element of the order.
"""
function rand(O::AbsSimpleNumFieldOrder, R::AbstractUnitRange{T}) where T <: Integer
  z = O()
  rand!(z, O, R)
  return z
end

function rand!(z::AbsNumFieldOrderElem, O::AbsSimpleNumFieldOrder, n::IntegerUnion)
  return rand!(z, O, -n:n)
end

@doc raw"""
    rand(O::AbsSimpleNumFieldOrder, n::IntegerUnion) -> AbsNumFieldOrderElem

Computes a coefficient vector with entries uniformly distributed in
$\{-n,\dotsc,-1,0,1,\dotsc,n\}$ and returns the corresponding element of the
order $\mathcal O$.
"""
function rand(O::AbsSimpleNumFieldOrder, n::Integer)
  return rand(O, -n:n)
end

function rand(O::AbsSimpleNumFieldOrder, n::ZZRingElem)
  z = O()
  rand!(z, O, BigInt(n))
  return z
end

function rand!(z::AbsNumFieldOrderElem, O::AbsSimpleNumFieldOrder, n::ZZRingElem)
  return rand!(z, O, BigInt(n))
end

################################################################################
#
#  Conversion
#
################################################################################

(K::AbsSimpleNumField)(x::AbsSimpleNumFieldOrderElem) = elem_in_nf(x)

(K::AbsNonSimpleNumField)(x::AbsNumFieldOrderElem{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}) = elem_in_nf(x)

################################################################################
#
#  Factorization
#
################################################################################

@doc raw"""
    factor(a::AbsSimpleNumFieldOrderElem) -> Fac{AbsSimpleNumFieldOrderElem}

Computes a factorization of $a$ into irreducible elements. The return value
is a factorization `fac`, which satisfies `a = unit(fac) * prod(p^e for (p, e)
in fac)`.

The function requires that $a$ is non-zero and that all prime ideals containing
$a$ are principal, which is for example satisfied if class group of the order
of $a$ is trivial.
"""
function factor(a::AbsSimpleNumFieldOrderElem)
  iszero(a) && error("Element must be non-zero")
  OK = parent(a)
  I = a * OK
  D = Dict{AbsSimpleNumFieldOrderElem, Int}()
  u = a
  for (p, e) in factor(I)
    b, c = is_principal_with_data(p)
    !b && error("Prime ideal dividing the element not principal")
    D[c] = e
    u = divexact(u, c^e)
  end
  return Nemo.Fac(u, D)
end
