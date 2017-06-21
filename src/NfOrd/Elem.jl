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

export deepcopy, call, parent, elem_in_nf, elem_in_basis, discriminant, hash,
       ==, zero, one, iszero, isone, show, -, +, *, divexact, ^, mod, powermod,
       representation_mat, trace, norm, rand, rand!, add!, mul!, minkowski_map,
       conjugates_arb, conjugates_arb_log, t2

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::NfOrdElem, dict::ObjectIdDict)
  z = parent(x)()
  z.elem_in_nf = deepcopy(x.elem_in_nf)
  if x.has_coord
    z.has_coord = true
    z.elem_in_basis = fmpz[ deepcopy(y) for y in x.elem_in_basis ]
  end
  return z
end

################################################################################
#
#  Parent object overloading
#
################################################################################

#if VERSION < v"0.5.0-"
#  doc"""
#  #      call(O::NfOrd, a::nf_elem, check::Bool = true) -> NfOrdElem
#
#  > Given an element $a$ of the ambient number field of $\mathcal O$, this
#  > function coerces the element into $\mathcal O$. It will be checked that $a$
#  > is contained in $\mathcal O$ if and only if `check` is `true`.
#  """
#  Base.call{T <: NfOrd}(O::T, a::nf_elem, check::Bool = true) = nothing
#
#  for T in (:NfOrdGen, :NfMaxOrd)
#    @eval begin
#      function Base.call(O::$T, a::nf_elem, check::Bool = true)
#        if check
#          (x,y) = _check_elem_in_order(a,O)
#          !x && error("Number field element not in the order")
#          return NfOrdElem{$T}(O, deepcopy(a), fmpz[ deepcopy(x) for x in y])
#        else
#          return NfOrdElem{$T}(O, deepcopy(a))
#        end
#      end
#    end
#  end
#
#  doc"""
#  #      call(O::NfOrd, a::Union{fmpz, Integer}) -> NfOrdElem
#
#  > Given an element $a$ of type `fmpz` or `Integer`, this
#  > function coerces the element into $\mathcal O$. It will be checked that $a$
#  > is contained in $\mathcal O$ if and only if `check` is `true`.
#  """
#  Base.call{T <: NfOrd}(O::T, a::Union{fmpz, Integer}) = nothing
#
#  for T in (:NfOrdGen, :NfMaxOrd)
#    @eval begin
#      function Base.call(O::$T, a::Union{fmpz, Integer})
#        return NfOrdElem{$T}(O, nf(O)(a))
#      end
#    end
#  end
#
#  doc"""
#  #      call(O::NfOrd, arr::Array{fmpz, 1})
#
#  > Returns the element of $\mathcal O$ with coefficient vector `arr`.
#  """
#  Base.call{T <: NfOrd}(O::T, a::Array{fmpz, 1}) = nothing
#
#  for T in (:NfOrdGen, :NfMaxOrd)
#    @eval begin
#      function Base.call(O::$T, arr::Array{fmpz, 1})
#        return NfOrdElem{$T}(O, fmpz[ deepcopy(x) for x in arr ])
#      end
#    end
#  end
#
#
#  doc"""
#  #      call{T <: Integer}(O::NfOrd, arr::Array{T, 1})
#
#  > Returns the element of $\mathcal O$ with coefficient vector `arr`.
#  """
#  Base.call{T <: NfOrd, S <: Integer}(O::T, arr::Array{S, 1}) = nothing
#
#  for T in (:NfOrdGen, :NfMaxOrd)
#    @eval begin
#      function Base.call{S <: Integer}(O::$T, arr::Array{S, 1})
#        return NfOrdElem{$T}(O, deepcopy(arr))
#      end
#    end
#  end
#
#  doc"""
#  #      call(O::NfOrd, a::nf_elem, arr::Array{fmpz, 1}) -> NfOrdElem
#
#  > This function constructs the element of $\mathcal O$ with coefficient vector
#  > `arr`. It is assumed that the corresponding element of the ambient number
#  > field is $a$.
#  """
#  Base.call{T <: NfOrd}(O::T, a::nf_elem, arr::Array{fmpz, 1}) = nothing
#
#  for T in (:NfOrdGen, :NfMaxOrd)
#    @eval begin
#      function Base.call(O::$T, a::nf_elem, arr::Array{fmpz, 1})
#        return NfOrdElem{$T}(O, deepcopy(a), fmpz[ deepcopy(x) for x in arr])
#      end
#    end
#  end
#
#  doc"""
#  #      call(O::NfOrd) -> NfOrdElem
#
#  > This function constructs a new element of $\mathcal O$ which is set to $0$.
#  """
#  Base.call{T <: NfOrd}(O::T)
#
#  for T in (:NfOrdGen, :NfMaxOrd)
#    @eval begin
#      Base.call(O::$T) = NfOrdElem{$T}(O)
#    end
#  end
#end
#if VERSION > v"0.5.0-"
  doc"""
  ***
        (O::NfOrd)(a::nf_elem, check::Bool = true) -> NfOrdElem

  > Given an element $a$ of the ambient number field of $\mathcal O$, this
  > function coerces the element into $\mathcal O$. It will be checked that $a$
  > is contained in $\mathcal O$ if and only if `check` is `true`.
  """
  (O::NfOrd)(a::nf_elem, check::Bool = true) = begin
    if check
      (x,y) = _check_elem_in_order(a,O)
      !x && error("Number field element not in the order")
      return NfOrdElem(O, deepcopy(a), fmpz[ deepcopy(x) for x in y])
    else
      return NfOrdElem(O, deepcopy(a))
    end
  end

  doc"""
  ***
        (O::NfOrd)(a::NfOrdElem, check::Bool = true) -> NfOrdElem

  > Given an element $a$ of some order in the ambient number field of 
  > $\mathcal O$, this function coerces the element into $\mathcal O$. It
  > will be checked that $a$ is contained in $\mathcal O$ if and only if
  > `check` is `true`.
  """
  (O::NfOrd)(a::NfOrdElem, check::Bool = true) = begin
    b = nf(parent(a))(a)
    if check
      (x,y) = _check_elem_in_order(b,O)
      !x && error("Number field element not in the order")
      return NfOrdElem(O, deepcopy(b), fmpz[ deepcopy(x) for x in y])
    else
      return NfOrdElem(O, deepcopy(b))
    end
  end

  doc"""
  ***
        (O::NfOrd)(a::Union{fmpz, Integer}) -> NfOrdElem

  > Given an element $a$ of type `fmpz` or `Integer`, this
  > function coerces the element into $\mathcal O$. It will be checked that $a$
  > is contained in $\mathcal O$ if and only if `check` is `true`.
  """
  (O::NfOrd)(a::Union{fmpz, Integer}) = begin
    return NfOrdElem(O, nf(O)(a))
  end

  doc"""
  ***
        (O::NfOrd)(arr::Array{fmpz, 1})

  > Returns the element of $\mathcal O$ with coefficient vector `arr`.
  """
  (O::NfOrd)(arr::Array{fmpz, 1}) = begin
    return NfOrdElem(O, fmpz[ deepcopy(x) for x in arr ])
  end

  doc"""
  ***
        (O::NfOrd)(arr::Array{Integer, 1})

  > Returns the element of $\mathcal O$ with coefficient vector `arr`.
  """
  (O::NfOrd){S <: Integer}(arr::Array{S, 1}) = begin
    return NfOrdElem(O, deepcopy(arr))
  end

  doc"""
  ***
        (O::NfOrd)(a::nf_elem, arr::Array{fmpz, 1}) -> NfOrdElem

  > This function constructs the element of $\mathcal O$ with coefficient vector
  > `arr`. It is assumed that the corresponding element of the ambient number
  > field is $a$.
  """
  (O::NfOrd)(a::nf_elem, arr::Array{fmpz, 1}) = begin
    return NfOrdElem(O, deepcopy(a), fmpz[ deepcopy(x) for x in arr])
  end

  doc"""
  ***
        (O::NfOrd)() -> NfOrdElem

  > This function constructs a new element of $\mathcal O$ which is set to $0$.
  """
  (O::NfOrd)() = NfOrdElem(O) 
#end

################################################################################
#
#  Parent
#
################################################################################

doc"""
***
    parent(a::NfOrdElem) -> NfOrd

> Returns the order of which $a$ is an element.
"""
parent(a::NfOrdElem) = a.parent::NfOrd

################################################################################
#
#  Element in number field
#
################################################################################

doc"""
***
    elem_in_nf(a::NfOrdElem) -> nf_elem

> Returns the element $a$ considered as an element of the ambient number field.
"""
function elem_in_nf(a::NfOrdElem)
  if isdefined(a, :elem_in_nf)
    return deepcopy(a.elem_in_nf)
  end
  error("Not a valid order element")
end

################################################################################
#
#  Coordinates
#
################################################################################

doc"""
***
    elem_in_basis(a::NfOrdElem) -> Array{fmpz, 1}

> Returns the coefficient vector of $a$.
"""
function elem_in_basis(a::NfOrdElem)
  if a.has_coord
    return fmpz[ deepcopy(x) for x in a.elem_in_basis]
  else
    (x,y) = _check_elem_in_order(a.elem_in_nf, parent(a))
    !x && error("Not a valid order element")
    a.elem_in_basis = fmpz[ deepcopy(x) for x in y]
    a.has_coord = true
    @hassert :NfOrd 2 a == dot(a.elem_in_basis, basis(parent(a)))
    return fmpz[ deepcopy(x) for x in a.elem_in_basis]
  end
end

################################################################################
#
#  Discriminant
#
################################################################################

doc"""
***
    discriminant(B::Array{NfOrdElem, 1}) -> fmpz

> Returns the discriminant of the family $B$.
"""
function discriminant(B::Array{NfOrdElem, 1})
  length(B) == 0 && error("Number of elements must be non-zero")
  length(B) != degree(parent(B[1])) &&
        error("Number of elements must be $(degree(parent(B[1])))")
  O = parent(B[1])
  A = MatrixSpace(FlintZZ, degree(O), degree(O))()
  for i in 1:degree(O)
    for j in 1:degree(O)
      A[i,j] = FlintZZ(trace(B[i]*B[j]))
    end
  end
  return det(A)
end

################################################################################
#
#  Hashing
#
################################################################################

hash(x::NfOrdElem, h::UInt) = hash(x.elem_in_nf, h)

################################################################################
#
#  Equality
#
################################################################################

doc"""
***
    ==(x::NfOrdElem, y::NfOrdElem) -> Bool

> Returns whether $x$ and $y$ are equal.
"""
 ==(x::NfOrdElem, y::NfOrdElem) = parent(x) == parent(y) &&
                                            x.elem_in_nf == y.elem_in_nf

################################################################################
#
#  Special elements
#
################################################################################

doc"""
***
    zero(O::NfOrd) -> NfOrdElem

> Returns the zero element of $\mathcal O$.
"""
zero(O::NfOrd) = O(fmpz(0))

doc"""
***
    one(O::NfOrd) -> NfOrdElem

> Returns the zero element of $\mathcal O$.
"""
one(O::NfOrd) = O(fmpz(1))

doc"""
***
    zero(a::NfOrdElem) -> NfOrdElem

> Returns the zero element of the parent of $a$.
"""
zero(a::NfOrdElem) = parent(a)(0)

doc"""
***
    one(O::NfOrd) -> NfOrdElem

> Returns the one element of the parent of $a$.
"""
one(a::NfOrdElem) = parent(a)(1)

################################################################################
#
#  isone/iszero
#
################################################################################

doc"""
***
    isone(a::NfOrd) -> Bool

> Tests if $a$ is one.
"""
isone(a::NfOrdElem) = isone(a.elem_in_nf)

doc"""
***
    iszero(a::NfOrd) -> Bool

> Tests if $a$ is one.
"""
iszero(a::NfOrdElem) = iszero(a.elem_in_nf)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfOrdElem)
  print(io, a.elem_in_nf)
end

################################################################################
#
#  Unary operations
#
################################################################################

doc"""
***
    -(x::NfOrdElem) -> NfOrdElem

> Returns the additive inverse of $x$.
"""
function -(x::NfOrdElem)
  z = parent(x)()
  z.elem_in_nf = - x.elem_in_nf
  if x.has_coord
    z.elem_in_basis = map(y -> -y, x.elem_in_basis)
    z.has_coord = true
  end
  return z
end

###############################################################################
#
#  Binary operations
#
###############################################################################

doc"""
***
    *(x::NfOrdElem, y::NfOrdElem) -> NfOrdElem

> Returns $x \cdot y$.
"""
function *(x::NfOrdElem, y::NfOrdElem)
  parent(x) != parent(y) && error("Wrong parents")
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf*y.elem_in_nf
  return z
end

doc"""
***
    +(x::NfOrdElem, y::NfOrdElem) -> NfOrdElem

> Returns $x + y$.
"""
function +(x::NfOrdElem, y::NfOrdElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  if x.has_coord && y.has_coord
    z.elem_in_basis =
      fmpz[ x.elem_in_basis[i] + y.elem_in_basis[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

doc"""
***
    -(x::NfOrdElem, y::NfOrdElem) -> NfOrdElem

> Returns $x - y$.
"""
function -(x::NfOrdElem, y::NfOrdElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y.elem_in_nf
  if x.has_coord && y.has_coord
    z.elem_in_basis =
      fmpz[ x.elem_in_basis[i] - y.elem_in_basis[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

function *(x::NfOrdElem, y::Integer)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf * y
  if x.has_coord
    z.elem_in_basis = map(z -> y*z, x.elem_in_basis)
    z.has_coord = true
  end
  return z
end

*(x::Integer, y::NfOrdElem) = y * x

function *(x::NfOrdElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf * y
  if x.has_coord
    z.elem_in_basis = map(z -> y*z, x.elem_in_basis)
    z.has_coord = true
  end
  return z
end

*(x::fmpz, y::NfOrdElem) = y * x

Base.dot(x::fmpz, y::NfOrdElem) = y*x

function +(x::NfOrdElem, y::Integer)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y
  return z
end

+(x::Integer, y::NfOrdElem) = y + x

function +(x::NfOrdElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y
  return z
end

+(x::fmpz, y::NfOrdElem) = y + x

function -(x::NfOrdElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y
  return z
end

function -(x::NfOrdElem, y::Int)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y
  return z
end

-(x::fmpz, y::NfOrdElem) = -(y - x)

-(x::Integer, y::NfOrdElem) = -(y - x)

################################################################################
#
#  Adhoc exact division
#
################################################################################

function divexact(x::NfOrdElem, y::Int)
  z = parent(x)()
  z.elem_in_nf = divexact(x.elem_in_nf, y)
  return z
end

function divexact(x::NfOrdElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = divexact(x.elem_in_nf, y)
  return z
end

################################################################################
#
#  Exponentiation
#
################################################################################

doc"""
***
    ^(x::NfOrdElem, y::Union{fmpz, Int})

> Returns $x^y$.
"""
function ^(x::NfOrdElem, y::Union{fmpz, Int})
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf^y
  return z
end

################################################################################
#
#  Modular reduction
#
################################################################################

doc"""
***
    mod(a::NfOrdElem, m::Union{fmpz, Int}) -> NfOrdElem

> Reduces the coefficient vector of $a$ modulo $m$ and returns the corresponding
> element. The coefficient vector of the result will have entries $x$ with 
> $0 \leq x \leq m$.
"""
function mod(a::NfOrdElem, m::Union{fmpz, Int})
  ar = elem_in_basis(a)
  for i in 1:degree(parent(a))
    ar[i] = mod(ar[i],m)
  end
  return parent(a)(ar)
end

################################################################################
#
#  Modular exponentiation
#
################################################################################

doc"""
***
    powermod(a::NfOrdElem, i::fmpz, m::Union{fmpz, Int}) -> NfOrdElem

> Returns the element $a^i$ modulo $m$.
"""

function powermod(a::NfOrdElem, i::fmpz, p::fmpz)
  if i == 0 then
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
  b = mod(a*powermod(a,i-1,p),p)
  return b
end  

doc"""
***
    powermod(a::NfOrdElem, i::Integer, m::Integer) -> NfOrdElem

> Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfOrdElem, i::Integer, m::Integer)  = powermod(a, fmpz(i), fmpz(m))

doc"""
***
    powermod(a::NfOrdElem, i::fmpz, m::Integer) -> NfOrdElem

> Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfOrdElem, i::fmpz, m::Integer)  = powermod(a, i, fmpz(m))

doc"""
***
    powermod(a::NfOrdElem, i::Integer, m::fmpz) -> NfOrdElem

> Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfOrdElem, i::Integer, m::fmpz)  = powermod(a, fmpz(i), m)

################################################################################
#
#  Representation matrices
#
################################################################################

doc"""
***
    representation_mat(a::NfOrdElem) -> fmpz_mat

> Returns the representation matrix of the element $a$.
"""
function representation_mat(a::NfOrdElem)
  O = parent(a)
  A = representation_mat(a, nf(parent(a)))
  A = basis_mat(O)*A*basis_mat_inv(O)
  !(A.den == 1) && error("Element not in order")
  return A.num
end

doc"""
***
    representation_mat(a::NfOrdElem, K::AnticNumberField) -> FakeFmpqMat

> Returns the representation matrix of the element $a$ considered as an element
> of the ambient number field $K$. It is assumed that $K$ is the ambient number
> field of the order of $a$.
"""
function representation_mat(a::NfOrdElem, K::AnticNumberField)
  nf(parent(a)) != K && error("Element not in this field")
  d = den(a.elem_in_nf)
  b = d*a.elem_in_nf
  A = representation_mat(b)
  z = FakeFmpqMat(A, d)
  return z
end

#  nf(parent(a)) != K && error("Element not in this field")
#  return representation_mat(a.elem_in_nf)
#end

################################################################################
#
#  Trace
#
################################################################################

doc"""
***
    trace(a::NfOrdElem) -> fmpz

> Returns the trace of $a$.
"""
function trace(a::NfOrdElem)
  return FlintZZ(trace(elem_in_nf(a)))
end

################################################################################
#
#  Norm
#
################################################################################

doc"""
***
    norm(a::NfOrdElem) -> fmpz

> Returns the norm of $a$.
"""
function norm(a::NfOrdElem)
  return FlintZZ(norm(elem_in_nf(a)))
end

################################################################################
#
#  Random element generation
#
################################################################################

function rand!{T <: Integer}(z::NfOrdElem, O::NfOrd, R::UnitRange{T})
  y = O()
  ar = rand(R, degree(O))
  B = basis(O)
  mul!(z, ar[1], B[1])
  for i in 2:degree(O)
    mul!(y, ar[i], B[i])
    add!(z, z, y)
  end
  return z
end

doc"""
***
    rand(O::NfOrd, R::UnitRange{Integer}) -> NfOrdElem

> Computes a coefficient vector with entries uniformly distributed in `R` and returns
> the corresponding element of the order.
"""
function rand{T <: Integer}(O::NfOrd, R::UnitRange{T})
  z = O()
  rand!(z, O, R)
  return z
end

function rand!(z::NfOrdElem, O::NfOrd, n::Union{Integer, fmpz})
  return rand!(z, O, -n:n)
end

doc"""
***
    rand(O::NfOrd, n::Union{Integer, fmpz}) -> NfOrdElem

> Computes a coefficient vector with entries uniformly distributed in
> $\{-n,\dotsc,-1,0,1,\dotsc,n\}$ and returns the corresponding element of the
> order $\mathcal O$.
"""
function rand(O::NfOrd, n::Integer)
  return rand(O, -n:n)
end

function rand(O::NfOrd, n::fmpz)
  z = O()
  rand!(z, O, BigInt(n))
  return z
end

function rand!(z::NfOrdElem, O::NfOrd, n::fmpz)
  return rand!(z, O, BigInt(n))
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function add!(z::NfOrdElem, x::NfOrdElem, y::NfOrdElem)
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  if x.has_coord && y.has_coord
    for i in 1:degree(parent(x))
      z.elem_in_basis[i] = x.elem_in_basis[i] + y.elem_in_basis[i]
    end
    z.has_coord = true
  else
    z.has_coord = false
  end
  nothing
end

function mul!(z::NfOrdElem, x::NfOrdElem, y::NfOrdElem)
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
  z.has_coord = false
  nothing
end

function mul!(z::NfOrdElem, x::fmpz, y::NfOrdElem)
  z.elem_in_nf = x * y.elem_in_nf
  if y.has_coord
    for i in 1:degree(parent(z))
      z.elem_in_basis[i] = x*y.elem_in_basis[i]
    end
    z.has_coord = true
  else
    z.has_coord = false
  end
  nothing
end

mul!(z::NfOrdElem, x::Integer, y::NfOrdElem) =  mul!(z, ZZ(x), y)

mul!(z::NfOrdElem, x::NfOrdElem, y::Integer) = mul!(z, y, x)

function add!(z::NfOrdElem, x::fmpz, y::NfOrdElem)
  z.elem_in_nf = y.elem_in_nf + x
  z.has_coord = false
  nothing
end

add!(z::NfOrdElem, x::NfOrdElem, y::fmpz) = add!(z, y, x)

function add!(z::NfOrdElem, x::Integer, y::NfOrdElem)
  z.elem_in_nf = x + y.elem_in_nf
  z.has_coord = false
  nothing
end

add!(z::NfOrdElem, x::NfOrdElem, y::Integer) = add!(z, y, x)

mul!(z::NfOrdElem, x::NfOrdElem, y::fmpz) = mul!(z, y, x)

################################################################################
#
#  Base cases for dot product of vectors
#
################################################################################

dot(x::NfOrdElem, y::Int) = x*y

dot(x::Int, y::NfOrdElem) = dot(y, x)

dot(x::NfOrdElem, y::fmpz) = x*y

################################################################################
#
#  Conversion
#
################################################################################

(K::AnticNumberField)(x::NfOrdElem) = elem_in_nf(x)

################################################################################
#
#  Minkowski embedding
#
################################################################################

doc"""
***
    minkowski_map(a::NfOrdElem, abs_tol::Int) -> Array{arb, 1}

> Returns the image of $a$ under the Minkowski embedding.
> Every entry of the array returned is of type `arb` with radius less then
> `2^-abs_tol`.
"""
function minkowski_map(a::NfOrdElem, abs_tol::Int = 32)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return minkowski_map(a.elem_in_nf, abs_tol)
end

################################################################################
#
#  Conjugates
#
################################################################################

doc"""
***
    conjugates_arb(x::NfOrdElem, abs_tol::Int) -> Array{acb, 1}

> Compute the the conjugates of `x` as elements of type `acb`.
> Recall that we order the complex conjugates
> $\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
> $\sigma_{i}(x) = \overline{\sigma_{i + s}(x)}$ for $r + 2 \leq i \leq r + s$.
>
> Every entry `y` of the array returned satisfies `radius(real(y)) < 2^-abs_tol`,
> `radius(imag(y)) < 2^-abs_tol` respectively.
"""
function conjugates_arb(x::NfOrdElem, abs_tol::Int = 32)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return conjugates_arb(x.elem_in_nf, abs_tol)
end

doc"""
***
    conjugates_arb_log(x::NfOrdElem, abs_tol::Int) -> Array{arb, 1}

> Returns the elements
> $(\log(\lvert \sigma_1(x) \rvert),\dotsc,\log(\lvert\sigma_r(x) \rvert),
> \dotsc,2\log(\lvert \sigma_{r+1}(x) \rvert),\dotsc,
> 2\log(\lvert \sigma_{r+s}(x)\rvert))$ as elements of type `arb` radius
> less then `2^-abs_tol`.
"""
function conjugates_arb_log(x::NfOrdElem, abs_tol::Int = 32)
  return conjugates_arb_log(x.elem_in_nf, abs_tol)
end

################################################################################
#
#  T2
#
################################################################################

doc"""
***
    t2(x::NfOrdElem, abs_tol::Int = 32) -> arb

> Return the $T_2$-norm of $x$. The radius of the result will be less than
> `2^-abs_tol`.
"""
function t2(x::NfOrdElem, abs_tol::Int = 32)
  return t2(x.elem_in_nf, abs_tol)
end

# cleanup

function addeq!(a::NfOrdElem, b::NfOrdElem)
  addeq!(a.elem_in_nf, b.elem_in_nf)
  return a
end

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule{T <: Integer}(::Type{NfOrdElem}, ::Type{T}) =
        NfOrdElem

Nemo.promote_rule(::Type{NfOrdElem}, ::Type{fmpz}) = NfOrdElem
