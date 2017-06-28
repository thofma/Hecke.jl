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
       divexact, elem_in_nf, elem_in_basis, isone, iszero, minkowski_map, mod,
       mul!, norm, one, parent, powermod, rand, rand!, representation_mat,
       show, trace, t2, zero

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::NfOrdElem, dict::ObjectIdDict)
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
      (O::NfOrd)(a::nf_elem, check::Bool = true) -> NfOrdElem

> Given an element $a$ of the ambient number field of $\mathcal O$, this
> function coerces the element into $\mathcal O$. It will be checked that $a$
> is contained in $\mathcal O$ if and only if `check` is `true`.
"""
(O::NfOrd)(a::nf_elem, check::Bool = true) = begin
  if check
    (x, y) = _check_elem_in_order(a,O)
    !x && error("Number field element not in the order")
    return NfOrdElem(O, deepcopy(a), y)
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
    (x, y) = _check_elem_in_order(b,O)
    !x && error("Number field element not in the order")
    return NfOrdElem(O, deepcopy(b), y)
  else
    return NfOrdElem(O, deepcopy(b))
  end
end

(O::NfOrd)(a::nf_elem, arr::Vector{fmpz}, check::Bool = false) = begin
  if check
    (x, y) = _check_elem_in_order(a,O)
    (!x || arr != y ) && error("Number field element not in the order")
    return NfOrdElem(O, deepcopy(a), y)
  else
    return NfOrdElem(O, deepcopy(a), deepcopy(arr))
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
  return NfOrdElem(O, deepcopy(arr))
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
      (O::NfOrd)() -> NfOrdElem

> This function constructs a new element of $\mathcal O$ which is set to $0$.
"""
(O::NfOrd)() = NfOrdElem(O) 

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
parent(a::NfOrdElem) = a.parent

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
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(a::NfOrdElem)
  if a.has_coord
    return nothing
  else
    (x, y) = _check_elem_in_order(a.elem_in_nf, parent(a))
    !x && error("Not a valid order element")
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
    elem_in_basis(a::NfOrdElem) -> Array{fmpz, 1}

> Returns the coefficient vector of $a$.
"""
function elem_in_basis(a::NfOrdElem)
  assure_has_coord(a)
  @hassert :NfOrd 2 a == dot(a.elem_in_basis, basis(parent(a)))
  return deepcopy(a.elem_in_basis)
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
      A[i,j] = FlintZZ(trace(B[i] * B[j]))
    end
  end
  return det(A)
end

################################################################################
#
#  Hashing
#
################################################################################

Base.hash(x::NfOrdElem, h::UInt) = Base.hash(x.elem_in_nf, h)

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
      [ x.elem_in_basis[i] + y.elem_in_basis[i] for i = 1:degree(parent(x))]
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
      [ x.elem_in_basis[i] - y.elem_in_basis[i] for i = 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

doc"""
***
    divexact(x::NfOrdElem, y::NfOrdElem, check::Bool) -> NfOrdElem

> Returns $x/y$. It is assumed that $x/y$ is an element of the same order
> as $x$.
"""
function divexact(x::NfOrdElem, y::NfOrdElem, check::Bool = true)
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

for T in [Integer, fmpz]
  @eval begin
    function +(x::NfOrdElem, y::$T)
      z = parent(x)()
      z.elem_in_nf = x.elem_in_nf + y
      return z
    end

    +(x::$T, y::NfOrdElem) = y + x

    function -(x::NfOrdElem, y::$T)
      z = parent(x)()
      z.elem_in_nf = x.elem_in_nf - y
      return z
    end

    function -(x::$T, y::NfOrdElem)
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
    function divexact(x::NfOrdElem, y::$T, check::Bool = true)
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
  assure_has_coord(a)
  d = degree(parent(a))
  ar = Vector{fmpz}(d)
  for i in 1:d
    ar[i] = mod(a.elem_in_basis[i], m)
  end
  return NfOrdElem(parent(a), ar) # avoid making a copy of ar
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
  b = mod(a * powermod(a, i - 1, p), p)
  return b
end  

doc"""
***
    powermod(a::NfOrdElem, i::Integer, m::Integer) -> NfOrdElem

> Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfOrdElem, i::Integer, m::Integer) = powermod(a, fmpz(i), fmpz(m))

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
  assure_has_basis_mat(O)
  assure_has_basis_mat_inv(O)
  A = representation_mat(a, nf(O))
  mul!(A, O.basis_mat, A)
  mul!(A, A, O.basis_mat_inv)
  #A = O.basis_mat*A*O.basis_mat_inv
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
  return FlintZZ(trace(a.elem_in_nf))
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
  return FlintZZ(norm(a.elem_in_nf))
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
  add!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  if x.has_coord && y.has_coord
    if isdefined(z.elem_in_basis, 1)
      for i in 1:degree(parent(x))
        add!(z.elem_in_basis[i], x.elem_in_basis[i], y.elem_in_basis[i])
      end
    else
      for i in 1:degree(parent(x))
        z.elem_in_basis[i] = x.elem_in_basis[i] + y.elem_in_basis[i]
      end
    end
    z.has_coord = true
  else
    z.has_coord = false
  end
  return z
end

function mul!(z::NfOrdElem, x::NfOrdElem, y::NfOrdElem)
  mul!(z.elem_in_nf, x.elem_in_nf, y.elem_in_nf)
  z.has_coord = false
  return z
end

function addeq!(z::NfOrdElem, x::NfOrdElem)
  addeq!(z.elem_in_nf, x.elem_in_nf)
  if x.has_coord && z.has_coord
    for i in 1:degree(parent(z))
      add!(z.elem_in_basis[i], z.elem_in_basis[i], x.elem_in_basis[i])
    end
  end
  return z
end

# ad hoc
for T in [Integer, fmpz]
  @eval begin
    function mul!(z::NfOrdElem, x::NfOrdElem, y::$T)
      mul!(z.elem_in_nf, x.elem_in_nf, y)
      if x.has_coord
        if isdefined(z.elem_in_basis, 1)
          for i in 1:degree(parent(z))
            mul!(z.elem_in_basis[i], x.elem_in_basis[i], y)
          end
        else
          for i in 1:degree(parent(z))
            z.elem_in_basis[i] = x.elem_in_basis[i] * y
          end
        end
        z.has_coord = true
      else
        z.has_coord = false
      end
      return z
    end

    mul!(z::NfOrdElem, x::$T, y::NfOrdElem) = mul!(z, y, x)

  end
end

for T in [Integer, fmpz]
  @eval begin
    function add!(z::NfOrdElem, x::NfOrdElem, y::$T)
      add!(z.elem_in_nf, x.elem_in_nf, y)
      z.has_coord = false
      return z
    end

    add!(z::NfOrdElem, x::$T, y::NfOrdElem) = add!(z, y, x)
  end
end

################################################################################
#
#  Base cases for dot product of vectors
#
################################################################################

dot(x::NfOrdElem, y::Integer) = x * y

dot(x::Integer, y::NfOrdElem) = y * x

dot(x::NfOrdElem, y::fmpz) = x * y

dot(x::fmpz, y::NfOrdElem) = y * x

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

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule{T <: Integer}(::Type{NfOrdElem}, ::Type{T}) = NfOrdElem

Nemo.promote_rule(::Type{NfOrdElem}, ::Type{fmpz}) = NfOrdElem
