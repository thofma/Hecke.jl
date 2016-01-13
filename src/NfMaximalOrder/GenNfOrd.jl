################################################################################
#
#  GenNfOrd.jl : Generic orders in number fields and elements/ideals thereof
#
# This file is part of hecke.
#
# Copyright (c) 2015: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2015 Tommy Hofmann
#
################################################################################
#
#  TODO:
#   Fix hashing 
#
################################################################################

export GenNfOrdIdl, elem_in_order, rand, rand!, istorsionunit, NfOrderElem,
       minkowski_mat, conjugates_log, conjugates_arb

################################################################################
#
#  Signature
#
################################################################################

doc"""
***
    signature(O::GenNfOrd) -> Tuple{Int, Int}

> Returns the signature of the ambient number field of $\mathcal O$.
"""
function signature(x::GenNfOrd)
  if x.signature[1] != -1
    return x.signature
  else
    x.signature = signature(nf(x).pol)
    return x.signature
  end
end

################################################################################
#
#  Discriminant
#
################################################################################

doc"""
***
    discriminant(O::GenNfOrd) -> fmpz

> Returns the discriminant of $\mathcal O$.
"""
function discriminant(O::GenNfOrd)
  if isdefined(O, :disc)
    return O.disc
  end

  A = MatrixSpace(FlintZZ, degree(O), degree(O))()
  B = basis_nf(O)
  for i in 1:degree(O)
    for j in 1:degree(O)
      A[i,j] = FlintZZ(trace(B[i]*B[j]))
    end
  end
  O.disc = determinant(A)
  return O.disc
end

################################################################################
#
#  Minkowski matrix
#
################################################################################

doc"""
***
    minkowski_mat(O::GenNfOrd, abs_tol::Int) -> arb_mat

> Returns the Minkowski matrix of $\mathcal O$.
> Thus if $\mathcal O$ has degree $d$, then the
> result is a matrix in $\operatorname{Mat}_{d\times d}(\mathbf R)$.
> The entries of the matrix are real balls of type `arb` with radius
> less then `2^abs_tol`. 
"""

function minkowski_mat(O::GenNfOrd, abs_tol::Int)
  if isdefined(O, :minkowski_mat) && O.minkowski_mat[2] < abs_tol
    A = deepcopy(O.minkowski_mat[1])
  else
    T = Array(Array{arb, 1}, degree(O))
    B = basis(O, nf(O))
    for i in 1:degree(O)
      T[i] = minkowski_map(B[i], abs_tol)
    end
    p = maximum([ prec(parent(T[i][j])) for i in 1:degree(O), j in 1:degree(O) ])
    M = ArbMatSpace(ArbField(p), degree(O), degree(O))()
    for i in 1:degree(O)
      for j in 1:degree(O)
        M[i, j] = T[i][j]
      end
    end
    println(p)
    O.minkowski_mat = (M, abs_tol)
    A = deepcopy(M)
  end
  return A
end

################################################################################
################################################################################
##
##  NfOrderElem
##
################################################################################
################################################################################


################################################################################
#
#  Parent object overloading
#
################################################################################

doc"""
***
    call(O::GenNfOrd, a::nf_elem, check::Bool = true) -> NfOrderElem

> Given an element $a$ of the ambient number field of $\mathcal O$, this
> function coerces the element into $\mathcal O$. It will be checked that $a$
> is contained in $\mathcal O$ if and only if `check` is `true`.
"""
function call(O::GenNfOrd, a::nf_elem, check::Bool = true)
  if check
    (x,y) = _check_elem_in_order(a,O)
    !x && error("Number field element not in the order")
    return NfOrderElem(O, deepcopy(a), y)
  else
    return NfOrderElem(O, deepcopy(a))
  end
end

doc"""
***
    call(O::GenNfOrd, a::Union{fmpz, Integer}) -> NfOrderElem

> Given an element $a$ of type `fmpz` or `Integer`, this
> function coerces the element into $\mathcal O$. It will be checked that $a$
> is contained in $\mathcal O$ if and only if `check` is `true`.
"""
function call(O::GenNfOrd, a::Union{fmpz, Integer})
  return NfOrderElem(O, nf(O)(a))
end

doc"""
***
    call(O::GenNfOrd, arr::Array{fmpz, 1})

> Returns the element of $\mathcal O$ with coefficient vector `arr`.
"""
function call(O::GenNfOrd, arr::Array{fmpz, 1})
  return NfOrderElem(O, deepcopy(arr))
end

doc"""
***
    call{T <: Integer}(O::GenNfOrd, arr::Array{T, 1})

> Returns the element of $\mathcal O$ with coefficient vector `arr`.
"""
function call{T <: Integer}(O::GenNfOrd, arr::Array{T, 1})
  return NfOrderElem(O, deepcopy(arr))
end

doc"""
***
    call(O::GenNfOrd, a::nf_elem, arr::Array{fmpz, 1}) -> NfOrderElem

> This function constructs the element of $\mathcal O$ with coefficient vector
> `arr`. It is assumed that the corresponding element of the ambient number
> field is $a$.
"""
function call(O::GenNfOrd, a::nf_elem, arr::Array{fmpz, 1})
  return NfOrderElem(O, deepcopy(a), deepcopy(arr))
end

doc"""
***
    call(O::GenNfOrd) -> NfOrderElem

> This function constructs a new element of $\mathcal O$ which is set to $0$.
"""
function call(O::GenNfOrd)
  return NfOrderElem(O)
end

################################################################################
#
#  Field access
#
################################################################################

doc"""
***
    parent(a::NfOrderElem) -> GenNfOrd

> Returns the order of which $a$ is an element.
"""
parent(a::NfOrderElem) = a.parent

doc"""
***
    elem_in_nf(a::NfOrderElem) -> nf_elem

> Returns the element $a$ considered as an element of the ambient number field.
"""
function elem_in_nf(a::NfOrderElem)
  if isdefined(a, :elem_in_nf)
    return a.elem_in_nf
  end
  error("Not a valid order element")
end

doc"""
***
    elem_in_basis(a::NfOrderElem) -> Array{fmpz, 1}

> Returns the coefficient vector of $a$.
"""
function elem_in_basis(a::NfOrderElem)
  @vprint :NfOrder 2 "Computing the coordinates of $a\n"
  if a.has_coord
    return a.elem_in_basis
  else
    (x,y) = _check_elem_in_order(a.elem_in_nf,parent(a))
    !x && error("Number field element not in the order")
    a.elem_in_basis = y
    a.has_coord = true
    return a.elem_in_basis
  end
end

################################################################################
#
#  Hashing
#
################################################################################

# I don't think this is a good idea

hash(x::NfOrderElem) = hash(elem_in_nf(x))

################################################################################
#
#  Equality testing
#
################################################################################

doc"""
***
    ==(x::NfOrderElem, y::NfOrderElem) -> Bool

> Returns whether $x$ and $y$ are equal.
"""
==(x::NfOrderElem, y::NfOrderElem) = parent(x) == parent(y) &&
                                            x.elem_in_nf == y.elem_in_nf

################################################################################
#
#  Copy
#
################################################################################

doc"""
***
    deepcopy(x::NfOrderElem) -> NfOrderElem

> Returns a copy of $x$.
"""
function deepcopy(x::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = deepcopy(x.elem_in_nf)
  if x.has_coord
    z.has_coord = true
    z.elem_in_basis = deepcopy(x.elem_in_basis)
  end
  return z
end

################################################################################
#
#  Inclusion of number field elements
#
################################################################################

# Check if a number field element is contained in O
# In this case, the second return value is the coefficient vector with respect
# to the basis of O

function _check_elem_in_order(a::nf_elem, O::GenNfOrd)
  M = MatrixSpace(ZZ, 1, degree(O))()
  t = FakeFmpqMat(M)
  elem_to_mat_row!(t.num, 1, t.den, a)
  x = t*basis_mat_inv(O)
  v = Array(fmpz, degree(O))
  for i in 1:degree(O)
    v[i] = x.num[1,i]
  end
  return (x.den == 1, v) 
end  

doc"""
***
    in(a::nf_elem, O::GenNfOrd) -> Bool

> Checks wether $a$ lies in $\mathcal O$.
"""
function in(a::nf_elem, O::GenNfOrd)
  (x,y) = _check_elem_in_order(a,O)
  return x
end

################################################################################
#
#  Denominator in an order
#
################################################################################

doc"""
***
    den(a::nf_elem, O::GenNfOrd) -> fmpz

> Returns the smallest positive integer $k$ such that $k \cdot a$ lies in O.
"""
function den(a::nf_elem, O::GenNfOrd)
  d = den(a)
  b = d*a 
  M = MatrixSpace(ZZ, 1, degree(O))()
  elem_to_mat_row!(M, 1, fmpz(1), b)
  t = FakeFmpqMat(M, d)
  z = t*basis_mat_inv(O)
  return z.den
end

################################################################################
#
#  Special elements
#
################################################################################

doc"""
***
    zero(O::GenNford) -> NfOrderElem

> Returns an element of $\mathcal O$ which is set to zero.
"""
zero(O::GenNfOrd) = O(fmpz(0))

doc"""
***
    one(O::GenNfOrd) -> NfOrderElem

> Returns an element of $\mathcal O$ which is set to one.
"""
one(O::GenNfOrd) = O(fmpz(1))

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfOrderElem)
  print(io, a.elem_in_nf)
end

################################################################################
#
#  Unary operations
#
################################################################################

doc"""
***
    -(x::NfOrderElem) -> NfOrderElem

> Returns the additive inverse of $x$.
"""
function -(x::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = - x.elem_in_nf
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

doc"""
***
    *(x::NfOrderElem, y::NfOrderElem) -> NfOrderElem

> Returns $x \cdot y$.
"""
function *(x::NfOrderElem, y::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf*y.elem_in_nf
  return z
end

doc"""
***
    +(x::NfOrderElem, y::NfOrderElem) -> NfOrderElem

> Returns $x + y$.
"""
function +(x::NfOrderElem, y::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  return z
end

doc"""
***
    -(x::NfOrderElem, y::NfOrderElem) -> NfOrderElem

> Returns $x - y$.
"""
function -(x::NfOrderElem, y::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y.elem_in_nf
  return z
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

doc"""
***
    *(x::NfOrderElem, y::Union{fmpz, Integer})

> Returns $x \cdot y$.
"""
function *(x::NfOrderElem, y::Union{fmpz, Integer})
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf * y
  return z
end

*(x::Union{fmpz, Integer}, y::NfOrderElem) = y * x

doc"""
***
    +(x::NfOrderElem, y::Union{fmpz, Integer})

> Returns $x + y$.
"""
function +(x::NfOrderElem, y::Union{fmpz, Integer})
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y
  return z
end

+(x::Union{fmpz, Integer}, y::NfOrderElem) = y + x

doc"""
***
    -(x::NfOrderElem, y::Union{fmpz, Integer})

> Returns $x - y$.
"""
function -(x::NfOrderElem, y::Union{fmpz, Integer})
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y
  return z
end

-(x::Union{fmpz, Integer}, y::NfOrderElem) = y - x

################################################################################
#
#  Exponentiation
#
################################################################################

doc"""
***
    ^(x::NfOrderElem, y::Union{fmpz, Int})

> Returns $x^y$.
"""
function ^(x::NfOrderElem, y::Union{fmpz, Int})
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
    mod(a::NfOrderElem, m::Union{fmpz, Int}) -> NfOrderElem

> Reduces the coefficient vector of $a$ modulo $m$ and returns the corresponding
> element.
"""
function mod(a::NfOrderElem, m::Union{fmpz, Int})
  ar = copy(elem_in_basis(a))
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
    powermod(a::NfOrderElem, i::fmpz, m::Union{fmpz, Int}) -> NfOrderElem

> Returns the element $a^i$ modulo $m$.
"""

function powermod(a::NfOrderElem, i::fmpz, p::fmpz)
  if i == 0 then
    return one(parent(a))
  end
  if i == 1 then
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
    powermod(a::NfOrderElem, i::Integer, m::Integer) -> NfOrderElem

> Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfOrderElem, i::Integer, m::Integer)  = powermod(a, fmpz(i), fmpz(m))

doc"""
***
    powermod(a::NfOrderElem, i::fmpz, m::Integer) -> NfOrderElem

> Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfOrderElem, i::fmpz, m::Integer)  = powermod(a, i, fmpz(m))

doc"""
***
    powermod(a::NfOrderElem, i::Integer, m::fmpz) -> NfOrderElem

> Returns the element $a^i$ modulo $m$.
"""
powermod(a::NfOrderElem, i::Integer, m::fmpz)  = powermod(a, fmpz(i), m)

################################################################################
#
#  Representation matrices
#
################################################################################

doc"""
***
    representation_mat(a::NfOrderElem) -> fmpz_mat

> Returns the representation matrix of the element $a$.
"""
function representation_mat(a::NfOrderElem)
  O = parent(a)
  A = representation_mat(a, nf(parent(a)))
  A = basis_mat(O)*A*basis_mat_inv(O)
  !(A.den == 1) && error("Element not in order")
  return A.num
end

doc"""
    representation_mat(a::NfOrderElem, K::AnticNumberField) -> FakeFmpqMat

> Returns the representation matrix of the element $a$ considered as an element
> of the ambient number field $K$. It is assumed that $K$ is the ambient number
> field of the order of $a$.
"""
function representation_mat(a::NfOrderElem, K::AnticNumberField)
  nf(parent(a)) != K && error("Element not in this field")
  d = den(a.elem_in_nf)
  b = d*a.elem_in_nf
  A = representation_mat(b)
  z = FakeFmpqMat(A,d)
  return z
end

################################################################################
#
#  Trace
#
################################################################################

doc"""
***
    trace(a::NfOrderElem) -> fmpz

> Returns the trace of $a$.
"""
function trace(a::NfOrderElem)
  return FlintZZ(trace(elem_in_nf(a)))
end

################################################################################
#
#  Norm
#
################################################################################

doc"""
***
    norm(a::NfOrderElem) -> fmpz

> Returns the norm of $a$.
"""
function norm(a::NfOrderElem)
  return FlintZZ(norm(elem_in_nf(a)))
end

################################################################################
#
#  Random element generation
#
################################################################################

function rand!{T <: Integer}(z::NfOrderElem, O::GenNfOrd, R::UnitRange{T})
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
    rand{T <: Union{Integer, fmpz}}(O::GenNfOrd, R::UnitRange{T}) -> NfOrderElem

> Computes a coefficient vector with entries uniformly distributed in `R` and returns
> the corresponding element of the order.
"""
function rand{T <: Union{Integer, fmpz}}(O::GenNfOrd, R::UnitRange{T})
  z = O()
  rand!(z, O, R)
  return z
end

function rand!(z::NfOrderElem, O::GenNfOrd, n::Union{Integer, fmpz})
  return rand!(z, O, -n:n)
end

doc"""
***
    rand(O::GenNfOrd, n::Union{Integer, fmpz}) -> NfOrderElem

> Computes a coefficient vector with entries uniformly distributed in
> $\{-n,\dotsc,-1,0,1,\dotsc,n\}$ and returns the corresponding element of the
> order $\mathcal O$.
"""
function rand(O::GenNfOrd, n::Integer)
  return rand(O, -n:n)
end

function rand!(z::NfOrderElem, O::GenNfOrd, n::fmpz)
  return rand!(z, O, BigInt(n))
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function add!(z::NfOrderElem, x::NfOrderElem, y::NfOrderElem)
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

function mul!(z::NfOrderElem, x::NfOrderElem, y::NfOrderElem)
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
  z.has_coord = false
  nothing
end

function mul!(z::NfOrderElem, x::fmpz, y::NfOrderElem)
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

mul!(z::NfOrderElem, x::Integer, y::NfOrderElem) =  mul!(z, ZZ(x), y)

mul!(z::NfOrderElem, x::NfOrderElem, y::Integer) = mul!(z, y, x)

function add!(z::NfOrderElem, x::fmpz, y::NfOrderElem)
  z.elem_in_nf = y.elem_in_nf + x
  nothing
end

add!(z::NfOrderElem, x::NfOrderElem, y::fmpz) = add!(z, y, x)

function add!(z::NfOrderElem, x::Integer, y::NfOrderElem)
  z.elem_in_nf = x + y.elem_in_nf
  nothing
end

add!(z::NfOrderElem, x::NfOrderElem, y::Integer) = add!(z, y, x)

mul!(z::NfOrderElem, x::NfOrderElem, y::fmpz) = mul!(z, y, x)

################################################################################
#
#  Base cases for dot product of vectors
#
################################################################################

dot(x::fmpz, y::nf_elem) = x*y

dot(x::nf_elem, y::fmpz) = x*y

dot(x::NfOrderElem, y::Int64) = y*x

################################################################################
#
#  Conversion
#
################################################################################

Base.call(K::AnticNumberField, x::NfOrderElem) = elem_in_nf(x)

################################################################################
#
#  Minkowski embedding
#
################################################################################

doc"""
***
    minkowski_map(a::NfOrderElem, abs_tol::Int) -> Array{arb, 1}

> Returns the image of $a$ under the Minkowski embedding.
> Every entry of the array returned is of type `arb` with radius less then
> `2^abs_tol`.
"""
function minkowski_map(a::NfOrderElem, abs_tol::Int)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return minkowski_map(a.elem_in_nf)
end

################################################################################
#
#  Conjugates
#
################################################################################

doc"""
***
    conjugates_arb(x::NfOrderElem, abs_tol::Int) -> Tuple{Array{arb, 1}, Array{acb, 1}}

> Compute the the conjugates of `x` as elements of type `arb` and `acb`
> respectively. Recall that we order the complex conjugates
> $\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
> $\sigma_{i}(x) = \overline{\sigma_{i + s}(x)}$ for $r + 1 \leq i \leq r + s$.
>
> Every entry `y` of the arrays returned satisfies `radius(y) < 2^abs_tol` or
> `radius(real(y)) < 2^abs_tol`, `radius(imag(y)) < 2^abs_tol` respectively.
"""
function conjugates_arb(x::NfOrderElem, abs_tol::Int)
  # Use a.elem_in_nf instead of elem_in_nf(a) to avoid copying the data.
  # The function minkowski_map does not alter the input!
  return conjugates_arb(x.elem_in_nf, abs_tol)
end

doc"""
***
    conjugates_log(x::NfOrderElem, abs_tol::Int) -> Array{arb, 1}

> Returns the elements
> $(\log(\lvert \sigma_1(x) \rvert),\dotsc,\log(\lvert\sigma_r(x) \rvert),
> \dotsc,2\log(\lvert \sigma_{r+1}(x) \rvert),\dotsc,
> 2\log(\lvert \sigma_{r+s}(x)\rvert))$ as elements of type `arb` radius
> less then `2^abs_tol`.
"""
function conjugates_log(x::NfOrderElem)
  return conjugates_log(x.elem_in_nf)
end

################################################################################
################################################################################
##
##  GenNfOrdIdl : Ideals in GenNfOrd
##
################################################################################
################################################################################

doc"""
***
    ==(x::GenNfOrdIdl, y::GenNfOrdIdl)

> Returns whether $x$ and $y$ are equal.
"""
function ==(x::GenNfOrdIdl, y::GenNfOrdIdl)
  return basis_mat(x) == basis_mat(y)
end

doc"""
***
    +(x::GenNfOrdIdl, y::GenNfOrdIdl)

> Returns $x + y$.
"""
function +(x::GenNfOrdIdl, y::GenNfOrdIdl)
  H = vcat(basis_mat(x), basis_mat(y))
  g = gcd(minimum(x),minimum(y))
  H = _hnf_modular_eldiv(H, g, :lowerleft)
  #H = sub(_hnf(vcat(basis_mat(x),basis_mat(y)), :lowerleft), degree(order(x))+1:2*degree(order(x)), 1:degree(order(x)))
  return ideal(order(x), H)
end

doc"""
***
    *(x::GenNfOrdIdl, y::GenNfOrdIdl)

> Returns $x \cdot y$.
"""
function *(x::GenNfOrdIdl, y::GenNfOrdIdl)
  return _mul(x, y)
end

function _mul(x::GenNfOrdIdl, y::GenNfOrdIdl)
  O = order(x)
  l = minimum(x)*minimum(y)
  z = MatrixSpace(FlintZZ, degree(O)*degree(O), degree(O))()
  X = basis(x)
  Y = basis(y)
  for i in 1:degree(O)
    for j in 1:degree(O)
      t = elem_in_basis(X[i]*Y[j])
      for k in 1:degree(O)
        z[i*j, k] = t[k]
      end
    end
  end
  return ideal(O, _hnf_modular_eldiv(z, l, :lowerleft))
end

################################################################################
#
#  Inclusion of order elements in ideals
#
################################################################################

doc"""
***
    in(x::NfOrderElem, y::GenNfOrdIdl)

> Returns whether $x$ is contained in $y$.
"""
function in(x::NfOrderElem, y::GenNfOrdIdl)
  v = transpose(MatrixSpace(FlintZZ, degree(parent(x)), 1)(elem_in_basis(x)))
  t = FakeFmpqMat(v, fmpz(1))*basis_mat_inv(y)
  return t.den == 1
end

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

doc"""
***
    mod(x::NfOrderElem, I::GenNfOrdIdl)

> Returns the unique element $y$ of the ambient order of $x$ with
> $x \equiv y \bmod I$ and the following property: If
> $a_1,\dotsc,a_d \in \Z_{\geq 1}$ are the diagonal entries of the unique HNF
> basis matrix of $I$ and $(b_1,\dotsc,b_d)$ is the coefficient vector of $y$,
> then $0 \leq b_i < a_i$ for $1 \leq i \leq d$.
"""
function mod(x::NfOrderElem, y::GenNfOrdIdl)
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape
  O = order(y)
  b = elem_in_basis(x)
  a = deepcopy(b)
  b = basis_mat(y)
  t = fmpz(0)
  for i in degree(O):-1:1
    t = div(a[i],b[i,i])
    for j in 1:i
      a[j] = a[j] - t*b[i,j]
    end
  end
  return O(a)
end

################################################################################
#
#  Compute the p-radical
#
################################################################################

doc"""
***
    pradical(O::GenNfOrd, p::fmpz) -> GenNfOrdIdl

> Given a prime number $p$, this function returns the $p$-radical
> $\sqrt{p\mathcal O}$ of $\mathcal O$, which is 
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
function pradical(O::GenNfOrd, p::fmpz)
  j = clog(fmpz(degree(O)),p)

  @assert p^(j-1) < degree(O)
  @assert degree(O) <= p^j

  R = ResidueRing(ZZ,p)
  A = MatrixSpace(R, degree(O), degree(O))()
  for i in 1:degree(O)
    t = powermod(basis(O)[i], p^j, p)
    ar = elem_in_basis(t)
    for k in 1:degree(O)
      A[i,k] = ar[k]
    end
  end
  X = kernel(A)
  Mat = MatrixSpace(ZZ, 1, degree(O))
  MMat = MatrixSpace(R, 1, degree(O))
  if length(X) != 0
    m = lift(MMat(X[1]))
    for x in 2:length(X)
      m = vcat(m,lift(MMat(X[x])))
    end
    m = vcat(m,MatrixSpace(ZZ, degree(O), degree(O))(p))
  else
    m = MatrixSpace(ZZ, degree(O), degree(O))(p)
  end
  r = sub(_hnf(m, :lowerleft), rows(m) - degree(O) + 1:rows(m), 1:degree(O))
  return ideal(O, r)
end

doc"""
***
    pradical(O::GenNfOrd, p::Integer) -> GenNfOrdIdl

> Given a prime number $p$, this function returns the $p$-radical
> $\sqrt{p\mathcal O}$ of $\mathcal O$, which is 
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
function pradical(O::GenNfOrd, p::Integer)
  return pradical(O, fmpz(p))
end

################################################################################
#
#  Promotion
#
################################################################################

Base.promote_rule{T <: Integer}(::Type{NfOrderElem}, ::Type{T}) = NfOrderElem
