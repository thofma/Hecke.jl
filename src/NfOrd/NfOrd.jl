################################################################################
#
#  NfOrd.jl : Orders in number fields
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

export isequationorder, nf, parent, basis, basis_mat, basis_mat_inv,
       discriminant, degree, gen_index, index, is_index_divisor, deepcopy,
       signature, minkowski_mat, in, den

################################################################################
#
#  Predicates
#
################################################################################

doc"""
***
    isequationorder(O::NfOrd) -> Bool

>  Returns whether $\mathcal O$ is the equation order.
"""
isequationorder(O::NfOrd) = O.isequationorder

################################################################################
#
#  Ambient number field
#
################################################################################

doc"""
***
    nf(O::NfOrd) -> AnticNumberField

> Returns the ambient number field of $\mathcal O$.
"""
nf(O::NfOrd) = O.nf

################################################################################
#
#  Parent
#
################################################################################

doc"""
***
    parent(O::NfOrd) -> NfOrdSet

> Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
> number field.
"""
parent(O::NfOrd) = O.parent

################################################################################
#
#  Basis
#
################################################################################

function basis_ord(O::NfOrd)
  if isdefined(O, :basis_ord)
    return O.basis_ord::Array{NfOrdElem{typeof(O)}, 1}
  end
  b = O.basis_nf
  B = Array(NfOrdElem{typeof(O)}, length(b))
  for i in 1:length(b)
    v = fill(FlintZZ(0), length(b))
    v[i] = FlintZZ(1)
    B[i] = O(b[i], v; check = false)
  end
  O.basis_ord = B
  return B::Array{NfOrdElem{typeof(O)}, 1}
end

doc"""
***
    basis(O::NfOrd) -> Array{NfOrdElem, 1}

> Returns the $\mathbf Z$-basis of $\mathcal O$.
"""
function basis(O::NfOrd)
  return basis_ord(O)
end

doc"""
***
    basis(O::NfOrd, K::AnticNumberField) -> Array{nf_elem, 1}

> Returns the $\mathbf Z$-basis of $\mathcal O$ as elements of the ambient
> number field.
"""
function basis(O::NfOrd, K::AnticNumberField)
  nf(O) != K && error()
  return deepcopy(O.basis_nf)
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

doc"""
***
    basis_mat(O::NfOrd) -> FakeFmpqMat

> Returns the basis matrix of $\mathcal O$ with respect to the power basis
> of the ambient number field.
"""
function basis_mat(O::NfOrd)
  if isdefined(O, :basis_mat)
    return deepcopy(O.basis_mat)
  end
  A = O.basis_nf
  O.basis_mat = FakeFmpqMat(basis_mat(A))
  return deepcopy(O.basis_mat)
end

doc"""
***
    basis_mat_inv(O::NfOrd) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfOrd)
  if isdefined(O, :basis_mat_inv)
    return deepcopy(O.basis_mat_inv)
  end
  O.basis_mat_inv = inv(basis_mat(O))
  return deepcopy(O.basis_mat_inv)
end

################################################################################
#
#  Discriminant
#
################################################################################

doc"""
***
    discriminant(O::NfOrd) -> fmpz

> Returns the discriminant of $\mathcal O$.
"""
function discriminant(O::NfOrd)
  if isdefined(O, :disc)
    return deepcopy(O.disc)
  end

  if isequationorder(O)
    O.disc = num(discriminant(nf(O).pol))
    return deepcopy(O.disc)
  end

  return discriminant(basis(O))
end

################################################################################
#
#  Degree
#
################################################################################

doc"""
    degree(O::NfOrd) -> Int

> Returns the degree of $\mathcal O$.
"""
degree(O::NfOrd) = degree(O.nf)

################################################################################
#
#  (Generalized) index
#
################################################################################

doc"""
***
    gen_index(O::NfOrd) -> fmpq

> Generalized index of $\mathcal O$ with respect to the ambient equation
> order $\mathbf Z[\alpha]$.
"""
function gen_index(O::NfOrd)
  if isdefined(O, :gen_index)
    return deepcopy(O.gen_index)
  else
    O.gen_index = QQ(basis_mat(O).den^degree(O), det(basis_mat(O).num))
    return deepcopy(O.gen_index)
  end
end

doc"""
***
    index(O::NfOrd) -> fmpz

> Assuming that the order $\mathcal O$ contains the ambient equation order
> $\mathbf Z[\alpha]$, this function returns the index $[ \mathcal O : \mathbf ZZ]$.
"""
function index(O::NfOrd)
  if isdefined(O, :index)
    return deepcopy(O.index)
  else
    i = gen_index(O)
    den(i) != 1 && error("Order does not contain the equation order")
    O.index = num(i)
    return deepcopy(O.index)
  end
end

################################################################################
#
#  Index divisor
#
################################################################################

doc"""
    is_index_divisor(O::NfOrd, d::fmpz) -> Bool
    is_index_divisor(O::NfOrd, d::Int) -> Bool

> Returns whether $d$ is a divisor of the index of $\mathcal O$.
"""
function is_index_divisor(O::NfOrd, d::Union{fmpz, Int})
  i = index(O)
  return i % d == 0
end

################################################################################
#
#  Deepcopy
#
################################################################################

doc"""
***
    deepcopy(O::NfOrd) -> NfOrd

> Makes a copy of $\mathcal O$.
"""
function deepcopy(O::NfOrd)
  z = NfOrdGen()
  for x in fieldnames(O)
    # This is slow. Julia can't interfere the type of the right hand side.
    # (According to @code_warntype)
    if x != :nf && x != :parent && isdefined(O, x) 
      z.(x) = deepcopy(getfield(O, x))
    end
  end
  z.nf = O.nf
  z.parent = O.parent
  return z
end

################################################################################
#
#  Signature
#
################################################################################

doc"""
    signature(O::NfOrd) -> Tuple{Int, Int}

> Returns the signature of the ambient number field of $\mathcal O$.
"""
function signature(x::NfOrd)
  if x.signature[1] != -1
    return x.signature
  else
    x.signature = signature(nf(x))
    return x.signature
  end
end

################################################################################
#
#  Minkowski matrix
#
################################################################################

doc"""
***
    minkowski_mat(O::NfOrd, abs_tol::Int = 64) -> arb_mat

> Returns the Minkowski matrix of $\mathcal O$.
> Thus if $\mathcal O$ has degree $d$, then the
> result is a matrix in $\operatorname{Mat}_{d\times d}(\mathbf R)$.
> The entries of the matrix are real balls of type `arb` with radius
> less then `2^-abs_tol`. 
"""
function minkowski_mat(O::NfOrd, abs_tol::Int = 64)
  if isdefined(O, :minkowski_mat) && O.minkowski_mat[2] > abs_tol
    A = deepcopy(O.minkowski_mat[1])
  else
    T = Array(Array{arb, 1}, degree(O))
    B = O.basis_nf
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
    O.minkowski_mat = (M, abs_tol)
    A = deepcopy(M)
  end
  return A
end

################################################################################
#
#  Inclusion of number field elements
#
################################################################################

# Check if a number field element is contained in O
# In this case, the second return value is the coefficient vector with respect
# to the basis of O
function _check_elem_in_order(a::nf_elem, O::NfOrd)
  M = MatrixSpace(FlintZZ, 1, degree(O))()
  t = FakeFmpqMat(M)
  elem_to_mat_row!(t.num, 1, t.den, a)
  x = t*basis_mat_inv(O)
  v = Array(fmpz, degree(O))
  for i in 1:degree(O)
    v[i] = deepcopy(x.num[1,i])
  end
  return (x.den == 1, v) 
end  

doc"""
***
    in(a::nf_elem, O::NfOrd) -> Bool

> Checks whether $a$ lies in $\mathcal O$.
"""
function in(a::nf_elem, O::NfOrd)
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
    den(a::nf_elem, O::NfOrd) -> fmpz

> Returns the smallest positive integer $k$ such that $k \cdot a$ lies in O.
"""
function den(a::nf_elem, O::NfOrd)
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
#  Addition of orders
#
################################################################################

doc"""
***
    +(R::NfOrd, S::NfOrd) -> NfOrd

> Given two orders $R$, $S$ of $K$, this function returns the smallest order
> containing both $R$ and $S$. It is assumed that $R$, $S$ contain the ambient
> equation order and have coprime index.
"""
function +(a::NfOrd, b::NfOrd)
  parent(a) != parent(b) && error("Orders must have same ambient number field")
  gcd(index(a), index(b)) != 1 && error("Indices must be coprime")
  aB = basis_mat(a)
  bB = basis_mat(b)
  d = degree(a)
  c = sub(_hnf(vcat(bB.den*aB.num, aB.den*bB.num), :lowerleft), d + 1:2*d, 1:d)
  O = Order(nf(a), FakeFmpqMat(c, aB.den*bB.den))
  return O
end

function NfOrdGen(a::NfOrdGenFracIdl)
  z = NfOrdGen(nf(order(a)), a.basis_mat*order(a).basis_mat)
  return z
end


