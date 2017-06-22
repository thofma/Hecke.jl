################################################################################
#
#    NfOrd/NfOrdFracIdl.jl : Fractional ideals of generic
#                               orders in number fields
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

export frac_ideal

################################################################################
#
#  Construction
#
################################################################################

doc"""
***
    frac_ideal(O::NfOrd, A::FakeFmpqMat) -> NfOrdFracIdl

> Creates the fractional ideal of $\mathcal O$ with basis matrix $A$.
"""
function frac_ideal(O::NfOrd, x::FakeFmpqMat)
  y = hnf(x)
  z = NfOrdFracIdl(O, y)
  return z
end

doc"""
***
    frac_ideal(O::NfOrd, A::fmpz_mat, b::fmpz) -> NfOrdFracIdl

> Creates the fractional ideal of $\mathcal O$ with basis matrix $A/b$.
"""
function frac_ideal(O::NfOrd, x::fmpz_mat, y::fmpz)
  y = FakeFmpqMat(x, y)
  z = NfOrdFracIdl(O, y)
  return z
end

frac_ideal(O::NfOrd, x::fmpz_mat, y::Integer) = frac_ideal(O, x, fmpz(y))

doc"""
***
    frac_ideal(O::NfOrd, I::NfOrdIdl) -> NfOrdFracIdl

> Turns the ideal $I$ into a fractional ideal of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::NfOrdIdl)
  z = NfOrdFracIdl(O, x, fmpz(1))
  return z
end

doc"""
***
    frac_ideal(O::NfOrd, I::NfOrdIdl, b::fmpz) -> NfOrdFracIdl

> Creates the fractional ideal $I/b$ of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::NfOrdIdl, y::fmpz)
  z = NfOrdFracIdl(O, x, deepcopy(y)) # deepcopy x?
  return z
end

frac_ideal(O::NfOrd, x::NfOrdIdl, y::Integer) = frac_ideal(O, x, fmpz(y))

doc"""
***
    frac_ideal(O::NfOrd, a::nf_elem) -> NfOrdFracIdl

> Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::nf_elem)
  z = NfOrdFracIdl(O, deepcopy(x))
  return z
end

doc"""
***
    frac_ideal(O::NfOrd, a::NfOrdElem) -> NfOrdFracIdl

> Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::NfOrdElem)
  z = NfOrdFracIdl(O, elem_in_nf(x))
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

export basis_mat, norm, inv, ==, *, integral_split

export parent, order, basis_mat, basis_mat_inv, basis, norm,
       ring_of_multipliers, ==

################################################################################
#
#  Parent
#
################################################################################

parent(a::NfOrdFracIdl) = a.parent

################################################################################
#
#  Order
#
################################################################################

order(a::NfOrdFracIdlSet) = a.order

order(a::NfOrdFracIdl) = order(parent(a))

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

doc"""
***
    basis_mat_inv(I::NfOrdFracIdl) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $I$.
"""
function basis_mat_inv(a::NfOrdFracIdl)
  if isdefined(a, :basis_mat_inv)
    return deepcopy(a.basis_mat_inv)
  else
    a.basis_mat_inv = inv(basis_mat(a))
    return deepcopy(a.basis_mat_inv)
  end
end

################################################################################
#
#  Basis
#
################################################################################

doc"""
***
    basis(I::NfOrdFracIdl) -> Array{nf_elem, 1}

> Returns the $\mathbf Z$-basis of $I$.
"""
function basis(a::NfOrdFracIdl)
  B = basis_mat(a)
  d = degree(order(a))
  O = order(a)
  K = nf(O)
  Oba = O.basis_nf
  res = Array{nf_elem}(d)

  for i in 1:d
    z = K()
    for j in 1:d
      z = z + B.num[i, j]*Oba[j]
    end
    z = divexact(z, B.den)
    res[i] = z
  end

  return res
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::NfOrdFracIdl, dict::ObjectIdDict)
  z = NfOrdFracIdl(deepcopy(x.num), deepcopy(x.den))
  if isdefined(x, :basis_mat)
    z.basis_mat = deepcopy(x.basis_mat)
  end
  return z
end

################################################################################
#
#  Basis matrix
#
################################################################################

doc"""
***
    basis_mat(I::NfOrdFracIdl) -> FakeFmpqMat

> Returns the basis matrix of $I$ with respect to the basis of the order.
"""
function basis_mat(x::NfOrdFracIdl)
  if isdefined(x, :basis_mat)
    return deepcopy(x.basis_mat)
  else
    x.basis_mat = FakeFmpqMat(basis_mat(num(x)), den(x))
    return deepcopy(x.basis_mat)
  end
end

################################################################################
#
#  Numerator and denominator
#
################################################################################

num(x::NfOrdFracIdl) = x.num

den(x::NfOrdFracIdl) = x.den

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, s::NfOrdFracIdlSet)
   print(io, "Set of fractional ideals of ")
   print(io, s.order)
end

function show(io::IO, id::NfOrdFracIdl)
  print(io, "1//", id.den, " * ")
  show(io, id.num)
end

################################################################################
#
#  Norm
#
################################################################################

doc"""
***
    norm(I::NfOrdFracIdl) -> fmpq

> Returns the norm of $I$
"""
function norm(A::NfOrdFracIdl)
  if isdefined(A, :norm)
    return deepcopy(A.norm)
  else
    A.norm = norm(A.num)//A.den^degree(A.num.parent.order)
    return deepcopy(A.norm)
  end
end

################################################################################
#
#  Minimum
#
################################################################################

function minimum(A::NfOrdFracIdl)
  return minimum(A.num)//A.den
end

################################################################################
#
#  Inverse
#
################################################################################

doc"""
***
    inv(A::NfOrdFracIdl) -> NfOrdFracIdl

> Returns the fractional ideal $B$ such that $AB = \mathcal O$.
"""
function inv(A::NfOrdFracIdl)
  B = inv(A.num)
  g = gcd(B.den, A.den)
  B.den = divexact(B.den, g)
  a = divexact(A.den, g)
  return prod_by_int(B, a)
end

################################################################################
#
#  Simplification
#
################################################################################

function simplify_exact(A::NfOrdFracIdl)
  g = A.den

  A.den = divexact(A.den, g)

  @assert A.den == 1

  if has_2_elem(A.num)
    A.num.gen_one = divexact(A.num.gen_one, g)
    A.num.gen_two = divexact(A.num.gen_two, g)
  end

  if has_minimum(A.num)
    A.num.minimum = divexact(A.num.minimum, g)
  end
  if has_norm(A.num)
    A.num.norm = divexact(A.num.norm, g^degree(A.num.parent.order))
  end
  if has_basis_mat(A.num)
    A.num.basis_mat = divexact(A.num.basis_mat, g)
  end
end

function simplify(A::NfOrdFracIdl)
  simplify(A.num)
  b = basis_mat(A.num)
  g = den(A)
  for i in 1:rows(b)
    for j in 1:cols(b)
      g = gcd(g, b[i, j])
    end
  end

  if g != 1
    if has_2_elem(A.num)
      A.num.gen_one = divexact(A.num.gen_one, g)
      A.num.gen_two = divexact(A.num.gen_two, g)
    end
    A.den = divexact(A.den, g)
    if has_minimum(A.num)
      A.num.minimum = divexact(A.num.minimum, g)
    end
    if has_norm(A.num)
      A.num.norm = divexact(A.num.norm, g^degree(A.num.parent.order))
    end
    if has_basis_mat(A.num)
      A.num.basis_mat = divexact(A.num.basis_mat, g)
    end
  end

#  m = minimum(A.num)
#  println("minimum is $m")
#  g = gcd(m, A.den)
#  println("gcd is $g")
#  println("now do something with $(A.num)")
#  if g != 1
#    if has_2_elem(A.num)
#      A.num.gen_one = divexact(A.num.gen_one, g)
#      A.num.gen_two = divexact(A.num.gen_two, g)
#    end
#    A.den = divexact(A.den, g)
#    if has_minimum(A.num)
#      A.num.minimum = divexact(A.num.minimum, g)
#    end
#    if has_norm(A.num)
#      A.num.norm = divexact(A.num.norm, g^degree(A.num.parent.order))
#    end
#    if has_basis_mat(A.num)
#      A.num.basis_mat = divexact(A.num.basis_mat, g)
#    end
#    simplify(A.num)
#  end
  return A
end

################################################################################
#
#  Primeness
#
################################################################################

isprime_known(A::NfOrdFracIdl) = isprime_known(A.num)

################################################################################
#
#  Equality
#
################################################################################

doc"""
***
    ==(x::NfOrdFracIdl, y::NfOrdFracIdl) -> Bool

> Returns whether $x$ and $y$ are equal.
"""
function ==(A::NfOrdFracIdl, B::NfOrdFracIdl)
  #return B.den * basis_mat(A.num) == A.den * basis_mat(B.num)
  if (!ismaximal_known(order(A)) || (ismaximal_known(order(A)) && !ismaximal(order(A))))
    return basis_mat(A) == basis_mat(B)
  end

  if !isdefined(A, :num) || !isdefined(B, :num)
    return basis_mat(A) == basis_mat(B)
  end
  D = inv(B)
  E = prod(A, D)
  C = simplify(E)
  return norm(C) == 1 && C.den == 1
end

################################################################################
#
#  Binary operations
#
################################################################################

function prod(a::NfOrdFracIdl, b::NfOrdFracIdl)
  A = a.num* b.num
  return NfOrdFracIdl(A, a.den*b.den)
end

doc"""
***
    *(I::NfOrdFracIdl, J::NfOrdFracIdl) -> NfOrdFracIdl

> Returns $IJ$.
"""
*(A::NfOrdFracIdl, B::NfOrdFracIdl) = prod(A, B)

################################################################################
#
#  Powering
#
################################################################################

function ^(A::NfOrdFracIdl, a::Int)
  if a == 0
    B = NfOrdFracIdl(ideal(order(A), 1), fmpz(1))
    return B
  end

  if a == 1
    return A # copy?
  end

  if a < 0
    return inv(A^(-a))
  end

  if a == 2
    return A*A
  end

  if mod(a, 2) == 0
    return (A^div(a, 2))^2
  else
    return A * A^(a - 1)
  end
end

function //(A::NfOrdFracIdl, B::NfOrdFracIdl)
  C = prod(A, inv(B))
  return C
end

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

function prod_by_int(A::NfOrdFracIdl, a::fmpz)
  return NfOrdFracIdl(A.num * a, A.den)
end

function *(A::NfOrdIdl, B::NfOrdFracIdl)
  z = NfOrdFracIdl(A*B.num, B.den)
  return z
end

*(A::NfOrdFracIdl, B::NfOrdIdl) = NfOrdFracIdl(A.num*B, A.den)

function *(A::NfOrdFracIdl, a::nf_elem)
  C = *(A, a*order(A))
  return C
end

*(a::nf_elem, A::NfOrdFracIdl) = A*a

function *(A::NfOrdIdl, a::nf_elem)
  C = *(A, a*order(A))
  return C
end

*(a::nf_elem, A::NfOrdIdl) = A*a

function //(A::NfOrdFracIdl, B::NfOrdIdl)
  C = prod(A, inv(B))
  return C
end

function //(A::NfOrdIdl, B::NfOrdIdl)
  return A*inv(B)
end

function //(A::NfOrdIdl, B::NfOrdFracIdl)
  return A*inv(B)
end

function //(A::NfOrdFracIdl, a::nf_elem)
  C = prod(A, Idl((order(A), inv(a))))
  return C
end

function //(A::NfOrdIdl, d::fmpz)
  return Hecke.NfOrdFracIdl(A, d)
end

function //(A::NfOrdIdl, d::Integer)
  return A//fmpz(d)
end

function +(A::NfOrdIdl, B::NfOrdFracIdl)
  return (A*den(B)+num(B))//den(B)
end

+(A::NfOrdFracIdl, B::NfOrdIdl) = B+A

function +(A::NfOrdFracIdl, B::Hecke.NfOrdFracIdl)
  d = lcm(den(A), den(B))
  ma = div(d, den(A))
  mb = div(d, den(B))
  return (num(A)*ma + num(B)*mb)//d
end

function *(x::nf_elem, y::NfOrd)
  b, z = _check_elem_in_order(den(x, y)*x, y)
  return NfOrdFracIdl(ideal(y, y(z)), den(x, y))
end
################################################################################
#
#  Conversion
#
################################################################################
 
function (ord::NfOrdIdlSet)(b::NfOrdFracIdl)
   b.den > 1 && error("not integral")
   return b.num
end

function ideal(O::NfOrd, a::nf_elem)
  return a*O
end

doc"""
***
    integral_split(A::NfOrdFracIdl) -> NfOrdIdl, NfOrdIdl
> Computes the unique coprime integral ideals $N$ and $D$ s.th. $A = N//D$
"""
function integral_split(A::NfOrdFracIdl)
  d = simplify(inv(A + ideal(order(A), fmpz(1))))
  @assert den(d) == 1
  n = simplify(A*d)
  @assert den(n) == 1
  return num(n), num(d)
end

