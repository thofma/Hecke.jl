################################################################################
#
#   NfMaxOrd/FracIdl.jl : Fractional ideals of maximal orders in
#                         absolute number fields
#
# This file is part of Hecke.
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
# (C) 2015, 2016 Tommy Hofmann
# (C) 2016, 2016 Claus Fieker
#
################################################################################

export basis_mat, norm, inv, ==, *

################################################################################
#
#  Deepcopy
#
################################################################################

function deepcopy(x::NfMaxOrdFracIdl)
  z = NfMaxOrdFracIdl(deepcopy(x.num), deepcopy(x.den))
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
function basis_mat(x::NfMaxOrdFracIdl)
  return FakeFmpqMat(basis_mat(num(x)), den(x))
end

################################################################################
#
#  Numerator and denominator
#
################################################################################

num(x::NfMaxOrdFracIdl) = x.num

den(x::NfMaxOrdFracIdl) = x.den

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, s::NfMaxOrdFracIdlSet)
   print(io, "Set of fractional ideals of ")
   print(io, s.order)
end

function show(io::IO, id::NfMaxOrdFracIdl)
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
function norm(A::NfMaxOrdFracIdl)
  return norm(A.num)//A.den^degree(A.num.parent.order)
end

################################################################################
#
#  Minimum
#
################################################################################

function minimum(A::NfMaxOrdFracIdl)
  return minimum(A.num)//A.den
end

################################################################################
#
#  Inverse
#
################################################################################

doc"""
    inv(A::NfMaxOrdFracIdl) -> NfMaxOrdFracIdl

> Returns the fractional ideal $B$ such that $AB = \mathcal O$.
"""
function inv(A::NfMaxOrdFracIdl)
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

function simplify_exact(A::NfMaxOrdFracIdl)
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

function simplify(A::NfMaxOrdFracIdl)
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

is_prime_known(A::NfMaxOrdFracIdl) = is_prime_known(A.num)

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
function ==(A::NfMaxOrdFracIdl, B::NfMaxOrdFracIdl)
  #return B.den * basis_mat(A.num) == A.den * basis_mat(B.num)
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

function prod(a::NfMaxOrdFracIdl, b::NfMaxOrdFracIdl)
  A = a.num* b.num
  return NfMaxOrdFracIdl(A, a.den*b.den)
end

doc"""
***
    *(I::NfMaxOrdFracIdl, J::NfMaxOrdFracIdl) -> NfMaxOrdFracIdl

> Returns $IJ$.
"""
*(A::NfMaxOrdFracIdl, B::NfMaxOrdFracIdl) = prod(A, B)

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

function prod_by_int(A::NfMaxOrdFracIdl, a::fmpz)
  return NfMaxOrdFracIdl(A.num * a, A.den)
end

function *(A::NfMaxOrdIdl, B::NfMaxOrdFracIdl)
  z = NfMaxOrdFracIdl(A*B.num, B.den)
  return z
end

*(A::NfMaxOrdFracIdl, B::NfMaxOrdIdl) = NfMaxOrdFracIdl(A.num*B, A.den)

function *(A::NfMaxOrdFracIdl, a::nf_elem)
  C = *(A, a*order(A))
  return C
end

*(a::nf_elem, A::NfMaxOrdFracIdl) = A*a

function *(A::NfMaxOrdIdl, a::nf_elem)
  C = *(A, a*order(A))
  return C
end

*(a::nf_elem, A::NfMaxOrdIdl) = A*a

function /(A::NfMaxOrdFracIdl, B::NfMaxOrdIdl)
  C = prod(A, inv(B))
  return C
end

function /(A::NfMaxOrdFracIdl, a::nf_elem)
  C = prod(A, Idl((order(A), inv(a))))
  return C
end

*(x::nf_elem, y::NfMaxOrdFracIdl) = y * x

function *(x::nf_elem, y::NfMaxOrd)
  b, z = _check_elem_in_order(den(x, y)*x, y)
  return NfMaxOrdFracIdl(ideal(y, y(z)), den(x, y))
end

################################################################################
#
#  Conversion
#
################################################################################
 
function call(ord::NfMaxOrdIdlSet, b::NfMaxOrdFracIdl)
   b.den > 1 && error("not integral")
   return b.num
end

