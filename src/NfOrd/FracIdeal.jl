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
#  Consistency
#
################################################################################

function isconsistent(x::NfOrdFracIdl)
  return isconsistent(numerator(x))
end

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
***
    frac_ideal(O::NfOrd, A::FakeFmpqMat, A_in_hnf::Bool = false) -> NfOrdFracIdl

> Creates the fractional ideal of $\mathcal O$ with basis matrix $A$. If A_in_hnf
> is set, then it is assumed that the numerator of $A$ is already in lower left
> HNF.
"""
function frac_ideal(O::NfOrd, x::FakeFmpqMat, x_in_hnf::Bool = false)
  !x_in_hnf ? x = hnf(x) : nothing
  z = NfOrdFracIdl(O, x)
  return z
end

@doc Markdown.doc"""
***
    frac_ideal(O::NfOrd, A::fmpz_mat, b::fmpz, A_in_hnf::Bool = false) -> NfOrdFracIdl

> Creates the fractional ideal of $\mathcal O$ with basis matrix $A/b$. If
> A_in_hnf is set, then it is assumed that $A$ is already in lower left HNF.
"""
function frac_ideal(O::NfOrd, x::fmpz_mat, y::fmpz=fmpz(1), x_in_hnf::Bool = false)
  !x_in_hnf ? x = _hnf(x, :lowerleft) : nothing
  y = FakeFmpqMat(x, y)
  z = NfOrdFracIdl(O, y)
  return z
end

frac_ideal(O::NfOrd, x::fmpz_mat, y::Integer) = frac_ideal(O, x, fmpz(y))

@doc Markdown.doc"""
***
    frac_ideal(O::NfOrd, I::NfOrdIdl) -> NfOrdFracIdl

> Turns the ideal $I$ into a fractional ideal of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::NfOrdIdl)
  z = NfOrdFracIdl(O, x, fmpz(1))
  return z
end

@doc Markdown.doc"""
***
    frac_ideal(O::NfOrd, I::NfOrdIdl, b::fmpz) -> NfOrdFracIdl

> Creates the fractional ideal $I/b$ of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::NfOrdIdl, y::fmpz)
  z = NfOrdFracIdl(O, x, deepcopy(y)) # deepcopy x?
  return z
end

frac_ideal(O::NfOrd, x::NfOrdIdl, y::Integer) = frac_ideal(O, x, fmpz(y))

@doc Markdown.doc"""
***
    frac_ideal(O::NfOrd, a::nf_elem) -> NfOrdFracIdl

> Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::nf_elem)
  z = NfOrdFracIdl(O, deepcopy(x))
  return z
end

@doc Markdown.doc"""
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

parent(a::NfOrdFracIdl) = NfOrdFracIdlSet(order(a), false)

function Base.hash(a::NfOrdFracIdl, h::UInt)
  b = simplify(a)
  return hash(b.num, hash(b.den, h))
end

################################################################################
#
#  Order
#
################################################################################

order(a::NfOrdFracIdlSet) = a.order

@doc Markdown.doc"""
    order(a::NfOrdFracIdl) -> NfOrd
> The order that was used to define the ideal $a$.
"""
order(a::NfOrdFracIdl) = a.order

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
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

@doc Markdown.doc"""
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
  res = Array{nf_elem}(undef, d)

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

function Base.deepcopy_internal(x::NfOrdFracIdl, dict::IdDict)
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

@doc Markdown.doc"""
***
    basis_mat(I::NfOrdFracIdl) -> FakeFmpqMat

> Returns the basis matrix of $I$ with respect to the basis of the order.
"""
function basis_mat(x::NfOrdFracIdl)
  if isdefined(x, :basis_mat)
    return deepcopy(x.basis_mat)
  else
    x.basis_mat = FakeFmpqMat(basis_mat(numerator(x)), denominator(x))
    return deepcopy(x.basis_mat)
  end
end

################################################################################
#
#  Numerator and denominator
#
################################################################################

numerator(x::NfOrdFracIdl) = x.num

denominator(x::NfOrdFracIdl) = deepcopy(x.den)

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
  if isdefined(id, :num) && isdefined(id, :den)
    print(io, "1//", id.den, " * ")
    print(io, id.num)
  else
    print(io, "Fractional ideal with basis matrix\n")
    print(io, id.basis_mat)
  end
end

################################################################################
#
#  Norm
#
################################################################################

@doc Markdown.doc"""
***
    norm(I::NfOrdFracIdl) -> fmpq

> Returns the norm of $I$
"""
function norm(A::NfOrdFracIdl)
  if isdefined(A, :norm)
    return deepcopy(A.norm)
  else
    A.norm = norm(A.num)//A.den^degree(order(A))
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

@doc Markdown.doc"""
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

function simplify_exact!(A::NfOrdFracIdl)
  g = A.den

  A.den = fmpz(1)
  A.num = divexact(A.num, g)
end


function simplify(A::NfOrdFracIdl)
  simplify(A.num)

  if has_2_elem(A.num)
    ZK = order(A)
    g = Base.reduce(gcd, elem_in_basis(ZK(A.num.gen_two)))
    g = gcd(g, A.den)
    g = gcd(g, A.num.gen_one)
  else  
    b = basis_mat(A.num, copy = false)
    g = gcd(denominator(A), content(b))
  end  

  if g != 1
    A.num = divexact(A.num, g)
    A.den = divexact(A.den, g)
  end

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

@doc Markdown.doc"""
***
    ==(x::NfOrdFracIdl, y::NfOrdFracIdl) -> Bool

> Returns whether $x$ and $y$ are equal.
"""
function ==(A::NfOrdFracIdl, B::NfOrdFracIdl)
  #return B.den * basis_mat(A.num) == A.den * basis_mat(B.num)
  if !ismaximal_known(order(A)) || !ismaximal(order(A))
    return basis_mat(A) == basis_mat(B)
  end

  if !isdefined(A, :num) || !isdefined(B, :num)
    return basis_mat(A) == basis_mat(B)
  end
  D = inv(B)
  E = prod(A, D)
  C = simplify(E)
  return isone(C.den) && isone(norm(C))
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

@doc Markdown.doc"""
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

*(A::NfOrdFracIdl, a::fmpz) = prod_by_int(A, a)
*(a::fmpz, A::NfOrdFracIdl) = prod_by_int(A, a)

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
  return (A*denominator(B)+numerator(B))//denominator(B)
end

+(A::NfOrdFracIdl, B::NfOrdIdl) = B+A

function +(A::NfOrdFracIdl, B::Hecke.NfOrdFracIdl)
  d = lcm(denominator(A), denominator(B))
  ma = div(d, denominator(A))
  mb = div(d, denominator(B))
  return (numerator(A)*ma + numerator(B)*mb)//d
end

function *(x::nf_elem, y::NfOrd)
  b, z = _check_elem_in_order(denominator(x, y)*x, y)
  return NfOrdFracIdl(ideal(y, y(z)), denominator(x, y))
end

################################################################################
#
#  Ad hoc comparison
#
################################################################################

function ==(A::NfOrdIdl, B::NfOrdFracIdl)
  if order(A) !== order(B)
    return false
  end

  C = simplify(B)

  if C.den != 1 || C.num != A
    return false
  else
    return true
  end
end

==(A::NfOrdFracIdl, B::NfOrdIdl) = B == A

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

@doc Markdown.doc"""
***
    integral_split(A::NfOrdFracIdl) -> NfOrdIdl, NfOrdIdl
> Computes the unique coprime integral ideals $N$ and $D$ s.th. $A = ND^{-1}$
"""
function integral_split(A::NfOrdFracIdl)
  d = simplify(inv(A + ideal(order(A), fmpz(1))))
  @assert denominator(d) == 1
  n = simplify(A*d)
  @assert denominator(n) == 1
  return numerator(n), numerator(d)
end

@doc Markdown.doc"""
    factor(I::NfOrdFracIdl) -> Dict{NfOrdIdl, Int}
> The factorisation of $I$.
"""
function factor(I::NfOrdFracIdl)
  if iszero(norm(I))
    error("Cannot factor zero ideal")
  end
  n, d = integral_split(I)
  fn = factor(n)
  fd = factor(d)
  for (k, v) = fd
    if haskey(fn, k)
      fn[k] -= v
    else
      fn[k] = -v
    end
  end  
  return fn  
end

function one(A::NfOrdFracIdl)
  return NfOrdFracIdl(ideal(order(A), 1), fmpz(1))
end

@doc Markdown.doc"""
    valuation(A::NfOrdFracIdl, p::NfOrdIdl)
> The valuation of $A$ at $p$.
"""
function valuation(A::NfOrdFracIdl, p::NfOrdIdl)
  return valuation(A.num, p) - valuation(A.den, p)
end

################################################################################
#
#  Coprime ideals
#
################################################################################

#Given I with v_p(I) = 0, returns element a \in I such that v_p(a) = 0
function coprime_to(I::NfOrdFracIdl, p::NfOrdIdl)
  pi = anti_uniformizer(p)
  a = basis(I)[1]
  l = valuation(a, p)
  @assert l >= 0
  if l > 0
    a = pi^l * a
  end
  @assert valuation(a, p) == 0
  @assert denominator(I)*a in numerator(I)
  return a
end
