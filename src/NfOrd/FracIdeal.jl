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

export fractional_ideal

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
    fractional_ideal(O::NfOrd, A::FakeFmpqMat, A_in_hnf::Bool = false) -> NfOrdFracIdl

Creates the fractional ideal of $\mathcal O$ with basis matrix $A$. If A_in_hnf
is set, then it is assumed that the numerator of $A$ is already in lower left
HNF.
"""
function fractional_ideal(O::NfOrd, x::FakeFmpqMat, x_in_hnf::Bool = false)
  !x_in_hnf ? x = hnf(x) : nothing
  z = NfOrdFracIdl(O, x)
  return z
end

@doc Markdown.doc"""
    fractional_ideal(O::NfOrd, A::fmpz_mat, b::fmpz, A_in_hnf::Bool = false) -> NfOrdFracIdl

Creates the fractional ideal of $\mathcal O$ with basis matrix $A/b$. If
A_in_hnf is set, then it is assumed that $A$ is already in lower left HNF.
"""
function fractional_ideal(O::NfOrd, x::fmpz_mat, y::fmpz=fmpz(1), x_in_hnf::Bool = false)
  !x_in_hnf ? x = _hnf(x, :lowerleft) : nothing
  y = FakeFmpqMat(x, y)
  z = NfOrdFracIdl(O, y)
  return z
end

fractional_ideal(O::NfOrd, x::fmpz_mat, y::Integer) = fractional_ideal(O, x, fmpz(y))

@doc Markdown.doc"""
    fractional_ideal(O::NfOrd, I::NfOrdIdl) -> NfOrdFracIdl

Turns the ideal $I$ into a fractional ideal of $\mathcal O$.
"""
function fractional_ideal(O::NfOrd, x::NfOrdIdl)
  z = NfOrdFracIdl(O, x, fmpz(1))
  return z
end

@doc Markdown.doc"""
    fractional_ideal(O::NfOrd, I::NfOrdIdl, b::fmpz) -> NfOrdFracIdl

Creates the fractional ideal $I/b$ of $\mathcal O$.
"""
function fractional_ideal(O::NfOrd, x::NfOrdIdl, y::fmpz)
  z = NfOrdFracIdl(O, x, deepcopy(y)) # deepcopy x?
  return z
end

fractional_ideal(O::NfOrd, x::NfOrdIdl, y::Integer) = fractional_ideal(O, x, fmpz(y))

@doc Markdown.doc"""
    fractional_ideal(O::NfOrd, a::nf_elem) -> NfOrdFracIdl

Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function fractional_ideal(O::NfOrd, x::nf_elem)
  z = NfOrdFracIdl(O, deepcopy(x))
  return z
end

@doc Markdown.doc"""
    fractional_ideal(O::NfOrd, a::NfOrdElem) -> NfOrdFracIdl

Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function fractional_ideal(O::NfOrd, x::NfOrdElem)
  z = NfOrdFracIdl(O, elem_in_nf(x))
  return z
end

function fractional_ideal_from_z_gens(O::NfAbsOrd{S, T}, b::Vector{T}) where {S, T}
  d = degree(O)
  den = lcm([ denominator(bb, O) for bb in b ])
  num = ideal_from_z_gens(O, [ O(den*bb) for bb in b ])
  return fractional_ideal(O, num, den)
end

function fractional_ideal(O::NfOrd, v::Vector{nf_elem})
  if isempty(v)
    return ideal(O, one(nf(O)))
  end
  I = ideal(O, v[1])
  for i = 2:length(v)
    I += ideal(O, v[i])
  end
  return I
end

################################################################################
#
#  String I/O
#
################################################################################

export basis_matrix, norm, inv, ==, *, integral_split

export parent, order, basis_matrix, basis_mat_inv, basis, norm,
       ring_of_multipliers, ==

################################################################################
#
#  Parent
#
################################################################################

parent(a::NfOrdFracIdl) = NfOrdFracIdlSet(order(a), false)

function FracIdealSet(O::NfAbsOrd)
   return NfOrdFracIdlSet(O, false)
end

function Base.hash(a::NfOrdFracIdl, h::UInt)
  b = simplify(a)
  return hash(numerator(b, copy = false), hash(denominator(b, copy = false), h))
end

elem_type(::Type{NfOrdFracIdlSet}) = NfOrdFracIdl

elem_type(::NfOrdFracIdlSet) = NfOrdFracIdl

parent_type(::Type{NfOrdFracIdl}) = NfOrdFracIdlSet

################################################################################
#
#  Order
#
################################################################################

order(a::NfOrdFracIdlSet) = a.order

@doc Markdown.doc"""
    order(a::NfOrdFracIdl) -> NfOrd
The order that was used to define the ideal $a$.
"""
order(a::NfOrdFracIdl) = a.order

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
    basis_mat_inv(I::NfOrdFracIdl) -> FakeFmpqMat

Returns the inverse of the basis matrix of $I$.
"""
function basis_mat_inv(a::NfOrdFracIdl)
  if isdefined(a, :basis_mat_inv)
    return deepcopy(a.basis_mat_inv)
  else
    a.basis_mat_inv = inv(basis_matrix(a))
    return deepcopy(a.basis_mat_inv)
  end
end

################################################################################
#
#  Basis
#
################################################################################

@doc Markdown.doc"""
    basis(I::NfOrdFracIdl) -> Array{nf_elem, 1}

Returns the $\mathbf Z$-basis of $I$.
"""
function basis(a::NfOrdFracIdl)
  B = basis_matrix(a)
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
  z = NfOrdFracIdl(numerator(x), denominator(x))
  if isdefined(x, :basis_matrix)
    z.basis_matrix = deepcopy(x.basis_matrix)
  end
  return z
end

################################################################################
#
#  Basis matrix
#
################################################################################

function assure_has_basis_matrix(a::NfOrdFracIdl)
  if isdefined(a, :basis_matrix)
    return nothing
  end
  if !isdefined(a, :num)
    error("Not a valid fractional ideal")
  end

  a.basis_matrix = FakeFmpqMat(basis_matrix(numerator(a, copy = false)), denominator(a))
  return nothing
end

@doc Markdown.doc"""
    basis_matrix(I::NfOrdFracIdl) -> FakeFmpqMat

Returns the basis matrix of $I$ with respect to the basis of the order.
"""
function basis_matrix(x::NfOrdFracIdl; copy::Bool = true)
  assure_has_basis_matrix(x)
  if copy
    return deepcopy(x.basis_matrix)
  else
    return x.basis_matrix
  end
end

################################################################################
#
#  Numerator and denominator
#
################################################################################

function assure_has_numerator_and_denominator(a::NfOrdFracIdl)
  if isdefined(a, :num) && isdefined(a, :den)
    return nothing
  end
  if !isdefined(a, :basis_matrix)
    error("Not a valid fractional ideal")
  end

  a.num = ideal(order(a), numerator(basis_matrix(a, copy = false)))
  a.den = denominator(basis_matrix(a, copy = false))
  return nothing
end

function numerator(x::NfOrdFracIdl; copy::Bool = true)
  assure_has_numerator_and_denominator(x)
  if copy
    return deepcopy(x.num)
  else
    return x.num
  end
end

function denominator(x::NfOrdFracIdl; copy::Bool = true)
  assure_has_numerator_and_denominator(x)
  if copy
    return deepcopy(x.den)
  else
    return x.den
  end
end

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
    print(io, "1//", denominator(id, copy = false), " * ")
    print(io, numerator(id, copy = false))
  else
    print(io, "Fractional ideal with basis matrix\n")
    print(io, basis_matrix(id, copy = false))
  end
end

################################################################################
#
#  Norm
#
################################################################################

@doc Markdown.doc"""
    norm(I::NfOrdFracIdl) -> fmpq

Returns the norm of $I$
"""
function norm(A::NfOrdFracIdl)
  if isdefined(A, :norm)
    return deepcopy(A.norm)
  else
    A.norm = norm(numerator(A, copy = false))//denominator(A, copy = false)^degree(order(A))
    return deepcopy(A.norm)
  end
end

################################################################################
#
#  Minimum
#
################################################################################

function minimum(A::NfOrdFracIdl)
  return minimum(numerator(A, copy = false))//denominator(A, copy = false)
end

################################################################################
#
#  Inverse
#
################################################################################

@doc Markdown.doc"""
    inv(A::NfOrdFracIdl) -> NfOrdFracIdl

Returns the fractional ideal $B$ such that $AB = \mathcal O$.
"""
function inv(A::NfOrdFracIdl)
  B = inv(numerator(A, copy = false))
  g = gcd(denominator(B, copy = false), denominator(A, copy = false))
  B.den = divexact(denominator(B, copy = false), g)
  a = divexact(denominator(A, copy = false), g)
  return prod_by_int(B, a)
end

################################################################################
#
#  Simplification
#
################################################################################

function simplify_exact!(A::NfOrdFracIdl)
  assure_has_numerator_and_denominator(A)
  g = A.den

  A.den = fmpz(1)
  A.num = divexact(A.num, g)
end


function simplify(A::NfOrdFracIdl)
  assure_has_numerator_and_denominator(A)
  simplify(A.num)

  if has_2_elem(A.num)
    ZK = order(A)
    g = Base.reduce(gcd, coordinates(ZK(A.num.gen_two)))
    g = gcd(g, A.den)
    g = gcd(g, A.num.gen_one)
  else  
    b = basis_matrix(A.num, copy = false)
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

isprime_known(A::NfOrdFracIdl) = isprime_known(numerator(A, copy = false))

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
    ==(x::NfOrdFracIdl, y::NfOrdFracIdl) -> Bool

Returns whether $x$ and $y$ are equal.
"""
function ==(A::NfOrdFracIdl, B::NfOrdFracIdl)
  #return B.den * basis_matrix(A.num) == A.den * basis_matrix(B.num)
  if !ismaximal_known(order(A)) || !ismaximal(order(A))
    return basis_matrix(A, copy = false) == basis_matrix(B, copy = false)
  end

  if !isdefined(A, :num) || !isdefined(B, :num)
    return basis_matrix(A, copy = false) == basis_matrix(B, copy = false)
  end
  D = inv(B)
  E = prod(A, D)
  C = simplify(E)
  return isone(denominator(C, copy = false)) && isone(norm(C))
end

################################################################################
#
#  Binary operations
#
################################################################################

function prod(a::NfOrdFracIdl, b::NfOrdFracIdl)
  A = numerator(a, copy = false)*numerator(b, copy = false)
  return NfOrdFracIdl(A, denominator(a, copy = false)*denominator(b, copy = false))
end

@doc Markdown.doc"""
    *(I::NfOrdFracIdl, J::NfOrdFracIdl) -> NfOrdFracIdl

Returns $IJ$.
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
  return NfOrdFracIdl(numerator(A, copy = false) * a, denominator(A))
end

*(A::NfOrdFracIdl, a::fmpz) = prod_by_int(A, a)
*(a::fmpz, A::NfOrdFracIdl) = prod_by_int(A, a)

function *(A::NfOrdIdl, B::NfOrdFracIdl)
  z = NfOrdFracIdl(A*numerator(B, copy = false), denominator(B))
  return z
end

*(A::NfOrdFracIdl, B::NfOrdIdl) = NfOrdFracIdl(numerator(A, copy = false)*B, denominator(A))

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
  n = A*denominator(B)+numerator(B)
  return n//denominator(B)
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

  if denominator(C, copy = false) != 1 || numerator(C, copy = false) != A
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
  denominator(b, copy = false) > 1 && error("not integral")
  return numerator(b, copy = false)
end

function ideal(O::NfOrd, a::nf_elem)
  return a*O
end

@doc Markdown.doc"""
    integral_split(A::NfOrdFracIdl) -> NfOrdIdl, NfOrdIdl
Computes the unique coprime integral ideals $N$ and $D$ s.th. $A = ND^{-1}$
"""
function integral_split(A::NfOrdFracIdl)
  if isone(A.den)
    return A.num, ideal(order(A), 1)
  end
  I1 = A + ideal(order(A), fmpz(1))
  d = simplify(inv(I1))
  @assert isone(d.den)
  n = simplify(A*d)
  @assert isone(n.den)
  return numerator(n), numerator(d)
end

@doc Markdown.doc"""
    factor(I::NfOrdFracIdl) -> Dict{NfOrdIdl, Int}
The factorisation of $I$.
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
The valuation of $A$ at $p$.
"""
function valuation(A::NfOrdFracIdl, p::NfOrdIdl)
  return valuation(numerator(A, copy = false), p) - valuation(denominator(A, copy = false), p)
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

################################################################################
#
#  Colon
#
################################################################################

function colon(I::NfOrdFracIdl, J::NfOrdFracIdl)
  # Let I = a/c and J = b/d, a and b integral ideals, c, d \in Z, then
  # \{ x \in K | xJ \subseteq I \} = \{ x \in K | xcb \subseteq da \}

  II = numerator(I, copy = false)*denominator(J, copy = false)
  JJ = numerator(J, copy = false)*denominator(I, copy = false)
  return colon(II, JJ)
end

################################################################################
#
#  Move ideals to another order
#
################################################################################

function extend(I::NfOrdFracIdl, O::NfAbsOrd)
  J = extend(numerator(I, copy = false), O)
  return fractional_ideal(O, J, denominator(I, copy = false))
end

*(I::NfOrdFracIdl, O::NfAbsOrd) = extend(I, O)
*(O::NfAbsOrd, I::NfOrdFracIdl) = extend(I, O)

function _as_fractional_ideal_of_smaller_order(O::NfAbsOrd, I::NfAbsOrdIdl)
  M = basis_matrix(I, copy = false)
  M = M*basis_matrix(order(I), copy = false)*basis_mat_inv(O, copy = false)
  return fractional_ideal(O, M)
end

function _as_fractional_ideal_of_smaller_order(O::NfAbsOrd, I::NfOrdFracIdl)
  J = _as_fractional_ideal_of_smaller_order(O, numerator(I, copy = false))
  return nf(O)(fmpq(1, denominator(I, copy = false)))*J
end
