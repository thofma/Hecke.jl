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

function is_consistent(x::NfOrdFracIdl)
  return is_consistent(numerator(x))
end

################################################################################
#
#  Predicates
#
################################################################################

function iszero(x::NfAbsOrdFracIdl)
  return iszero(numerator(x))
end

#################################################################################
#
#  Parent constructor
#
#################################################################################

function FractionalIdealSet(O::NfOrd)
  return NfAbsOrdFracIdlSet{AnticNumberField, nf_elem}(O)
end

################################################################################
#
#  Construction
#
################################################################################

@doc raw"""
    fractional_ideal(O::NfAbsOrd, A::FakeFmpqMat, A_in_hnf::Bool = false) -> NfAbsOrdFracIdl

Creates the fractional ideal of $\mathcal O$ with basis matrix $A$. If `A_in_hnf`
is set, then it is assumed that the numerator of $A$ is already in lower left
HNF.
"""
function fractional_ideal(O::NfAbsOrd, x::FakeFmpqMat, x_in_hnf::Bool = false)
  !x_in_hnf ? x = hnf(x) : nothing
  z = NfAbsOrdFracIdl(O, x)
  return z
end

@doc raw"""
    fractional_ideal(O::NfAbsOrd, A::ZZMatrix, b::ZZRingElem, A_in_hnf::Bool = false) -> NfAbsOrdFracIdl

Creates the fractional ideal of $\mathcal O$ with basis matrix $A/b$. If
`A_in_hnf` is set, then it is assumed that $A$ is already in lower left HNF.
"""
function fractional_ideal(O::NfAbsOrd, x::ZZMatrix, y::ZZRingElem=ZZRingElem(1), x_in_hnf::Bool = false)
  !x_in_hnf ? x = _hnf(x, :lowerleft) : nothing
  y = FakeFmpqMat(x, y)
  z = NfAbsOrdFracIdl(O, y)
  return z
end

fractional_ideal(O::NfAbsOrd, x::ZZMatrix, y::Integer) = fractional_ideal(O, x, ZZRingElem(y))

@doc raw"""
    fractional_ideal(O::NfAbsOrd, I::NfAbsOrdIdl) -> NfAbsOrdFracIdl

Turns the ideal $I$ into a fractional ideal of $\mathcal O$.
"""
function fractional_ideal(O::NfAbsOrd, x::NfAbsOrdIdl)
  order(x) !== O && error("Incompatible orders")
  z = NfAbsOrdFracIdl(O, x, ZZRingElem(1))
  return z
end

@doc raw"""
    fractional_ideal(O::NfAbsOrd, I::NfAbsOrdIdl, b::ZZRingElem) -> NfAbsOrdFracIdl

Creates the fractional ideal $I/b$ of $\mathcal O$.
"""
function fractional_ideal(O::NfAbsOrd, x::NfAbsOrdIdl, y::ZZRingElem)
  @assert order(x) === O
  z = NfAbsOrdFracIdl(O, x, deepcopy(y)) # deepcopy x?
  return z
end

fractional_ideal(x::NfAbsOrdIdl, y::ZZRingElem) = fractional_ideal(order(x), x, y)

fractional_ideal(x::NfAbsOrdIdl) = fractional_ideal(order(x), x, ZZRingElem(1))

fractional_ideal(O::NfAbsOrd, x::NfAbsOrdIdl, y::Integer) = fractional_ideal(O, x, ZZRingElem(y))

@doc raw"""
    fractional_ideal(O::NfAbsOrd, a::nf_elem) -> NfAbsOrdFracIdl

Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function fractional_ideal(O::NfAbsOrd, x::NumFieldElem)
  @assert parent(x) == nf(O)
  z = NfAbsOrdFracIdl(O, deepcopy(x))
  return z
end

@doc raw"""
    fractional_ideal(O::NfAbsOrd, a::NfAbsOrdElem) -> NfAbsOrdFracIdl

Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function fractional_ideal(O::NfAbsOrd, x::NfAbsOrdElem)
  @assert parent(x) === O
  z = NfAbsOrdFracIdl(O, elem_in_nf(x))
  return z
end

function fractional_ideal_from_z_gens(O::NfAbsOrd{S, T}, b::Vector{T}) where {S, T}
  d = degree(O)
  den = lcm([ denominator(bb, O) for bb in b ])
  num = ideal_from_z_gens(O, [ O(den*bb) for bb in b ])
  return fractional_ideal(O, num, den)
end

function fractional_ideal(O::NfAbsOrd{S, T}, v::Vector{T}) where {S, T}
  if isempty(v)
    return ideal(O, one(nf(O)))
  end
  I = ideal(O, v[1])
  for i = 2:length(v)
    if iszero(v[i])
      continue
    end
    I += ideal(O, v[i])
  end
  return I
end

*(R::NfAbsOrd, x::QQFieldElem) = fractional_ideal(R, nf(R)(x))

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

parent(a::NfAbsOrdFracIdl{S, T}) where {S, T} = NfAbsOrdFracIdlSet{S, T}(order(a), false)

function FracIdealSet(O::NfAbsOrd{S, T}) where {S, T}
  return NfAbsOrdFracIdlSet{S, T}(O, false)
end

function Base.hash(a::NfAbsOrdFracIdl, h::UInt)
  b = simplify(a)
  return hash(numerator(b, copy = false), hash(denominator(b, copy = false), h))
end

elem_type(::Type{NfAbsOrdFracIdlSet{S, T}}) where {S, T} = NfAbsOrdFracIdl{S, T}

elem_type(::NfAbsOrdFracIdlSet{S, T}) where {S, T} = NfAbsOrdFracIdl{S, T}

parent_type(::Type{NfAbsOrdFracIdl{S, T}}) where {S, T} = NfAbsOrdFracIdlSet{S, T}

==(a::NfAbsOrdFracIdlSet, b::NfAbsOrdFracIdlSet) = order(a) === order(b)

################################################################################
#
#  Order
#
################################################################################

order(a::NfAbsOrdFracIdlSet) = a.order

@doc raw"""
    order(a::NfAbsOrdFracIdl) -> NfAbsOrd

The order that was used to define the ideal $a$.
"""
order(a::NfAbsOrdFracIdl) = a.order

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc raw"""
    basis_mat_inv(I::NfAbsOrdFracIdl) -> FakeFmpqMat

Returns the inverse of the basis matrix of $I$.
"""
function basis_mat_inv(a::NfAbsOrdFracIdl)
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

@doc raw"""
    basis(I::NfAbsOrdFracIdl) -> Vector{nf_elem}

Returns the $\mathbf Z$-basis of $I$.
"""
function basis(a::NfAbsOrdFracIdl{S, T}) where {S, T}
  B = basis_matrix(a)
  d = degree(order(a))
  O = order(a)
  K = nf(O)
  Oba = O.basis_nf
  res = Array{T}(undef, d)
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

function Base.deepcopy_internal(x::NfAbsOrdFracIdl, dict::IdDict)
  z = NfAbsOrdFracIdl(numerator(x), denominator(x))
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

function assure_has_basis_matrix(a::NfAbsOrdFracIdl)
  if isdefined(a, :basis_matrix)
    return nothing
  end
  if !isdefined(a, :num)
    error("Not a valid fractional ideal")
  end

  a.basis_matrix = FakeFmpqMat(basis_matrix(numerator(a, copy = false)), denominator(a))
  return nothing
end

@doc raw"""
    basis_matrix(I::NfAbsOrdFracIdl) -> FakeFmpqMat

Returns the basis matrix of $I$ with respect to the basis of the order.
"""
function basis_matrix(x::NfAbsOrdFracIdl; copy::Bool = true)
  assure_has_basis_matrix(x)
  if copy
    return deepcopy(x.basis_matrix)
  else
    return x.basis_matrix
  end
end

# For compatibility with AlgAssAbsOrdIdl
function basis_matrix_wrt(A::NfAbsOrdFracIdl, O::NfAbsOrd; copy::Bool = true)
  @assert O === order(A)
  return basis_matrix(A, copy = copy)
end

################################################################################
#
#  Numerator and denominator
#
################################################################################

function assure_has_numerator_and_denominator(a::NfAbsOrdFracIdl)
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

function numerator(x::NfAbsOrdFracIdl; copy::Bool = true)
  assure_has_numerator_and_denominator(x)
  if copy
    return deepcopy(x.num)
  else
    return x.num
  end
end

function denominator(x::NfAbsOrdFracIdl; copy::Bool = true)
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

function show(io::IO, s::NfAbsOrdFracIdlSet)
   print(io, "Set of fractional ideals of ")
   print(io, s.order)
end

function show(io::IO, id::NfAbsOrdFracIdl)
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

@doc raw"""
    norm(I::NfAbsOrdFracIdl) -> QQFieldElem

Returns the norm of $I$.
"""
function norm(A::NfAbsOrdFracIdl)
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

function minimum(A::NfAbsOrdFracIdl)
  return minimum(numerator(A, copy = false))//denominator(A, copy = false)
end

################################################################################
#
#  Inverse
#
################################################################################

@doc raw"""
    inv(A::NfAbsOrdFracIdl) -> NfAbsOrdFracIdl

Returns the fractional ideal $B$ such that $AB = \mathcal O$.
"""
function inv(A::NfAbsOrdFracIdl)
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

function simplify_exact!(A::NfAbsOrdFracIdl)
  assure_has_numerator_and_denominator(A)
  g = A.den

  A.den = ZZRingElem(1)
  A.num = divexact(A.num, g)
end


function simplify(A::NfAbsOrdFracIdl)
  assure_has_numerator_and_denominator(A)
  if isone(A.den)
    return A
  end
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
    simplify(A.num)
    A.den = divexact(A.den, g)
  end

  return A
end

################################################################################
#
#  Primeness
#
################################################################################

is_prime_known(A::NfAbsOrdFracIdl) = is_prime_known(numerator(A, copy = false))

################################################################################
#
#  Equality
#
################################################################################

function ==(A::NfAbsOrdFracIdl, B::NfAbsOrdFracIdl)
  #return B.den * basis_matrix(A.num) == A.den * basis_matrix(B.num)
  if !is_maximal_known(order(A)) || !is_maximal(order(A))
    return basis_matrix(A, copy = false) == basis_matrix(B, copy = false)
  end

  if !isdefined(A, :num) || !isdefined(B, :num)

    return basis_matrix(A, copy = false) == basis_matrix(B, copy = false)
  end

  if isdefined(A, :num) && isdefined(B, :num)
    if A.den == B.den && A.num == B.num
      return true
    end
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

function prod(a::T, b::T) where T <: NfAbsOrdFracIdl
  A = numerator(a, copy = false)*numerator(b, copy = false)
  return NfAbsOrdFracIdl(A, denominator(a, copy = false)*denominator(b, copy = false))
end

*(A::T, B::T) where T <: NfAbsOrdFracIdl = prod(A, B)

################################################################################
#
#  Powering
#
################################################################################

function ^(A::NfAbsOrdFracIdl, a::Int)
  if a == 0
    B = NfAbsOrdFracIdl(ideal(order(A), 1), ZZRingElem(1))
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

function //(A::NfAbsOrdFracIdl, B::NfAbsOrdFracIdl)
  C = prod(A, inv(B))
  return C
end

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

function prod_by_int(A::NfAbsOrdFracIdl, a::ZZRingElem)
  return NfAbsOrdFracIdl(numerator(A, copy = false) * a, denominator(A))
end

*(A::NfAbsOrdFracIdl, a::ZZRingElem) = prod_by_int(A, a)
*(a::ZZRingElem, A::NfAbsOrdFracIdl) = prod_by_int(A, a)

function *(A::NfAbsOrdIdl, B::NfAbsOrdFracIdl)
  z = NfAbsOrdFracIdl(A*numerator(B, copy = false), denominator(B))
  return z
end

*(A::NfAbsOrdFracIdl, B::NfAbsOrdIdl) = NfAbsOrdFracIdl(numerator(A, copy = false)*B, denominator(A))

function *(A::NfAbsOrdFracIdl{S, T}, a::T) where {S <: NumField, T <: NumFieldElem}
  C = *(A, a*order(A))
  return C
end

*(a::T, A::NfAbsOrdFracIdl{S, T}) where {S <: NumField, T <: NumFieldElem} = A*a

function *(A::NfAbsOrdIdl{S, T}, a::T) where {S <: NumField, T <: NumFieldElem}
  C = *(A, a*order(A))
  return C
end

*(a::T, A::NfAbsOrdIdl{S, T}) where {S <: NumField, T <: NumFieldElem} = A*a

function //(A::NfAbsOrdFracIdl{S, T}, B::NfAbsOrdIdl{S, T}) where {S <: NumField, T <: NumFieldElem}
  C = prod(A, inv(B))
  return C
end

function //(A::NfAbsOrdIdl{S, T}, B::NfAbsOrdIdl{S, T}) where {S <: NumField, T <: NumFieldElem}
  return A*inv(B)
end

function //(A::NfAbsOrdIdl{S, T}, B::NfAbsOrdFracIdl{S, T}) where {S <: NumField, T <: NumFieldElem}
  return A*inv(B)
end

function //(A::NfAbsOrdFracIdl{S, T}, a::T) where {S <: NumField, T <: NumFieldElem}
  C = prod(A, Idl((order(A), inv(a))))
  return C
end

function //(A::NfAbsOrdIdl, d::ZZRingElem)
  return Hecke.NfAbsOrdFracIdl(A, d)
end

function //(A::NfAbsOrdIdl, d::Integer)
  return A//ZZRingElem(d)
end

function +(A::NfAbsOrdIdl{S, T}, B::NfAbsOrdFracIdl{S, T}) where {S <: NumField, T <: NumFieldElem}
  if iszero(A)
    return B
  end

  if iszero(B)
    return fractional_ideal(order(A), A)
  end
  n1 = A*denominator(B)
  n = n1 + numerator(B)
  return n//denominator(B)
end

+(A::NfAbsOrdFracIdl{S, T}, B::NfAbsOrdIdl{S, T}) where {S <: NumField, T <: NumFieldElem} = B+A

function +(A::NfAbsOrdFracIdl{S, T}, B::Hecke.NfAbsOrdFracIdl{S, T}) where {S <: NumField, T <: NumFieldElem}
  if iszero(A)
    return B
  end

  if iszero(B)
    return A
  end

  d = lcm(denominator(A), denominator(B))
  ma = div(d, denominator(A))
  mb = div(d, denominator(B))
  return (numerator(A)*ma + numerator(B)*mb)//d
end

function *(x::T, y::NfAbsOrd{S, T}) where {S <: NumField, T <: NumFieldElem}
  d = denominator(x, y)
  return NfAbsOrdFracIdl(ideal(y, y(d*x, false)), d)
end

################################################################################
#
#  Ad hoc comparison
#
################################################################################

function ==(A::NfAbsOrdIdl{S, T}, B::NfAbsOrdFracIdl{S, T}) where {S <: NumField, T <: NumFieldElem}
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

==(A::NfAbsOrdFracIdl{S, T}, B::NfAbsOrdIdl{S, T}) where {S <: NumField, T <: NumFieldElem} = B == A

################################################################################
#
#  Conversion
#
################################################################################

function (ord::NfAbsOrdIdlSet)(b::NfAbsOrdFracIdl)
  denominator(b, copy = false) > 1 && error("not integral")
  return numerator(b, copy = false)
end

function ideal(O::NfAbsOrd{S, T}, a::T) where {S <: NumField, T <: NumFieldElem}
  return a*O
end

@doc raw"""
    integral_split(A::NfAbsOrdFracIdl) -> NfAbsOrdIdl, NfAbsOrdIdl

Computes the unique coprime integral ideals $N$ and $D$ s.th. $A = ND^{-1}$
"""
function integral_split(A::NfAbsOrdFracIdl)
  if isone(A.den)
    return A.num, ideal(order(A), 1)
  end
  I1 = A + ideal(order(A), ZZRingElem(1))
  I2 = inv(I1)
  d = simplify(I2)
  @assert isone(d.den)
  n = simplify(A*d)
  @assert isone(n.den)
  @hassert :NfOrd 1 A == (numerator(n)//numerator(d))
  return numerator(n), numerator(d)
end

@doc raw"""
    factor(I::NfAbsOrdFracIdl) -> Dict{NfAbsOrdIdl, Int}

The factorisation of $I$.
"""
function factor(I::NfAbsOrdFracIdl)
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

function one(A::NfAbsOrdFracIdl)
  return NfAbsOrdFracIdl(ideal(order(A), 1), ZZRingElem(1))
end

@doc raw"""
    valuation(A::NfAbsOrdFracIdl, p::NfAbsOrdIdl)

The valuation of $A$ at $p$.
"""
function valuation(A::NfAbsOrdFracIdl, p::NfAbsOrdIdl)
  return valuation(numerator(A, copy = false), p) - valuation(denominator(A, copy = false), p)
end

################################################################################
#
#  Coprime ideals
#
################################################################################

#Given I with v_p(I) = 0, returns element a \in I such that v_p(a) = 0
function coprime_to(I::NfAbsOrdFracIdl, p::NfAbsOrdIdl)
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

function colon(I::NfAbsOrdFracIdl, J::NfAbsOrdFracIdl)
  # Let I = a/c and J = b/d, a and b integral ideals, c, d \in Z, then
  # \{ x \in K | xJ \subseteq I \} = \{ x \in K | xcb \subseteq da \}

  II = numerator(I, copy = false)*denominator(J, copy = false)
  JJ = numerator(J, copy = false)*denominator(I, copy = false)
  return colon(II, JJ)
end

################################################################################
#
#  Membership of elements
#
################################################################################

#TODO: Use the inclusion element/NfOrdIdl
function in(x::nf_elem, y::NfOrdFracIdl)
  B = inv(basis_matrix(y))
  O = order(y)
  M = zero_matrix(FlintZZ, 1, degree(O))
  t = FakeFmpqMat(M)
  elem_to_mat_row!(t.num, 1, t.den, x)
  v = t*basis_mat_inv(O)
  v = v*B

  return v.den == 1
end

function in(x::T, y::NfOrdFracIdl) where T <: IntegerUnion
  O = order(y)
  return in(O(x), y)
end

function in(x::NfAbsOrdElem, y::NfOrdFracIdl)
  return in(elem_in_nf(x), y)
end

################################################################################
#
#  Move ideals to another order
#
################################################################################

function extend(I::NfAbsOrdFracIdl, O::NfAbsOrd)
  J = extend(numerator(I, copy = false), O)
  return fractional_ideal(O, J, denominator(I, copy = false))
end

*(I::NfAbsOrdFracIdl, O::NfAbsOrd) = extend(I, O)
*(O::NfAbsOrd, I::NfAbsOrdFracIdl) = extend(I, O)

function _as_fractional_ideal_of_smaller_order(O::NfAbsOrd, I::NfAbsOrdIdl)
  M = basis_matrix(I, copy = false)
  M = M*basis_matrix(order(I), copy = false)*basis_mat_inv(O, copy = false)
  return fractional_ideal(O, M)
end

function _as_fractional_ideal_of_smaller_order(O::NfAbsOrd, I::NfAbsOrdFracIdl)
  J = _as_fractional_ideal_of_smaller_order(O, numerator(I, copy = false))
  return nf(O)(QQFieldElem(1, denominator(I, copy = false)))*J
end

################################################################################
#
#  Some basic functions
#
################################################################################

function one(A::NfOrdFracIdlSet)
  return ideal(order(A), 1)//1
end

function copy(A::NfOrdFracIdl)
  return deepcopy(A)
end

function ^(A::NfOrdFracIdl, d::ZZRingElem)
  return A^Int(d)
end
