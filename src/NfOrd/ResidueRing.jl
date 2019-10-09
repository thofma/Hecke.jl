################################################################################
#
#  NfOrd/ResidueRing.jl : Quotients of maximal orders of number fields
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
# (C) 2016 Tommy Hofmann
#
################################################################################

export NfOrdQuoRing, NfOrdQuoRingElem, quo, *, -, ==, deepcopy, divrem,
       gcd, inv, parent, show, divexact, isone, iszero, howell_form,
       strong_echelon_form, triangularize, det, euclid, xxgcd, annihilator

################################################################################
#
#  Assert
#
################################################################################

add_assert_scope(:NfOrdQuoRing)

set_assert_level(:NfOrdQuoRing, 0)

################################################################################
#
#  Field access
#
################################################################################

function elem_type(::Type{AbsOrdQuoRing{S, T}}) where {S, T}
  U = elem_type(S)
  return AbsOrdQuoRingElem{S, T, U}
end

function elem_type(::AbsOrdQuoRing{S, T}) where {S, T}
  U = elem_type(S)
  return AbsOrdQuoRingElem{S, T, U}
end

base_ring(Q::AbsOrdQuoRing) = Q.base_ring

ideal(Q::AbsOrdQuoRing) = Q.ideal

basis_matrix(Q::AbsOrdQuoRing) = Q.basis_matrix

parent(x::AbsOrdQuoRingElem) = x.parent

parent_type(::Type{AbsOrdQuoRingElem{S, T, U}}) where {S, T, U} = AbsOrdQuoRing{S, T}

################################################################################
#
#  Hashing
#
################################################################################

hash(x::AbsOrdQuoRingElem, h::UInt) = hash(x.elem, h)

################################################################################
#
#  Functions to allow polynomial and polynomial ring constructions
#
################################################################################

needs_parentheses(::NfOrdQuoRingElem) = true

isnegative(::NfOrdQuoRingElem) = false

Nemo.promote_rule(::Type{NfOrdQuoRingElem},
                                ::Type{S}) where {S <: Integer} = NfOrdQuoRingElem

Nemo.promote_rule(::Type{NfOrdQuoRingElem}, ::Type{fmpz}) = NfOrdQuoRingElem

################################################################################
#
#  Copying
#
################################################################################

Base.deepcopy_internal(x::AbsOrdQuoRingElem, dict::IdDict) =
        AbsOrdQuoRingElem(parent(x), Base.deepcopy_internal(x.elem, dict))

#copy(x::NfOrdQuoRingElem) = deepcopy(x)

################################################################################
#
#  I/O
#
################################################################################

function show(io::IO, Q::AbsOrdQuoRing)
  print(io, "Quotient of $(Q.base_ring)")
end

function show(io::IO, x::AbsOrdQuoRingElem)
  print(io, "$(x.elem)")
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (Q::AbsOrdQuoRing{S, T})(x::U) where {S, T, U}
  parent(x) !== base_ring(Q) && error("Cannot coerce element into the quotient ring")
  return AbsOrdQuoRingElem(Q, x)
end

function (Q::AbsOrdQuoRing)(x::Integer)
  return Q(base_ring(Q)(x))
end

function (Q::AbsOrdQuoRing)(x::fmpz)
  return Q(base_ring(Q)(x))
end

################################################################################
#
#  Quotient function
#  
# (and standard helpers)
#
################################################################################

@doc Markdown.doc"""
    quo(O::NfOrd, I::NfOrdIdl) -> NfOrdQuoRing, Map
    quo(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl) -> AbsOrdQuoRing, Map
The quotient ring $O/I$ as a ring together with the section $M: O/I \to O$.
The pointwise inverse of $M$ is the canonical projection $O\to O/I$.
"""

function quo(O::Union{NfAbsOrd, AlgAssAbsOrd}, I::Union{NfAbsOrdIdl, AlgAssAbsOrdIdl}; type::Symbol = :ring)
  @assert order(I) === O
  # We should check that I is not zero
  if type == :ring
    Q = AbsOrdQuoRing(O, I)
    f = AbsOrdQuoMap(O, Q)
    return Q, f
  elseif type == :group
    f = GrpAbFinGenToNfOrdQuoNfOrd(O, I)
    return domain(f), f
  else
    error("Type $type not supported")
  end
end

@doc Markdown.doc"""
    ResidueRing(O::NfOrd, I::NfOrdIdl) -> NfOrdQuoRing
    ResidueRing(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl) -> AbsOrdQuoRing
The quotient ring $O$ modulo $I$ as a new ring.
"""
Nemo.ResidueRing(O::Union{NfAbsOrd, AlgAssAbsOrd}, I::Union{NfAbsOrdIdl, AlgAssAbsOrdIdl}) = AbsOrdQuoRing(O, I)

@doc Markdown.doc"""
    lift(O::NfOrd, a::NfOrdQuoRingElem) -> NfOrdElem
Returns a lift of $a$ back to $O$.
"""
function lift(O::NfOrd, a::NfOrdQuoRingElem)
  f = NfOrdQuoMap(O, parent(a))
  return preimage(f, a)
end

################################################################################
#
#  Parent check
#
################################################################################

function check_parent(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  if parent(x) !== parent(y)
    error("Elements must have same parents")
  end
  return true
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  check_parent(x, y)
  return parent(x)(x.elem + y.elem)
end

function -(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  check_parent(x, y)
  return parent(x)(x.elem - y.elem)
end

function -(x::AbsOrdQuoRingElem)
  return parent(x)(-x.elem)
end

function *(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  check_parent(x, y)
  return parent(x)(x.elem * y.elem)
end

function mul!(z::AbsOrdQuoRingElem, x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  z.elem = mul!(z.elem, x.elem, y.elem)
  z.elem = mod!(z.elem, parent(z))
  return z
end

function add!(z::AbsOrdQuoRingElem, x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  z.elem = add!(z.elem, x.elem, y.elem)
  z.elem = mod!(z.elem, parent(z))
  return z
end

function sub!(z::AbsOrdQuoRingElem, x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  z.elem = sub!(z.elem, x.elem, y.elem)
  z.elem = mod!(z.elem, parent(z))
  return z
end

function *(x::Integer, y::AbsOrdQuoRingElem)
  return parent(y)(x * y.elem)
end

*(x::AbsOrdQuoRingElem, y::Integer) = y*x

function *(x::fmpz, y::AbsOrdQuoRingElem)
  return parent(y)(x * y.elem)
end

*(x::AbsOrdQuoRingElem, y::fmpz) = y*x

function ^(a::AbsOrdQuoRingElem, f::fmpz)
  if nbits(f) < 64
    return a^Int(f)
  end
  f == 0 && return one(parent(a))
  f == 1 && return deepcopy(a)
  if f < 0
    f = -f
    a = inv(a)
  end
  b = a^(div(f, 2))
  b *= b
  if isodd(f)
    b *= a
  end
  return b
end

#^(a::NfOrdQuoRingElem, f::Integer) = a^fmpz(f)

function ^(a::AbsOrdQuoRingElem, b::Int)
  if b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  else
    if b < 0
      a = inv(a)
      b = -b
    end
    bit = ~((~UInt(0)) >> 1)
    while (UInt(bit) & b) == 0
      bit >>= 1
    end
    z = deepcopy(a)
    bit >>= 1
    while bit != 0
      z = mul!(z, z, z)
      if (UInt(bit) & b) != 0
        z = mul!(z, z, a)
      end
      bit >>= 1
    end
    return z
  end
end

################################################################################
#
#  Special elements
#
################################################################################

iszero(x::AbsOrdQuoRingElem) = iszero(x.elem)

isone(x::AbsOrdQuoRingElem) = isone(x.elem)

function one(Q::AbsOrdQuoRing)
  return Q(one(Q.base_ring))
end

function zero(Q::AbsOrdQuoRing)
  return Q(zero(Q.base_ring))
end

################################################################################
#
#  Equality
#
################################################################################

function ==(x::AbsOrdQuoRing, y::AbsOrdQuoRing)
  return base_ring(x) === base_ring(y) && ideal(x) == ideal(y)
end

==(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem) = x.elem == y.elem

################################################################################
#
#  Exact division
#
################################################################################

function divexact(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  b, z = isdivisible(x, y)
  @assert b
  return z
end

function isdivisible2(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  check_parent(x, y)

  iszero(y) && error("Dividing by zero")

  if iszero(x)
    return true, zero(parent(x))
  end

  R = parent(x)
  O = base_ring(R)
  d = degree(O)

  
  A = representation_matrix_mod(y.elem, minimum(R.ideal))
  B = parent(x).basis_matrix
  V = hcat(A', B')

  a = coordinates(x.elem, copy = false)
  rhs = matrix(FlintZZ, d, 1, a)
  
  fl, sol = cansolve(V, rhs)
  if !fl
    return fl, zero(R)
  end
  z = R(O(fmpz[sol[i, 1] for i = 1:degree(O)]))
  @hassert :NfOrdQuoRing 1 z*y == x
  return true, z
end

function isdivisible(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  check_parent(x, y)

  iszero(y) && error("Dividing by zero")

  if iszero(x)
    return true, zero(parent(x))
  end

  R = parent(x)
  d = degree(base_ring(R))
  # We cannot solve with non-square matrices.
  # Thus build the matrix
  # ( 1   x    0  )
  # ( 0  M_y   I  )
  # ( 0  M_I   0  ).
  # Compute the UPPER RIGHT HNF ->
  # ( 1   0   u )
  # ( *   *   * )
  # u will be the coefficient vector of the quotient

  V = R.tmp_div
  A = representation_matrix_mod(y.elem, minimum(R.ideal))
  B = parent(x).basis_matrix

  V[1, 1] = 1

  a = coordinates(x.elem, copy = false)

  for i in 1:d
    V[1, 1 + i] = a[i]
  end

  _copy_matrix_into_matrix(V, 2, 2, A)   # this really is a copy
  _copy_matrix_into_matrix(V, 2 + d, 2, B) # this really is a copy

  for i in 1:d
    V[1 + i, d + 1 + i] = 1
  end

  if typeof(base_ring(parent(x))) <: NfOrd
    hnf_modular_eldiv!(V, minimum(R.ideal))
  else
    hnf!(V)
  end

  for i in 2:(d + 1)
    if !iszero(V[1, i])
  #if !iszero(sub(V, 1:1, 2:(d + 1)))
      ccall((:fmpz_mat_zero, :libflint), Nothing, (Ref{fmpz_mat}, ), V)
      return false, zero(parent(x))
    end
  end
  
  z = R(-base_ring(R)(fmpz[ V[1, i] for i in (d + 2):(2*d + 1)])) # V[1, i] is always a copy

  ccall((:fmpz_mat_zero, :libflint), Nothing, (Ref{fmpz_mat}, ), V)

  @hassert :NfOrdQuoRing 1 z*y == x
  return true, z
end

################################################################################
#
#  Strong exact division
#
################################################################################

function _divexact_strong(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  n = euclid(x)
  m = euclid(y)
  @hassert :NfOrdQuoRing 1 mod(n, m) == 0
  target = divexact(n, m)

  #println("target valuation: $target")
  #println("doing first an ordinary divexact with\n $x \n and \n $y")
  q0 = divexact(x, y)
  #println("valuation of first quotient: $(euclid(q0))")

  if euclid(q0) == target
    return q0
  else
    i = annihilator(y)
    #println("generator of annihilator: $i")

    q = q0 + rand(parent(x))*i

    k = 0
    while euclid(q) != target 
      k += 1
      q = q0 + rand(parent(x))*i
      #println("current valuation $(euclid(q))")
      if k > 500
        error("Could not find proper quotion for strong division")
      end
    end
  end

  @hassert :NfOrdQuoRing 1 q*y == x
  @hassert :NfOrdQuoRing 1 euclid(q) *euclid(y) == euclid(x)

  return q
end

################################################################################
#
#  Inverse element
#
################################################################################

function isinvertible(x::AbsOrdQuoRingElem)
  if iszero(x)
    return false, x
  end
  return isdivisible(one(parent(x)), x)
end

function inv(x::AbsOrdQuoRingElem)
  t, y = isinvertible(x)
  @assert t "Element is not invertible"
  return y
end

################################################################################
#
#  Euclidean function
#
################################################################################

function euclid(x::NfOrdQuoRingElem)
  if iszero(x)
    return fmpz(-1)
  end

  U = parent(x).tmp_euc

  d = degree(base_ring(parent(x)))

  _copy_matrix_into_matrix(U, 1, 1, representation_matrix(x.elem))
  _copy_matrix_into_matrix(U, d + 1, 1, parent(x).basis_matrix)

  hnf_modular_eldiv!(U, minimum(parent(x).ideal, copy = false))

  z = fmpz(1)

  for i in 1:degree(base_ring(parent(x)))
    mul!(z, z, U[i, i])
  end

  @hassert :NfOrdQuoRing 1 z == norm(ideal(parent(x.elem), x.elem) + parent(x).ideal)

  return z
end

################################################################################
#
#  Division with remainder
#
################################################################################

function divrem(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)

  b, q = isdivisible(x, y)
  if b
    return q, zero(parent(x))
  end

  e = euclid(y)

  cnt = 0
  while true 
    cnt += 1
    q = rand(parent(x))
    r = x - q*y
    if euclid(r) < e
      @hassert :NfOrdQuoRing 1 euclid(r) < e
      return q, r
    end
    if cnt > 1000
      error("Something odd in divrem for $x $y $(parent(x))")
    end
  end
end

################################################################################
#
#  Random elements
#
################################################################################

function rand(Q::NfOrdQuoRing)
  A = basis_matrix(Q)
  B = basis(base_ring(Q))
  z = rand(fmpz(1):A[1,1]) * B[1]

  for i in 2:nrows(A)
    z = z + rand(fmpz(1):A[i, i]) * B[i]
  end

  return Q(z)
end

################################################################################
#
#  Annihilator
#
################################################################################

function annihilator(x::NfOrdQuoRingElem)
  I = parent(x).ideal
  O = base_ring(parent(x))
  d = degree(O)
  f = NfOrdQuoMap(O, parent(x))
  U = parent(x).tmp_ann
  # We first compute a Z-basis of the annihilator ideal
  # The basis is the kernel of the following matrix
  # ( M_I )
  # ( M_x )
   _copy_matrix_into_matrix(U, 1, 1, representation_matrix(x.elem))
   _copy_matrix_into_matrix(U, d + 1, 1, I.basis_matrix)

  m = left_kernel(U)[2]
  I = ideal(O, _hnf_modular_eldiv(sub(m, 1:degree(O), 1:degree(O)),
                                  minimum(I), :lowerleft))
  z = f(I)
  #@assert iszero(z*x)
  return z
end

################################################################################
#
#  GCD
#
################################################################################

function gcd(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  Q = parent(x)
  O = base_ring(Q)

  if iszero(x)
    if iszero(y)
      return zero(Q)
    else
      return y
    end
  else
    if iszero(y)
      return x
    end
  end

  I = ideal(O, x.elem) + ideal(O, y.elem)

  f = NfOrdQuoMap(O, parent(x))

  return f(I)
end

################################################################################
#
#  Extended extended GCD
#
################################################################################

function xxgcd(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  Q = parent(x)
  O = base_ring(Q)

  d = degree(O)

  if iszero(x)
    return deepcopy(y), Q(O(0)), Q(O(1)), Q(O(-1)), Q(O(0))
  elseif iszero(y)
    return deepcopy(x), Q(O(1)), Q(O(0)), Q(O(0)), Q(O(1))
  end

  g = gcd(x, y)

  e = _divexact_strong(x, g)
  f = _divexact_strong(y, g)

  M_e = representation_matrix(e.elem)
  M_f = representation_matrix(f.elem)

  M_I = Q.basis_matrix

  # let us build
  # ( 1  Q(1) 0  0 )
  # ( 0  M_e  I  0 )
  # ( 0  M_f  0  I )
  # ( 0  M_I  0  0 )

  a = coordinates(one(O), copy = false)

  V = parent(x).tmp_xxgcd

  V[1, 1] = 1

  for i in 1:d
    V[1, 1 + i] = a[i]
  end

  Hecke._copy_matrix_into_matrix(V, 2, 2, M_e)
  Hecke._copy_matrix_into_matrix(V, d + 2, 2, M_f)
  Hecke._copy_matrix_into_matrix(V, 2*d + 2, 2, M_I)

  for i in 1:2*d
    V[1+i, 1 + d + i] = 1
  end

  #U = V

  hnf_modular_eldiv!(V, minimum(Q.ideal))

  u = Q(-O([ V[1,i] for i in (d + 2):(2*d + 1)]))
  v = Q(-O([ V[1,i] for i in (2*d + 2):(3*d + 1)]))

  @hassert :NfOrdQuoRing 1 Q(O(1)) == u*e - (v*(-f))

  ccall((:fmpz_mat_zero, :libflint), Nothing, (Ref{fmpz_mat}, ), V)

  return g, u, v, -f, e
end

function (M::Generic.MatSpace{NfOrdQuoRingElem})(x::Generic.MatSpaceElem{NfOrdElem})
  z = map(base_ring(M), x.entries)::Array{NfOrdQuoRingElem, 2}
  return M(z)::Generic.MatSpaceElem{NfOrdQuoRingElem}
end

################################################################################
#
#  Compute the probability
#
################################################################################

# Just for debugging purposes
# This governs the runtime of the probablistic algorithms.
function probablity(O::NfOrdQuoRing)
  p = 1.0
  I = O.ideal
  f = factor(norm(I))
  for (P, e) in f
    if valuation(I, P) > 0
      p = p * (1 - 1/Float64(norm(P)))
    end
  end
  return p
end


################################################################################
#
#  Group Structure
#
################################################################################

@doc Markdown.doc"""
    group_structure(Q::NfOrdQuoRing) -> GrpAbFinGenSnf

Returns an abelian group with the structure of (Q,+).
"""
function group_structure(Q::NfOrdQuoRing)
  i = ideal(Q)
  fac = factor(i)
  structure = Vector{fmpz}()
  for (p,vp) in fac
    pnum = minimum(p)
    e = valuation(pnum,p)
    f = factor(norm(p))[pnum]
    q, r = divrem(vp+e-1,e)
    structure_pvp = [repeat([pnum^q],inner=[Int((r+1)*f)]) ; repeat([pnum^(q-1)],inner=[Int((e-r-1)*f)])]
    append!(structure,structure_pvp)
  end
  G = DiagonalGroup(structure)
  S, Smap = snf(G)
  return S
end
