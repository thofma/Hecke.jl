################################################################################
#
#  AbsSimpleNumFieldOrder/residue_ring.jl : Quotients of maximal orders of number fields
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

################################################################################
#
#  Assertion
#
################################################################################

add_assertion_scope(:AbsOrdQuoRing)

################################################################################
#
#  Field access
#
################################################################################

function elem_type(::Type{AbsOrdQuoRing{S, T}}) where {S, T}
  U = elem_type(S)
  return AbsOrdQuoRingElem{S, T, U}
end

base_ring(Q::AbsOrdQuoRing) = Q.base_ring

base_ring_type(::Type{AbsOrdQuoRing{S, T}}) where {S, T} = S

ideal(Q::AbsOrdQuoRing) = Q.ideal

basis_matrix(Q::AbsOrdQuoRing) = Q.basis_matrix

parent(x::AbsOrdQuoRingElem) = x.parent

parent_type(::Type{AbsOrdQuoRingElem{S, T, U}}) where {S, T, U} = AbsOrdQuoRing{S, T}

(R::AbsOrdQuoRing)() = zero(R)

function simplify!(x::AbsOrdQuoRingElem)
  if x.isreduced
    return x
  end
  mod!(x.elem, parent(x))
  x.isreduced = true
  return x
end

canonical_unit(x::AbsOrdQuoRingElem) = one(parent(x))

################################################################################
#
#  Hashing
#
################################################################################

hash(x::AbsOrdQuoRingElem, h::UInt) = hash(mod(x.elem, parent(x)), h)

################################################################################
#
#  Functions to allow polynomial and polynomial ring constructions
#
################################################################################

Nemo.promote_rule(::Type{AbsSimpleNumFieldOrderQuoRingElem},
                                ::Type{S}) where {S <: Integer} = AbsSimpleNumFieldOrderQuoRingElem

Nemo.promote_rule(::Type{AbsSimpleNumFieldOrderQuoRingElem}, ::Type{ZZRingElem}) = AbsSimpleNumFieldOrderQuoRingElem

################################################################################
#
#  Copying
#
################################################################################

Base.deepcopy_internal(x::AbsOrdQuoRingElem, dict::IdDict) =
        AbsOrdQuoRingElem(parent(x), Base.deepcopy_internal(x.elem, dict))

#copy(x::AbsSimpleNumFieldOrderQuoRingElem) = deepcopy(x)

################################################################################
#
#  I/O
#
################################################################################

function show(io::IO, Q::AbsOrdQuoRing)
  print(io, "Quotient of $(Q.base_ring)")
end

function AbstractAlgebra.expressify(x::AbsOrdQuoRingElem; context = nothing)
  return AbstractAlgebra.expressify(x.elem, context = context)
end

function show(io::IO, x::AbsOrdQuoRingElem)
  print(io, AbstractAlgebra.obj_to_string(x, context = io))
end

################################################################################
#
#  Easy reduction of elements
#
################################################################################

#TODO: Inplace versions of mod
function _easy_mod(x::AbsSimpleNumFieldOrderQuoRingElem)
  Q = parent(x)
  I = Q.ideal
  O = parent(x.elem)
  if is_defining_polynomial_nice(nf(O)) && contains_equation_order(O)
    x.elem = O(mod(x.elem.elem_in_nf, minimum(I, copy = false)), false)
  else
    x.elem = mod(x.elem, I)
  end
  return x
end

function _easy_mod(x::AbsOrdQuoRingElem)
  x.elem = mod(x.elem, parent(x).ideal)
  return x
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (Q::AbsOrdQuoRing{S, T})(x::U) where {S, T, U}
  parent(x) !== base_ring(Q) && error("Cannot coerce element into the quotient ring")
  res = AbsOrdQuoRingElem{S, T, U}(Q, x)
  return _easy_mod(res)
end

function (Q::AbsOrdQuoRing{S, T})(x::Integer) where {S, T}
  res = elem_type(Q)(Q, base_ring(Q)(x))
  return res
end

function (Q::AbsOrdQuoRing{S, T})(x::ZZRingElem) where {S, T}
  res = elem_type(Q)(Q, base_ring(Q)(x))
  return res
end

################################################################################
#
#  Quotient function
#
# (and standard helpers)
#
################################################################################

@doc raw"""
    quo(O::AbsSimpleNumFieldOrder, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldOrderQuoRing, Map
    quo(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl) -> AbsOrdQuoRing, Map

The quotient ring $O/I$ as a ring together with the section $M: O/I \to O$.
The pointwise inverse of $M$ is the canonical projection $O\to O/I$.
"""
function quo(O::Union{AbsNumFieldOrder, AlgAssAbsOrd}, I::Union{AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl})
  @assert order(I) === O
  if O isa AlgAssAbsOrd
    @hassert :AbsOrdQuoRing 1 _test_ideal_sidedness(I, O, :left)
    @hassert :AbsOrdQuoRing 1 _test_ideal_sidedness(I, O, :right)
  end
  # We should check that I is not zero
  Q = AbsOrdQuoRing(O, I)
  f = AbsOrdQuoMap(O, Q)
  return Q, f
end

function quo(O::Union{AbsNumFieldOrder, AlgAssAbsOrd}, I::Union{AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl}, ::Type{FinGenAbGroup})
  f = GrpAbFinGenToNfOrdQuoNfOrd(O, I)
  return domain(f), f
end

@doc raw"""
    residue_ring(O::AbsSimpleNumFieldOrder, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldOrderQuoRing
    residue_ring(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl) -> AbsOrdQuoRing

The quotient ring $O$ modulo $I$ as a new ring.
"""
Nemo.residue_ring(O::Union{AbsNumFieldOrder, AlgAssAbsOrd}, I::Union{AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl}) = AbsOrdQuoRing(O, I)

@doc raw"""
    lift(O::AbsSimpleNumFieldOrder, a::AbsSimpleNumFieldOrderQuoRingElem) -> AbsSimpleNumFieldOrderElem

Returns a lift of $a$ back to $O$.
"""
function lift(O::AbsSimpleNumFieldOrder, a::AbsSimpleNumFieldOrderQuoRingElem)
  f = NfOrdQuoMap(O, parent(a))
  return preimage(f, a)
end

@doc raw"""
    lift(a::AbsSimpleNumFieldOrderQuoRingElem) -> AbsSimpleNumFieldOrderElem

Given an element of the quotient ring $\mathcal O/I$, return a lift in
$\mathcal O$.
"""
function lift(a::AbsSimpleNumFieldOrderQuoRingElem)
  simplify!(a)
  return a.elem
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::AbsOrdQuoRingElem{S, T, U}, y::AbsOrdQuoRingElem{S, T, U}) where {S, T, U}
  check_parent(x, y)
  Q = parent(x)
  return Q(x.elem + y.elem)
end

function -(x::AbsOrdQuoRingElem{S, T, U}, y::AbsOrdQuoRingElem{S, T, U}) where {S, T, U}
  check_parent(x, y)
  Q = parent(x)
  return Q(x.elem - y.elem)
end

function -(x::AbsOrdQuoRingElem{S, T, U}) where {S, T, U}
  Q = parent(x)
  return AbsOrdQuoRingElem{S, T, U}(Q, -x.elem)
end

function *(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  check_parent(x, y)
  Q = parent(x)
  return Q(x.elem * y.elem)
end

function mul!(z::AbsOrdQuoRingElem, x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  z.elem = mul!(z.elem, x.elem, y.elem)
  z.isreduced = false
  return _easy_mod(z)
end

function add!(z::AbsOrdQuoRingElem, x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  z.elem = add!(z.elem, x.elem, y.elem)
  z.isreduced = false
  return _easy_mod(z)
end

addeq!(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem) = add!(x, x, y)

function sub!(z::AbsOrdQuoRingElem, x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  z.elem = sub!(z.elem, x.elem, y.elem)
  z.isreduced = false
  return _easy_mod(z)
end

function *(x::T, y::AbsOrdQuoRingElem) where T <: IntegerUnion
  Q = parent(y)
  return Q(x*y.elem)
end

*(x::AbsOrdQuoRingElem, y::T) where T <: IntegerUnion = y*x

function ^(a::AbsOrdQuoRingElem, f::ZZRingElem)
  if fits(Int, f)
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

#^(a::AbsSimpleNumFieldOrderQuoRingElem, f::Integer) = a^ZZRingElem(f)
function ^(a::AbsSimpleNumFieldOrderQuoRingElem, b::Int)
  if b < 0
    a = inv(a)
    b = -b
  end
  Q = parent(a)
  O = base_ring(Q)
  if !is_defining_polynomial_nice(nf(O)) || !contains_equation_order(O)
    return pow1(a, b)
  end
  m = minimum(Q.ideal, copy = false)
  x = _powermod(a.elem.elem_in_nf, b, m)
  return Q(O(x))
end

function ^(a::AbsOrdQuoRingElem, b::Int)
  return pow1(a, b)
end

function pow1(a::AbsOrdQuoRingElem, b::Int)
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

function iszero(x::AbsOrdQuoRingElem)
  if iszero(x.elem)
    return true
  end
  simplify!(x)
  return iszero(x.elem)
end

function isone(x::AbsOrdQuoRingElem)
  if isone(x.elem)
    return true
  end
  return x == _one(parent(x))
end

function _one(Q::AbsOrdQuoRing)
  return Q.one::elem_type(Q)
end

function one(Q::AbsOrdQuoRing)
  if isdefined(Q, :one)
    return deepcopy(Q.one::elem_type(Q))#elem_type(Q)(Q, one(base_ring(Q)))
  else
    return elem_type(Q)(Q, one(base_ring(Q)))
  end
end

function zero(Q::AbsOrdQuoRing)
  return elem_type(Q)(Q, base_ring(Q)(0))
end

function zero!(x::AbsOrdQuoRingElem)
  zero!(x.elem)
  x.isreduced = true
  return x
end

################################################################################
#
#  Equality
#
################################################################################

function ==(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  parent(x) !== parent(y) && return false
  simplify!(x)
  simplify!(y)
  return x.elem == y.elem
end

################################################################################
#
#  Exact division
#
################################################################################

function divexact(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem; check::Bool = true)
  b, z = is_divisible(x, y)
  @assert b
  return z
end

function is_divisible2(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
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

  fl, sol = can_solve_with_solution(V, rhs, side = :right)
  if !fl
    return fl, zero(R)
  end
  z = R(O(ZZRingElem[sol[i, 1] for i = 1:degree(O)]))
  @hassert :AbsOrdQuoRing 1 z*y == x
  return true, z
end

divides(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem) = is_divisible(x, y)

function is_divisible(x::AbsOrdQuoRingElem, y::AbsOrdQuoRingElem)
  check_parent(x, y)

  if iszero(y)
    if iszero(x)
      return true, zero(parent(x))
    else
      return false, x
    end
  end

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
  if typeof(base_ring(parent(x))) <: AbsSimpleNumFieldOrder
    A = representation_matrix_mod(y.elem, minimum(R.ideal))
  else
    A = representation_matrix(y.elem, :left)#, minimum(R.ideal))
  end
  B = parent(x).basis_matrix

  V[1, 1] = 1

  a = coordinates(x.elem, copy = false)

  for i in 1:d
    # this makes a copy
    V[1, 1 + i] = a[i]
  end

  _copy_matrix_into_matrix(V, 2, 2, A)   # this really is a copy
  _copy_matrix_into_matrix(V, 2 + d, 2, B) # this really is a copy

  for i in 1:d
    V[1 + i, d + 1 + i] = 1
  end

  hnf_modular_eldiv!(V, minimum(R.ideal))

  for i in 2:(d + 1)
    if !iszero(V[1, i])
  #if !iszero(sub(V, 1:1, 2:(d + 1)))
      ccall((:fmpz_mat_zero, libflint), Nothing, (Ref{ZZMatrix}, ), V)
      return false, zero(parent(x))
    end
  end

  z = R(-base_ring(R)(ZZRingElem[ V[1, i] for i in (d + 2):(2*d + 1)])) # V[1, i] is always a copy

  ccall((:fmpz_mat_zero, libflint), Nothing, (Ref{ZZMatrix}, ), V)
  @hassert :AbsOrdQuoRing 1 z*y == x
  return true, z
end

################################################################################
#
#  Strong exact division
#
################################################################################

function _divexact_strong(x::AbsSimpleNumFieldOrderQuoRingElem, y::AbsSimpleNumFieldOrderQuoRingElem)
  n = euclid(x)
  m = euclid(y)
  @hassert :AbsOrdQuoRing 1 mod(n, m) == 0
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

  @hassert :AbsOrdQuoRing 1 q*y == x
  @hassert :AbsOrdQuoRing 1 euclid(q) *euclid(y) == euclid(x)

  return q
end

################################################################################
#
#  Inverse element
#
################################################################################

function is_invertible(x::AbsOrdQuoRingElem)
  return is_divisible(one(parent(x)), x)
end

function inv(x::AbsOrdQuoRingElem)
  t, y = is_invertible(x)
  @assert t "Element is not invertible"
  return y
end

################################################################################
#
#  Unit
#
################################################################################

is_unit(x::AbsOrdQuoRingElem) = is_invertible(x)[1]

################################################################################
#
#  Euclidean function
#
################################################################################

function euclid(x::AbsSimpleNumFieldOrderQuoRingElem)
  if iszero(x)
    return ZZRingElem(-1)
  end

  U = parent(x).tmp_euc

  d = degree(base_ring(parent(x)))

  _copy_matrix_into_matrix(U, 1, 1, representation_matrix(x.elem))
  _copy_matrix_into_matrix(U, d + 1, 1, parent(x).basis_matrix)

  hnf_modular_eldiv!(U, minimum(parent(x).ideal, copy = false))

  z = ZZRingElem(1)

  for i in 1:degree(base_ring(parent(x)))
    mul!(z, z, U[i, i])
  end

  @hassert :AbsOrdQuoRing 1 z == norm(ideal(parent(x.elem), x.elem) + parent(x).ideal)

  return z
end

################################################################################
#
#  Division with remainder
#
################################################################################

function Base.divrem(x::AbsSimpleNumFieldOrderQuoRingElem, y::AbsSimpleNumFieldOrderQuoRingElem)
  b, q = is_divisible(x, y)
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
      @hassert :AbsOrdQuoRing 1 euclid(r) < e
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

Random.gentype(::Type{AbsSimpleNumFieldOrderQuoRing}) = elem_type(AbsSimpleNumFieldOrderQuoRing)

function rand(rng::AbstractRNG, Qsp::Random.SamplerTrivial{AbsSimpleNumFieldOrderQuoRing})
  Q = Qsp[]
  A = basis_matrix(Q)
  B = basis(base_ring(Q))
  z = rand(rng, ZZRingElem(1):A[1,1]) * B[1]

  for i in 2:nrows(A)
    z = z + rand(rng, ZZRingElem(1):A[i, i]) * B[i]
  end

  return Q(z)
end

################################################################################
#
#  Annihilator
#
################################################################################

function annihilator(x::AbsSimpleNumFieldOrderQuoRingElem)
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

  m = kernel(U, side = :left)
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

function gcd(x::AbsSimpleNumFieldOrderQuoRingElem, y::AbsSimpleNumFieldOrderQuoRingElem)
  Q = parent(x)
  O = base_ring(Q)

  if iszero(x)
    if iszero(y)
      return zero(Q)
    else
      return y
    end
  elseif iszero(y)
    return x
  end

  if isone(x) || isone(y)
    return one(Q)
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

function AbstractAlgebra.gcdxx(x::AbsSimpleNumFieldOrderQuoRingElem, y::AbsSimpleNumFieldOrderQuoRingElem)
  Q = parent(x)
  O = base_ring(Q)

  d = degree(O)

  if iszero(x)
    return deepcopy(y), Q(0), Q(1), Q(-1), Q(0)
  elseif iszero(y)
    return deepcopy(x), Q(1), Q(0), Q(0), Q(1)
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

  V = parent(x).tmp_gcdxx

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

  hnf_modular_eldiv!(V, minimum(Q.ideal, copy = false))

  u = Q(-O([ V[1,i] for i in (d + 2):(2*d + 1)]))
  v = Q(-O([ V[1,i] for i in (2*d + 2):(3*d + 1)]))

  @hassert :AbsOrdQuoRing 1 Q(O(1)) == u*e - (v*(-f))

  ccall((:fmpz_mat_zero, libflint), Nothing, (Ref{ZZMatrix}, ), V)

  return g, u, v, -f, e
end

function (M::Generic.MatSpace{AbsSimpleNumFieldOrderQuoRingElem})(x::Generic.MatSpaceElem{AbsSimpleNumFieldOrderElem})
  z = map(base_ring(M), x.entries)::Matrix{AbsSimpleNumFieldOrderQuoRingElem}
  return M(z)::Generic.MatSpaceElem{AbsSimpleNumFieldOrderQuoRingElem}
end

################################################################################
#
#  Compute the probability
#
################################################################################

# Just for debugging purposes
# This governs the runtime of the probabilistic algorithms.
function probability(O::AbsSimpleNumFieldOrderQuoRing)
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

@doc raw"""
    group_structure(Q::AbsSimpleNumFieldOrderQuoRing) -> FinGenAbGroup

Returns an abelian group with the structure of $(Q,+)$.
"""
function group_structure(Q::AbsSimpleNumFieldOrderQuoRing)
  i = ideal(Q)
  fac = factor(i)
  structure = Vector{ZZRingElem}()
  for (p,vp) in fac
    pnum = minimum(p)
    e = valuation(pnum,p)
    f = factor(norm(p))[pnum]
    q, r = divrem(vp+e-1,e)
    structure_pvp = [repeat([pnum^q],inner=[Int((r+1)*f)]) ; repeat([pnum^(q-1)],inner=[Int((e-r-1)*f)])]
    append!(structure,structure_pvp)
  end
  G = abelian_group(structure)
  S, Smap = snf(G)
  return S
end
