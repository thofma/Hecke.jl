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

elem_type(::Type{NfOrdQuoRing}) = NfOrdQuoRingElem

elem_type(::NfOrdQuoRing) = NfOrdQuoRingElem

base_ring(Q::NfOrdQuoRing) = Q.base_ring

ideal(Q::NfOrdQuoRing) = Q.ideal

basis_mat(Q::NfOrdQuoRing) = Q.basis_mat

parent(x::NfOrdQuoRingElem) = x.parent

parent_type(::Type{NfOrdQuoRingElem}) = NfOrdQuoRing

################################################################################
#
#  Hashing
#
################################################################################

hash(x::NfOrdQuoRingElem, h::UInt) = hash(x.elem, h)

################################################################################
#
#  Functions to allow polynomial and polynomial ring constructions
#
################################################################################

needs_parentheses(::NfOrdQuoRingElem) = true

isnegative(::NfOrdQuoRingElem) = false

Nemo.promote_rule{S <: Integer}(::Type{NfOrdQuoRingElem},
                                ::Type{S}) = NfOrdQuoRingElem

Nemo.promote_rule(::Type{NfOrdQuoRingElem}, ::Type{fmpz}) = NfOrdQuoRingElem

################################################################################
#
#  Copying
#
################################################################################

Base.deepcopy_internal(x::NfOrdQuoRingElem, dict::ObjectIdDict) =
        NfOrdQuoRingElem(parent(x), Base.deepcopy_internal(x.elem, dict))

#copy(x::NfOrdQuoRingElem) = deepcopy(x)

################################################################################
#
#  I/O
#
################################################################################

function show(io::IO, Q::NfOrdQuoRing)
  print(io, "Quotient of $(Q.base_ring)")
end

function show(io::IO, x::NfOrdQuoRingElem)
  print(io, "$(x.elem)")
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (O::NfOrdQuoRing)(x::NfOrdElem)
  parent(x) != base_ring(O) && error("Cannot coerce element into the quotient ring")
  return NfOrdQuoRingElem(O, x)
end

function (Q::NfOrdQuoRing)(x::Integer)
  return Q(base_ring(Q)(x))
end

function (Q::NfOrdQuoRing)(x::fmpz)
  return Q(base_ring(Q)(x))
end

################################################################################
#
#  Quotient function
#  
# (and standart helpers)
#
################################################################################
doc"""
    quo(O::NfOrd, I::NfOrdIdl) -> NfOrdQuoRing, Map
> The quotient ring $O/I$ as a ring together with the section $M: O/I \to O$.
> The pointwise inverse of $M$ is the canonical projection $O\to O/I$.
"""
function quo(O::NfOrd, I::NfOrdIdl)
  # We should check that I is not zero
  Q = NfOrdQuoRing(O, I)
  f = NfOrdQuoMap(O, Q)
  return Q, f
end

doc"""
    ResidueRing(O::NfOrd, I::NfOrdIdl) -> NfOrdQuoRing
> The quotient ring $O$ modulo $I$ as a new ring.
"""
Nemo.ResidueRing(O::NfOrd, I::NfOrdIdl) = NfOrdQuoRing(O, I)

doc"""
    lift(O::NfOrd, a::NfOrdQuoRingElem) -> NfOrdElem
> Returns a lift of $a$ back to $O$.
"""
function lift(O::NfOrd, a::NfOrdQuoRingElem)
  f = NfOrdQuoMap(O, parent(a))
  return preimage(f, a)
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem + y.elem)
end

function -(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem - y.elem)
end

function -(x::NfOrdQuoRingElem)
  return parent(x)(-x.elem)
end

function *(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem * y.elem)
end

function mul!(z::NfOrdQuoRingElem, x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  mul!(z.elem, x.elem, y.elem)
  mod!(z.elem, parent(z))
  return z
end

function *(x::Integer, y::NfOrdQuoRingElem)
  return parent(y)(x * y.elem)
end

*(x::NfOrdQuoRingElem, y::Integer) = y*x

function *(x::fmpz, y::NfOrdQuoRingElem)
  return parent(x)(x * y.elem)
end

*(x::NfOrdQuoRingElem, y::fmpz) = y*x

function ^(a::NfOrdQuoRingElem, f::fmpz)
  if nbits(f) < 64
    return a^Int(f)
  end
  f==0 && return one(parent(a))
  f==1 && return deepcopy(a)
  if f<0
    f=-f
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

function ^(a::NfOrdQuoRingElem, b::Int)
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

iszero(x::NfOrdQuoRingElem) = iszero(x.elem)

isone(x::NfOrdQuoRingElem) = isone(x.elem)

function one(Q::NfOrdQuoRing)
  return Q(one(Q.base_ring))
end

function zero(Q::NfOrdQuoRing)
  return Q(zero(Q.base_ring))
end

################################################################################
#
#  Equality
#
################################################################################

==(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem) = x.elem == y.elem

################################################################################
#
#  Exact division
#
################################################################################

function divexact(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  b, z = isdivisible(x, y)
  @assert b
  return z
end

function isdivisible(x::NfOrdQuoRingElem, y::NfOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")

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
  A = representation_mat(y.elem)
  B = basis_mat(parent(x))

  V[1, 1] = 1

  a = elem_in_basis(x.elem, Val{false})

  for i in 1:d
    V[1, 1 + i] = a[i]
  end

  _copy_matrix_into_matrix(V, 2, 2, A)   # this really is a copy
  _copy_matrix_into_matrix(V, 2 + d, 2, B) # this really is a copy

  for i in 1:d
    V[1 + i, d + 1 + i] = 1
  end

  hnf_modular_eldiv!(V, minimum(parent(x).ideal))

  if !iszero(submat(V, 1:1, 2:(d + 1)))
    ccall((:fmpz_mat_zero, :libflint), Void, (Ptr{fmpz_mat}, ), &V)
    return false, zero(parent(x))
  end
  
  z = R(-base_ring(R)(fmpz[ deepcopy(V[1, i]) for i in (d + 2):(2*d + 1)]))

  ccall((:fmpz_mat_zero, :libflint), Void, (Ptr{fmpz_mat}, ), &V)

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

function inv(x::NfOrdQuoRingElem)
  return divexact(one(parent(x)), x)
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

  _copy_matrix_into_matrix(U, 1, 1, representation_mat(x.elem))
  _copy_matrix_into_matrix(U, d + 1, 1, parent(x).basis_mat)

  hnf_modular_eldiv!(U, parent(x).ideal.minimum)

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
  q = rand(parent(x))
  r = x - q*y
  e = euclid(y)

  # This should be only one case and don't do the try/catch crap
  # Write a proper _is_divisible function

  if e == 1
    q = x*inv(y)
    r = x - q*y
    @hassert :NfOrdQuoRing 1 iszero(x - q*y)
    @hassert :NfOrdQuoRing 1 euclid(r) < e
    return q, r
  end

  try q = divexact(x, y)
    r = x - q*y
    @hassert :NfOrdQuoRing 1 iszero(x - q*y)
    @hassert :NfOrdQuoRing 1 euclid(r) < e
    return q, r
  catch
  end

  cnt = 0
  while euclid(r) >= e
    cnt += 1
    q = rand(parent(x))
    r = x - q*y
    if cnt > 1000
      error("Something odd in divrem for $x $y $(parent(x))")
    end
  end

  @hassert :NfOrdQuoRing 1 euclid(r) < e

  return q, r
end

################################################################################
#
#  Random elements
#
################################################################################

function rand(Q::NfOrdQuoRing)
  A = basis_mat(Q)
  B = basis(base_ring(Q))
  z = rand(fmpz(1):A[1,1]) * B[1]

  for i in 2:rows(A)
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
   _copy_matrix_into_matrix(U, 1, 1, representation_mat(x.elem))
   _copy_matrix_into_matrix(U, d + 1, 1, I.basis_mat)

  m = _kernel(U)
  I = ideal(O, _hnf_modular_eldiv(submat(m, 1:degree(O), 1:degree(O)),
                                  minimum(I), :lowerleft))
  z = f(I)
  @assert iszero(z*x)
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

  M_e = representation_mat(e.elem)
  M_f = representation_mat(f.elem)

  M_I = basis_mat(Q)

  # let us build
  # ( 1  Q(1) 0  0 )
  # ( 0  M_e  I  0 )
  # ( 0  M_f  0  I )
  # ( 0  M_I  0  0 )

  a = elem_in_basis(Q(O(1)).elem, Val{false})

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

  U = V

  U = hnf_modular_eldiv(U, minimum(Q.ideal))::fmpz_mat

  u = Q(-O([ U[1,i] for i in (d + 2):(2*d + 1)]))
  v = Q(-O([ U[1,i] for i in (2*d + 2):(3*d + 1)]))

  @hassert :NfOrdQuoRing 1 Q(O(1)) == u*e - (v*(-f))

  ccall((:fmpz_mat_zero, :libflint), Void, (Ptr{fmpz_mat}, ), &V)

  return g, u, v, -f, e
end

################################################################################
#
#  Triangularization
#
################################################################################

function _pivot(A, start_row, col)
  if !iszero(A[start_row, col])
    return 1;
  end

  for j in start_row + 1:rows(A)
    if !iszero(A[j, col])
      swap_rows!(A, j, start_row)
      return -1
    end
  end

  return 0
end

function _strong_echelon_form(A::Generic.Mat{NfOrdQuoRingElem})
  B = deepcopy(A)

  if rows(B) < cols(B)
    B = vcat(B, zero_matrix(base_ring(B), cols(B) - rows(B), cols(B)))
  end

  strong_echelon_form!(B)
  return B
end

function strong_echelon_form(A::Generic.Mat{NfOrdQuoRingElem}, shape::Symbol = :upperright)
  if shape == :lowerleft
    h = _strong_echelon_form(_swapcols(A))
    _swapcols!(h)
    _swaprows!(h)
    return h
  elseif shape == :upperright
    return _strong_echelon_form(A)
  else
    error("Not yet implemented")
  end
end

function triangularize!(A::Generic.Mat{NfOrdQuoRingElem})
  n = rows(A)
  m = cols(A)
  d = one(base_ring(A))

  t_isdiv = 0.0
  t_xxgcd = 0.0
  t_arith = 0.0

  row = 1
  col = 1
  tic()
  while row <= rows(A) && col <= cols(A)
    #println("doing row $row")
    t = _pivot(A, row, col)
    if t == 0
      col = col + 1
      continue
    end
    d = d*t
    for i in (row + 1):rows(A)
      if iszero(A[i, col])
        continue
      end

      t_isdiv += @elapsed b, q = isdivisible(A[i, col], A[row, col])

      if b
        for k in col:m
          t_arith += @elapsed A[i, k] = A[i, k] - q*A[row, k]
        end
        @hassert :NfOrdQuoRing 1 A[i, col] == zero(base_ring(A))
      else
        t_xxgcd += @elapsed g,s,t,u,v = xxgcd(A[row, col], A[i, col])
        @hassert :NfOrdQuoRing 1 isone(s*v - t*u)

        for k in col:m
          t_arith += @elapsed t1 = s*A[row, k] + t*A[i, k]
          t_arith += @elapsed t2 = u*A[row, k] + v*A[i, k]
          A[row, k] = t1
          A[i, k] = t2
        end
      end
    end
    row = row + 1;
    col = col + 1;
  end
  #println("  === Time triangularization")
  #println("    isdivisbible: $t_isdiv")
  #println("    xxgcd       : $t_xxgcd")
  #println("    arith       : $t_arith")
  #println("    total time  : $(toc())")
  return d
end

function triangularize(A::Generic.Mat{NfOrdQuoRingElem})
  #println("copying ...")
  B = deepcopy(A)
  #println("done")
  triangularize!(B)
  return B
end

################################################################################
#
#  Strong echelon form
#
################################################################################

function strong_echelon_form!(A::Generic.Mat{NfOrdQuoRingElem})
  #A = deepcopy(B)
  n = rows(A)
  m = cols(A)

  @assert n >= m

  #print("triangularizing ... ")
  triangularize!(A)

  T = zero_matrix(base_ring(A), 1, cols(A))

  # We do not normalize!
  for j in 1:m
    if !iszero(A[j,j]) != 0
      # This is the reduction
      for i in 1:j-1
        if iszero(A[i, j])
          continue
        else
          q, r = divrem(A[i, j], A[j, j])
          for l in i:m
            A[i, l] = A[i, l] - q*A[j, l]
          end
        end
      end

      a = annihilator(A[j, j])

      for k in 1:m
        T[1, k] = a*A[j, k]
      end
    else
      for k in 1:m
        T[1, k] = A[j, k]
      end
    end


    for i in j+1:m 
      
      if iszero(T[1, i])
        continue
      end

      b, q = isdivisible(T[1, i], A[i, i])

      if b
        for k in i:m
          T[1, k] = T[1, k] - q*A[i, k]
        end
        @hassert :NfOrdQuoRing 1 T[1, i] == zero(base_ring(A))
      else
        g,s,t,u,v = xxgcd(A[i, i], T[1, i])

        for k in i:m
          t1 = s*A[i, k] + t*T[1, k]
          t2 = u*A[i, k] + v*T[1, k]
          A[i, k] = t1
          T[1, k] = t2
        end
      end
    end
  end
  return A
end

################################################################################
#
#  Howell form
#
################################################################################

function howell_form!(A::Generic.Mat{NfOrdQuoRingElem})
  @assert rows(A) >= cols(A)

  k = rows(A)

  strong_echelon_form!(A)

  for i in 1:rows(A)
    if iszero_row(A, i)
      k = k - 1

      for j in (i + 1):rows(A)
        if !iszero_row(A, j)
          swap_rows!(A, i, j)
          j = rows(A)
          k = k + 1
        end
      end
    end
  end
  return k
end

function howell_form(A::Generic.Mat{NfOrdQuoRingElem})
  B = deepcopy(A)

  if rows(B) < cols(B)
    B = vcat(B, zero_matrix(base_ring(B), cols(B) - rows(B), cols(B)))
  end

  howell_form!(B)

  return B
end

################################################################################
#
#  Determinant
#
################################################################################

function det(M::Generic.Mat{NfOrdQuoRingElem})
  rows(M) != cols(M) && error("Matrix must be square matrix")
  N = deepcopy(M)
  d = triangularize!(N)
  z = one(base_ring(M))
  for i in 1:rows(N)
    z = z * N[i, i]
  end
  return z*d
  q, r = divrem(z, d)
  @hassert :NfOrdQuoRing 1 iszero(r)
  return divexact(z, d)
end

################################################################################
#
#  Functions for matrix spaces
#
################################################################################

#function call(M::Generic.MatSpace{NfOrdQuoRingElem}, x::Generic.Mat{NfOrdElem})
#  base_ring(base_ring(M)) != base_ring(parent(x)) &&
#      error("Base rings do not coincide")
#  z = M()
#  R = base_ring(M)
#  for i in 1:rows(x)
#    for j in 1:cols(x)
#      z[i, j] = R(x[i, j])
#    end
#  end
#  return z
#end

function (M::Generic.MatSpace{NfOrdQuoRingElem})(x::Generic.Mat{NfOrdElem})
  z = map(base_ring(M), x.entries)::Array{NfOrdQuoRingElem, 2}
  return M(z)::Generic.Mat{NfOrdQuoRingElem}
end
################################################################################
#
#  Hensel Lifting
#
################################################################################
function lift(R::NmodPolyRing, a::fq_nmod)
  f = R()
  for i=0:degree(parent(a))-1
    setcoeff!(f, i, _get_coeff_raw(a, i))
  end
  return f
end

function (Zx::FmpzPolyRing)(a::nf_elem) 
  b = Zx()
  @assert denominator(a) == 1
  for i=0:a.elem_length
    setcoeff!(b, i, numerator(coeff(a, i)))
  end
  return b
end

#missing:
#  assertion on the lifting
#  filtering of the roots (maybe we don't want all?)
#  find all/ one/ few roots
#  break down in various modules:
#  - find powers of ideal
#  - find LLL/HNF basis
#  - lifting?
#  use ResRing(Poly) instead of doing % pgg?
#  an open variant where k is increased until we have a root?

function _hensel(f::Generic.Poly{nf_elem}, p::Int, k::Int; max_roots::Int = degree(f))
  #assumes f squarefree
  #assumes constant_coefficient(f) != 0
  ZX, X = FlintZZ["X"]
  Rp = ResidueRing(FlintZZ, p)
  Rpt, t = Rp["t"]
  K = base_ring(f)

  gp = Rpt(K.pol)
  #to avoid embarrasment...
  @assert !iszero(discriminant(gp))

  #find the prime ideal - as I don't want to use orders, this is 
  #fun (computing a max order just for this is wasteful)
  #fun fact: if g = prod g_i mod p^k, then P_i^k = <p^k, g_i>
  #so instead of powering, and simplify and such, lets write it down
  lp = factor(gp).fac
  if length(lp) > 1
    g1 = lift(ZX, first(keys(lp)))
    gg = hensel_lift(ZX(K.pol), g1, fmpz(p), k)
  else
    gg = ZX(K.pol)
  end
  # now for all i<= k, <p^i, K(gg)+p^i> is a normal presentation for
  #                                     the prime ideal power.
  #later we'll get the HNF matrix for selected powers as well

  #set up the mod p data:
  #need FiniteField as I need to factor (roots)
  S = FqNmodFiniteField(first(keys(lp)), :z)
  ST, T = S["T"]
  fp = ST([S(Rpt(coeff(f, i))) for i=0:degree(f)])
  rt = roots(fp)
  #we're going to lift the roots - and for efficiency 1/f'(rt) as well:
  fps = derivative(fp)
  irt = [inv(fps(x)) for x= rt]

  # this is in the finite field, but now I need it in the res. ring.
  # in ZX for ease of transport.
  RT = [lift(ZX, lift(Rpt, x)) for x = rt]
  IRT = [lift(ZX, lift(Rpt, x)) for x = irt]

  #the den: ala Kronnecker:
  den = ZX(derivative(K.pol)(gen(K)))
  iden = inv(derivative(K.pol)(gen(K)))

  #for the result, to check for stabilising

  res = nf_elem[K(0) for x = RT]
  rs = nf_elem[]

  #we'll be working in (Z/p^k)[t]/gg

  #an "optimal" lifting chain:
  pr = [k]
  while k>1
    k = div(k+1, 2)
    push!(pr, k)
  end
  pr = reverse(pr)

  #lets start:

  for i=2:length(pr)
    pp = fmpz(p)^pr[i]
    Q = ResidueRing(FlintZZ, pp)
    Qt, t = Q["t"]

    #possibly this should be done with max precision and then adjusted down
    #the poly mod P^??
    fp = [Qt(ZX(coeff(f, k))) for k=0:degree(f)]

    #we need to evaluate fp and fp' at the roots (later)
    #given that we evaluate "by hand" we don't need polynomials

    pgg = Qt(gg) #we'll do the reductions by hand - possibly not optimal

    #the lattice for reco:
    n = degree(K)
    M = MatrixSpace(FlintZZ, n, n)()
    for j=1:degree(pgg)
      M[j,j] = pp
    end
    pt = t^(degree(pgg)-1)
    for j=degree(pgg)+1:n
      pt = (pt*t) % pgg
      M[j,j] = 1
      for k=0:degree(pt)
        M[j, k+1] = -lift(coeff(pt, k))
      end
    end
    #this is (or should be) the HNF basis for P^??
    M = lll(M)
    Mi, d = pseudo_inv(M)

    for j=1:length(RT)
      if RT[j] == 0
        continue
      end
      #to eval fp and the derivative, we pre-compute the powers of the
      #evaluation point - to save on large products...

      pow = [Qt(1), Qt(RT[j])]
      while length(pow) <= degree(f)+1
        push!(pow, pow[2]*pow[end] % pgg)
      end

      eval_f = sum(pow[k] * fp[k] for k=1:length(fp)) % pgg
      eval_fs = sum(pow[k-1] *(k-1)*fp[k] for k=2:length(fp)) % pgg

      #double lift:
      #IRT = invmod(fp'(rt), p^k)
      # using x -> x(2-xy) to compute the inverse of y
      IRT[j] = lift(ZX, Qt(IRT[j])*(Qt(2-IRT[j]*eval_fs) % pgg) %pgg)
      #RT = rt mod p^k normal Newton
      # using x -> x-fp(x)//fp'(x) = x-fp(x) * IRT
      RT[j] = lift(ZX, Qt(pow[2] - eval_f*Qt(IRT[j])) % pgg)

      #before the reconstruction, we need to scale by den
      cf = lift(ZX, Qt(RT[j]*den) % pgg)
      ve = matrix(FlintZZ, 1, n, [coeff(cf, k) for k=0:n-1])
      _ve = ve*Mi
      mu = matrix(FlintZZ, 1, n,  [ round(_ve[1, k]//d) for k=1:n])
      ve = ve - mu*M
      z = ZX()
      for k=1:n
        setcoeff!(z, k-1, ve[1, k])
      end
      zz = K(z)*iden
      if res[j] == zz || i == length(pr)
        if f(zz) == 0
          push!(rs, zz)
          if length(rs) >= max_roots
            return rs
          end
          RT[j] = ZX(0)
        end
      else
        res[j] = zz
      end
    end
  end  
  return rs
end

function ispower(a::Nemo.fq_nmod, m::Int)
  s = size(parent(a))
  if gcd(s-1, m) == 1
    return true, a^invmod(m, s-1)
  end
  St, t = parent(a)["t"]
  f = t^m-a
  rt = roots(f)
  if length(rt) > 0
    return true, rt[1]
  else
    return false, a
  end
end

function has_primitive_root_1(K::Nemo.FqNmodFiniteField, m::Int)
  @assert m>0
  if m == 1
    return K(1)
  end
  if size(K) % m != 1
    return false, K(1)
  end
  if m == 2
    return K(-1)
  end
  fm = factor(m)
  while true
    g = rand(K)
    if iszero(g)
      continue
    end
    if any(x -> isone(g^div(m, x)), keys(fm))
      continue
    end
    return true, g^div(size(K)-1, m)
  end  
end

#as above, but for f = x^m-a, so m-th root of a

function _hensel(a::nf_elem, m::Int, p::Int, k::Int; max_roots::Int = m)
  #@assert denominator(a) == 1                           
  #well, actually, denominator(a, maximal_order)==1 would be sufficient, but 
  #hard to test...
  ZX, X = FlintZZ["X"]
  Rp = ResidueRing(FlintZZ, p)
  Rpt, t = Rp["t"]
  K = parent(a)

  gp = Rpt(K.pol)
  #to avoid embarrasment...
  @assert !iszero(discriminant(gp))

  #find the prime ideal - as I don't want to use orders, this is 
  #fun (computing a max order just for this is wasteful)
  #fun fact: if g = prod g_i mod p^k, then P_i^k = <p^k, g_i>
  #so instead of powering, and simplify and such, lets write it down
  lp = factor(gp).fac
  if length(lp) > 1
    g1 = lift(ZX, first(keys(lp)))
    gg = hensel_lift(ZX(K.pol), g1, fmpz(p), k)
  else
    gg = ZX(K.pol)
  end
  
  # now for all i<= k, <p^i, K(gg)+p^i> is a normal presentation for
  #                                     the prime ideal power.
  #later we'll get the HNF matrix for selected powers as well

  #set up the mod p data:
  #need FiniteField as I need to factor (roots)
  S = FqNmodFiniteField(first(keys(lp)), :z)
  ST, T = S["T"]
  fp = T^m - S(Rpt(a))
  rt = roots(fp)
  #OK, we're doing s.th. different
#  b = a^(m-1) #this dominates everything!!!, maybe it should be done in the 
#              #residue ring as well.
  rt = [inv(x^(m-1)) for x = rt]

  # this is in the finite field, but now I need it in the res. ring.
  # in ZX for ease of transport.
  RT = [lift(ZX, lift(Rpt, x)) for x = rt]

  #the den: ala Kronnecker:
  den = ZX(derivative(K.pol)(gen(K)))
  iden = inv(derivative(K.pol)(gen(K)))

  #for the result, to check for stabilising

  res = nf_elem[K(0) for x = RT]
  rs = nf_elem[]

  #we'll be working in (Z/p^k)[t]/gg

  #an "optimal" lifting chain:
  pr = [k]
  while k>1
    k = div(k+1, 2)
    push!(pr, k)
  end
  pr = reverse(pr)

  #lets start:

  for i=2:length(pr)
    pp = fmpz(p)^pr[i]
    Q = ResidueRing(FlintZZ, pp)
    Qt, t = Q["t"]

    #possibly this should be done with max precision and then adjusted down
    #the poly mod P^??

    pgg = Qt(gg) #we'll do the reductions by hand - possibly not optimal

    #the lattice for reco:
    n = degree(K)
    M = MatrixSpace(FlintZZ, n, n)()
    for j=1:degree(pgg)
      M[j,j] = pp
    end
    pt = t^(degree(pgg)-1)
    for j=degree(pgg)+1:n
      pt = (pt*t) % pgg
      M[j,j] = 1
      for k=0:degree(pt)
        M[j, k+1] = -lift(coeff(pt, k))
      end
    end
    #this is (or should be) the HNF basis for P^??
    M = lll(M)
    Mi, d = pseudo_inv(M)

    ap = Qt(ZX(a))
    bp = powmod(ap, m-1, pgg)
    minv = invmod(fmpz(m), pp)

    for j=1:length(RT)
      if RT[j] == 0
        continue
      end

      RTjp = Qt(RT[j])
      RT[j] = lift(ZX, (RTjp*(1+minv) - bp*minv* powmod(RTjp, m+1, pgg)) % pgg)

      #before the reconstruction, we need to scale by den and by a
      cf = lift(ZX, (Qt(RT[j]*den) % pgg)*ap % pgg)
      ve = matrix(FlintZZ, 1, n, [coeff(cf, k) for k=0:n-1])
      _ve = ve*Mi
      mu = matrix(FlintZZ, 1, n,  [ round(_ve[1, k]//d) for k=1:n])
      ve = ve - mu*M
      z = ZX()
      for k=1:n
        setcoeff!(z, k-1, ve[1, k])
      end
      zz = K(z)*iden
      if res[j] == zz || i == length(pr)
        if zz^m == a
          push!(rs, zz)
          if length(rs) >= max_roots
            return rs
          end
          RT[j] = ZX(0)
        end
      else
        res[j] = zz
      end
    end
  end  
  return rs
end

## Hensel lifting of roots
##todo: redo for equation order using the kronnecker basis (co-different)
##      to avoid denominators
##    : use double iteration to avoid division
#     : use exponent chain to not overshoot (too much) in lifting
#     : common case is f == K.pol. In this case we known a sharp T2-bound
#     : for torsion polynomials, embed torsion units faithully and 
#     : lift only one root of maximal order
#mostly done for nf_elem, see next function
#missing: different (better) handling for x^n-a
# possibly based on https://scicomp.stackexchange.com/questions/18846/newton-iteration-for-cube-root-without-division
#
# g = x^-n -a^(n-1), and r = root(g), then r = a^(-(n-1)/n), hence
#                                         ar = a^(-(n-1)/n + 1) = a^(1/n)
# Here, the Newton-iteration is easy: (b = a^(n-1))
# g = x^-n - b, => g' = -nx^(-n-1)
#Newton: r -> r-g(r)/g'(r) = r - (r^(-n) -b)/(-n r^(-n-1))
#                          = r - r/(-n) - b/n r^(n+1)
#                          = r(1+1/n) - b/n r^(n+1)
# no division! and no double iteration
# however, for reconstruction: we don't want r (which is non-integral)
# but ar which is...

function _roots_hensel(f::Generic.Poly{NfOrdElem}, max_roots::Int = degree(f))
  # f must be squarefree
  # I should check that
  O = base_ring(f)
  n = degree(O)
  deg = degree(f)

  # First we find a prime ideal such that f is squarefree modulo P 
  # (The discriminant of f has only finitely many divisors).

  p = degree(f)+1

  fder = derivative(f)

  found_prime = false

  # Dummy variable
  Q = NfOrdIdl(O)
  pi_F = NfOrdToFqNmodMor()
  rt = Array{fq_nmod, 1}()
  di = discriminant(O)

  while !found_prime
    p = next_prime(p)

    if di % p == 0
      continue
    end

    lP = prime_decomposition(O, p)

    for P in lP
      F, pi_F = ResidueField(O, P[1])

      fmodP = pi_F(f)

      if !issquarefree(fmodP)
        continue
      end

      rt = roots(fmodP)
      Q = P[1]
      found_prime = true
      break
    end
  end

  #println("prime $p $(Q.gen_two)")

  fmodQ = pi_F(f)

  # compute the lifting exponent a la Friedrich-Fieker

  R = ArbField(64)
  (r1, r2) = signature(O) 

  bound_root = [ R(0) for i in 1:(r1 + r2) ]

  CC = AcbField(64)
  CCt, t = PolynomialRing(CC, "t")
  conjugates_of_coeffs = [ conjugates_arb(coeff(f, i), 32) for i in 0:degree(f) ]

  for i in 1:r1
    g = CCt([ conjugates_of_coeffs[j + 1][i] for j in 0:degree(f) ])
    bound_root[i] = roots_upper_bound(g)
  end

  for i in 1:r2
    g = CCt([ conjugates_of_coeffs[j + 1][r1 + i] for j in 0:degree(f) ])
    bound_root[r1 + i] = roots_upper_bound(g)
  end

  ss = _lifting_expo(p, Q.splitting_type[2], order(Q), bound_root)
  s = Int(ss)


  #println(length(lin_factor))
  #println("lifting bound: ", s)

  rts = NfOrdElem[]
  #println("aiming for $max_roots roots")
  for j in 1:length(rt)
  #  println("have $(length(roots)) found, want $max_roots")
    if length(rts) >= max_roots
      break
    end

    zero_mod_Q = rt[j]

    #println(zero_mod_Q)

    #println(0, " ", pi_F\(zero_mod_Q))
    
    # The following should be a uniformizing element
    Q_pi = Q.gen_two

    @hassert :NfOrdQuoRing 1 fmodQ(zero_mod_Q) == 0

    # This is the first step

    I = Q^2

    R, pi_R = quo(O, I)

    t1 = divexact(pi_R(subst(f, pi_F\zero_mod_Q)), pi_R(Q_pi))
    t2 = -inv(pi_R(subst(fder,pi_F\zero_mod_Q)))
    new_a = pi_R\(pi_R(pi_F\zero_mod_Q) + t1*t2*pi_R(Q_pi))
    #return pi_R(f)

    #println(1, " ", new_a)

    old_a = new_a

    RR, pi_RR = R, pi_R

    # reconstruction
    B = basis_mat(I)
    L = lll(B)

    rhs = MatrixSpace(FlintZZ, degree(O), 1)(elem_in_basis(new_a)'')
    lhs = transpose(L)

    X, d = solve_rational(lhs, rhs)

    zz = [ fmpq(BigInt(X[l, 1])//BigInt(d) - round(BigInt(X[l, 1])//BigInt(d))) for l in 1:degree(O)]

    cden = denominator(zz[1])

    for l in 2:degree(O)
      cden = lcm(cden, denominator(zz[l]))
    end

    zz_num = [ numerator(cden*zz[l]) for l in 1:degree(O) ]

    v = matrix(FlintZZ, 1, degree(O), zz_num)

    w = v*L

    # There is no slower function

    reconstructed_new = O(fmpz[ divexact(w[1, l], cden) for l in 1:degree(O) ])
    # end reconstruction

    reconstructed_old = reconstructed_new

    stabilized = 0 

    i = 1
    while 2^i < s
      if reconstructed_new == reconstructed_old
        stabilized = stabilized + 1
      else
        stabilized = 0
      end

      if stabilized >= 2
        if subst(f, reconstructed_new) == 0
          #push!(rts, reconstructed_new)
          break
        else
          stabilized = 0
        end
      end

      if i == s
        if iszero(subst(f, reconstructed_new))
          push!(rts, reconstructed_new)
        end
        break
      end

      reconstructed_old = reconstructed_new
      old_a = new_a
      R, pi_R = RR, pi_RR
      I = simplify(I^2)

      # From Q^i -> Q^(i+1)
      # From Q^(2^i) -> Q^(2^i+1)

      RR, pi_RR = quo(O, I)
      #t1 = divexact(pi_RR(subst(f, old_a)), pi_RR(Q_pi)^(2^i))
      #t2 = pi_RR(pi_F\(-inv(pi_F(subst(fder, old_a)))))
      #new_a = pi_RR\(pi_RR(old_a) + t1*t2*pi_RR((Q_pi))^(2^i))
      new_a = old_a - subst(f, old_a) * (pi_R\(divexact(one(R), pi_R(subst(fder, old_a)))))
      new_a = pi_RR\(pi_RR(new_a))
      #println(i + 1, " ", new_a)

      # Try to reconstruct:

      B = basis_mat(I)
      L = lll(B)

      rhs = MatrixSpace(FlintZZ, degree(O), 1)(elem_in_basis(new_a)'')
      lhs = transpose(L)

      X, d = solve_rational(lhs, rhs)

      zz = [ fmpq(BigInt(X[l, 1])//BigInt(d) - round(BigInt(X[l, 1])//BigInt(d))) for l in 1:degree(O)]

      cden = denominator(zz[1])

      for l in 2:degree(O)
        cden = lcm(cden, denominator(zz[l]))
      end

      zz_num = [ numerator(cden*zz[l]) for l in 1:degree(O) ]

      v = matrix(FlintZZ, 1, degree(O), zz_num)

      w = v*L

      # There is no slower function

      reconstructed_new = O(fmpz[ divexact(w[1, l], cden) for l in 1:degree(O) ])

      #println(i + 1, " ", reconstructed_new)

      i = i + 1
    end
    if f(reconstructed_new) == 0
      push!(rts, reconstructed_new)
    end
  end
  return rts
end

function _lifting_expo(p::Int, deg_p::Int, O::NfOrd, bnd::Array{arb, 1})
  # compute the lifting exponent a la Friedrich-Fieker
  #bnd has upper bounds on |x^{(i)}| 1<= i <= r1+r2 as arbs
  #we're using a prime ideal above p of intertia degree deg_p

  (c1, c2) = norm_change_const(O)
  r1, r2 = signature(O)
  R = parent(bnd[1])
  bd = R(0)
  n = degree(O)
  #so   |x|_mink  <= c_1 |x|_coeff
  #and  |x|_coeff <= c_2 |x|_mink

  for i in 1:r1
    bd += bnd[i]^2
  end

  for i=1:r2
    bd += 2*bnd[i+r1]^2
  end

  boundt2 = max(bd, R(1))

  boundk = R(n)*log(R(c1)*R(c2)*boundt2*exp((R(n*(n-1))//4 + 2)*log(R(2))))//(2*deg_p*log(R(p)))

  ss = abs_upper_bound(boundk, fmpz)
  return ss
end

function _roots_hensel(f::Generic.Poly{nf_elem}, max_roots::Int = degree(f))
  # f must be squarefree
  # I should check that
  K = base_ring(f)
  if iszero(constant_coefficient(f))
    rs = [K(0)]
    f = div(f, gen(parent(f)))
  else
    rs = nf_elem[]
  end
  if length(rs) >= max_roots
    return rs
  end
  n = degree(K)
  deg = degree(f)

  # First we find a prime ideal such that f is squarefree modulo P 
  # (The discriminant of f has only finitely many divisors).

  p = degree(f)+1
  deg_p = 1

  while true
    p = next_prime(p)

    Rp = ResidueRing(FlintZZ, p)
    Rpt, t = Rp["t"]
    gp = Rpt(K.pol)
    if iszero(discriminant(gp))
      continue
    end

    lp = factor(gp).fac
    #set up the mod p data:
    #need FiniteField as I need to factor (roots)
    deg_p = degree(first(keys(lp)))
    S = FqNmodFiniteField(first(keys(lp)), :z)
    ST, T = S["T"]
    fp = ST([S(Rpt(coeff(f, i))) for i=0:degree(f)])
    if !issquarefree(fp)
      continue
    end
    rt = roots(fp)
    if length(rt) == 0
      return nf_elem[]
    end
    break
  end

  #println("prime $p ")

  # compute the lifting exponent a la Friedrich-Fieker

  R = ArbField(64)

  (r1, r2) = signature(K) 

  # for Kronnecker:
  gsa = derivative(K.pol)(gen(K))
  gsa_con = conjugates_arb(gsa, 32)

  bound_root = [ R(0) for i in 1:(r1 + r2) ]

  CC = AcbField(64)
  CCt, t = PolynomialRing(CC, "t")
  conjugates_of_coeffs = [ conjugates_arb(coeff(f, i), 32) for i in 0:degree(f) ]

  for i in 1:r1
    g = CCt([ conjugates_of_coeffs[j + 1][i] for j in 0:degree(f) ])
    bound_root[i] = roots_upper_bound(g) * abs(gsa_con[i])
  end

  for i in 1:r2
    g = CCt([ conjugates_of_coeffs[j + 1][r1 + i] for j in 0:degree(f) ])
    bound_root[r1 + i] = roots_upper_bound(g) * abs(gsa_con[r1+i])
  end

  ss = _lifting_expo(p, deg_p, EquationOrder(K), bound_root)

  rts = _hensel(f, p, Int(ss), max_roots = max_roots - length(rs))
  return vcat(rs, rts)
end

function _roots_hensel(a::nf_elem, m::Int, max_roots::Int = m)
  # f must be squarefree
  # I should check that
  K = parent(a)
  n = degree(K)

  # First we find a prime ideal such that f is squarefree modulo P 
  # (The discriminant of f has only finitely many divisors).

  p = m+1
  deg_p = 1

  while true
    p = next_prime(p)

    Rp = ResidueRing(FlintZZ, p)
    Rpt, t = Rp["t"]
    gp = Rpt(K.pol)
    if iszero(discriminant(gp))
      continue
    end

    lp = factor(gp).fac
    #set up the mod p data:
    #need FiniteField as I need to factor (roots)
    deg_p = degree(first(keys(lp)))
    S = FqNmodFiniteField(first(keys(lp)), :z)
    ST, T = S["T"]
    fp = T^m - S(Rpt(a))
    if !issquarefree(fp)
      continue
    end
    rt = roots(fp)
    if length(rt) == 0
      return nf_elem[]
    end
    break
  end

  #println("prime $p ")

  # compute the lifting exponent a la Friedrich-Fieker

  R = ArbField(64)
  (r1, r2) = signature(K) 

  # for Kronnecker:
  gsa = derivative(K.pol)(gen(K))
  gsa_con = conjugates_arb(gsa, 32)
  a_con = conjugates_arb(a, 32)

  bound_root = [ R(0) for i in 1:(r1 + r2) ]

  for i in 1:r1+r2
    bound_root[i] = root(abs(a_con[i]), m) * abs(gsa_con[i])
  end

  ss = _lifting_expo(p, deg_p, EquationOrder(K), bound_root)

  rts = _hensel(a, m, p, Int(ss), max_roots = max_roots)
  return rts
end
#identical to hasroot - which one do we want?
function ispower(a::NfOrdElem, n::Int)
  Ox, x = parent(a)["x"]
  f = x^n - a
  r = _roots_hensel(f, 1)
  
  if length(r) == 0
    return false, parent(a)(0)
  else
    return true, r[1]
  end
end

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

doc"""
***
    group_structure(Q::NfOrdQuoRing) -> GrpAbFinGenSnf

> Returns an abelian group with the structure of (Q,+).
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
