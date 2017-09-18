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

function *(x::Integer, y::NfOrdQuoRingElem)
  return parent(y)(x * y.elem)
end

*(x::NfOrdQuoRingElem, y::Integer) = y*x

function *(x::fmpz, y::NfOrdQuoRingElem)
  return parent(x)(x * y.elem)
end

*(x::NfOrdQuoRingElem, y::fmpz) = y*x

function ^(a::NfOrdQuoRingElem, f::fmpz)
  f==0 && return one(parent(a))
  f==1 && return a
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

^(a::NfOrdQuoRingElem, f::Integer) = a^fmpz(f)


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

  a = elem_in_basis(x.elem)

  for i in 1:d
    V[1, 1 + i] = a[i]
  end

  _copy_matrix_into_matrix(V, 2, 2, A)   # this really is a copy
  _copy_matrix_into_matrix(V, 2+d, 2, B) # this really is a copy

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

  a = elem_in_basis(Q(O(1)).elem)

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
    B = vcat(B, MatrixSpace(base_ring(B), cols(B) - rows(B), cols(B))())
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

  T = MatrixSpace(base_ring(A), 1, cols(A))()

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
    B = vcat(B, MatrixSpace(base_ring(B), cols(B) - rows(B), cols(B))())
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

## Hensel lifting of roots
##todo: redo for equation order using the kronnecker basis (co-different)
##      to avoid denominators
##    : use double iteration to avoid division
#     : use exponent chain to not overshoot (too much) in lifting
#     : common case is f == K.pol. In this case we known a sharp T2-bound
#     : for torsion polynomials, embedd torsion units faithully and 
#     : lift only one root of maximal order
function _roots_hensel(f::Generic.Poly{NfOrdElem}, max_roots::Int = degree(f))
  # f must be squarefree
  # I should check that
  O = base_ring(f)
  n = degree(O)
  deg = degree(f)

  # First we find a prime ideal such that f is squarefree modulo P 
  # (The discriminant of f has only finitely many divisors).

  p = 3

  fder = derivative(f)

  found_prime = false

  # Dummy variable
  Q = NfOrdIdl(O)
  pi_F = NfOrdToFqNmodMor()
  lin_factor = Array{fq_nmod_poly, 1}()

  while !found_prime
    p = next_prime(p)

    if isindex_divisor(O, p) || isramified(O, p)
      continue
    end

    lP = prime_decomposition(O, p)

    for P in lP
      F, pi_F = ResidueField(O, P[1])

      fmodP = pi_F(f)

      if !issquarefree(fmodP)
        continue
      end

      fac = factor(fmodP)

      for (i, l) in fac
        if degree(i) == 1
          push!(lin_factor, i)
        end
      end
      
      Q = P[1]
      found_prime = true
      break
    end
  end

  #println("prime $p $(Q.gen_two)")

  fmodQ = pi_F(f)

  # compute the lifting exponent a la Friedrich-Fieker

  R = ArbField(64)
  z = R(0)
  (c1, c2) = norm_change_const(O)
  #so   |x|_mink  <= c_1 |x|_coeff
  #and  |x|_coeff <= c_2 |x|_mink
  # hopefully
  (r1, r2) = signature(O) 

  bound_root = [ R(0) for i in 1:(r1 + r2) ]

  CC = AcbField(64)
  CCt, t = PolynomialRing(CC, "t")
  conjugates_of_coeffs = [ conjugates_arb(coeff(f, i), -1) for i in 0:degree(f) ]

  for i in 1:r1
    g = CCt([ conjugates_of_coeffs[j + 1][i] for j in 0:degree(f) ])
    bound_root[i] = roots_upper_bound(g)
  end

  for i in 1:r2
    g = CCt([ conjugates_of_coeffs[j + 1][r1 + i] for j in 0:degree(f) ])
    bound_root[r1 + i] = roots_upper_bound(g)
  end

  bd = R(0)

  for i in 1:r1
    bd += bound_root[i]^2
  end

  for i=1:r2
    bd += 2*bound_root[i+r1]^2
  end

  boundt2 = max(bd, R(1))

  boundk = R(n)*log(R(c1)*R(c2)*boundt2*exp((R(n*(n-1))//4 + 2)*log(R(2))))//(2*Q.splitting_type[2]*log(R(p)))

  ss = abs_upper_bound(boundk, fmpz)

  roots = NfOrdElem[]

  s = Int(ss)

  #println(length(lin_factor))
  #println("lifting bound: ", s)

  #println("aiming for $max_roots roots")
  for j in 1:length(lin_factor)
  #  println("have $(length(roots)) found, want $max_roots")
    if length(roots) == max_roots
      break
    end

    zero_mod_Q = - coeff(lin_factor[j], 0)

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

    cden = den(zz[1])

    for l in 2:degree(O)
      cden = lcm(cden, den(zz[l]))
    end

    zz_num = [ num(cden*zz[l]) for l in 1:degree(O) ]

    v = MatrixSpace(FlintZZ, 1, degree(O))(zz_num)

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
          #push!(roots, reconstructed_new)
          break
        else
          stabilized = 0
        end
      end

      if i == s
        if iszero(subst(f, reconstructed_new))
          push!(roots, reconstructed_new)
        end
        break
      end

      reconstructed_old = reconstructed_new
      old_a = new_a
      R, pi_R = RR, pi_RR
      I = I^2

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

      cden = den(zz[1])

      for l in 2:degree(O)
        cden = lcm(cden, den(zz[l]))
      end

      zz_num = [ num(cden*zz[l]) for l in 1:degree(O) ]

      v = MatrixSpace(FlintZZ, 1, degree(O))(zz_num)

      w = v*L

      # There is no slower function

      reconstructed_new = O(fmpz[ divexact(w[1, l], cden) for l in 1:degree(O) ])

      #println(i + 1, " ", reconstructed_new)

      i = i + 1
    end
    if f(reconstructed_new) == 0
      push!(roots, reconstructed_new)
    end
  end
  return roots
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
