################################################################################
#
#  NfMaxOrd/ResidueRing.jl : Quotients of maximal orders of number fields
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

export NfMaxOrdQuoRing, NfMaxOrdQuoRingElem, quo, *, -, ==, deepcopy, divrem,
       gcd, inv, parent, show, divexact, isone, iszero, howell_form,
       strong_echelon_form, triangularize, det

################################################################################
#
#  Field access
#
################################################################################

elem_type(::Type{NfMaxOrdQuoRing}) = NfMaxOrdQuoRingElem

elem_type(::NfMaxOrdQuoRing) = NfMaxOrdQuoRingElem

base_ring(Q::NfMaxOrdQuoRing) = Q.base_ring

ideal(Q::NfMaxOrdQuoRing) = Q.ideal

basis_mat(Q::NfMaxOrdQuoRing) = Q.basis_mat

parent(x::NfMaxOrdQuoRingElem) = x.parent

parent_type(::Type{NfMaxOrdQuoRingElem}) = NfMaxOrdQuoRing

################################################################################
#
#  Functions to allow polynomial and polynomial ring constructions
#
################################################################################

needs_parentheses(::NfMaxOrdQuoRingElem) = true

is_negative(::NfMaxOrdQuoRingElem) = false

# This is dangerous
parent_type(::Type{NfOrdElem}) = NfMaxOrd

Base.promote_rule{S <: Integer}(::Type{NfMaxOrdQuoRingElem},
                                ::Type{S}) = NfMaxOrdQuoRingElem

################################################################################
#
#  Copying
#
################################################################################

deepcopy(x::NfMaxOrdQuoRingElem) = NfMaxOrdQuoRingElem(parent(x), x.elem)

################################################################################
#
#  I/O
#
################################################################################

function show(io::IO, Q::NfMaxOrdQuoRing)
  print(io, "Quotient of $(Q.base_ring)")
end

function show(io::IO, x::NfMaxOrdQuoRingElem)
  print(io, "$(x.elem)")
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function call(O::NfMaxOrdQuoRing, x::NfOrdElem)
  parent(x) != base_ring(O) && error("Cannot coerce element into the quotient ring")
  return NfMaxOrdQuoRingElem(O, x)
end

function call(Q::NfMaxOrdQuoRing, x::Integer)
  return Q(base_ring(Q)(x))
end

function call(Q::NfMaxOrdQuoRing, x::fmpz)
  return Q(base_ring(Q)(x))
end

################################################################################
#
#  Quotient function
#
################################################################################

function quo(O::NfMaxOrd, I::NfMaxOrdIdl)
  # We should check that I is not zero
  Q = NfMaxOrdQuoRing(O, I)
  f = NfMaxOrdQuoMap(O, Q)
  return Q, f
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem + y.elem)
end

function -(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem - y.elem)
end

function -(x::NfMaxOrdQuoRingElem)
  return parent(x)(-x.elem)
end

function *(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem * y.elem)
end

function *(x::Integer, y::NfMaxOrdQuoRingElem)
  return parent(x)(x * y.elem)
end

*(x::NfMaxOrdQuoRingElem, y::Integer) = y*x

function *(x::fmpz, y::NfMaxOrdQuoRingElem)
  return parent(x)(x * y.elem)
end

*(x::NfMaxOrdQuoRingElem, y::fmpz) = y*x

################################################################################
#
#  Special elements
#
################################################################################

iszero(x::NfMaxOrdQuoRingElem) = iszero(x.elem)

is_zero(x::NfMaxOrdQuoRingElem) = iszero(x)

isone(x::NfMaxOrdQuoRingElem) = isone(x.elem)

function one(Q::NfMaxOrdQuoRing)
  return Q(one(Q.base_ring))
end

function zero(Q::NfMaxOrdQuoRing)
  return Q(zero(Q.base_ring))
end

################################################################################
#
#  Equality
#
################################################################################

==(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem) = x.elem == y.elem

################################################################################
#
#  Exact division
#
################################################################################

function divexact(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")

  if iszero(x)
    return zero(parent(x))
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
  V = parent(x).tmp_div
  A = representation_mat(y.elem)
  B = basis_mat(parent(x))

  V[1, 1] = 1

  a = elem_in_basis(x.elem)

  for i in 1:d
    V[1, 1 + i] = a[i]
  end

  _copy_matrix_into_matrix(V, 2, 2, A)
  _copy_matrix_into_matrix(V, 2+d, 2, B)

  for i in 1:d
    V[1 + i, d + 1 + i] = 1
  end

  U = hnf_modular_eldiv(V, minimum(parent(x).ideal))
  #v = submat(U, 1:1, (d + 2):(2*d + 1))
  @assert iszero(submat(U, 1:1, 2:(d + 1)))
  
  z = R(-base_ring(R)(fmpz[ U[1, i] for i in (d + 2):(2*d + 1)]))

  ccall((:fmpz_mat_zero, :libflint), Void, (Ptr{fmpz_mat}, ), &V)

  #@assert z*y == x
  return z
end

################################################################################
#
#  Strong exact division
#
################################################################################

function _divexact_strong(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  n = euclid(x)
  m = euclid(y)
  #@assert mod(n, m) == 0
  target = divexact(n, m)

  q0 = divexact(x, y)

  if euclid(q0) == target
    return q0
  else
    i = annihilator(y)

    q = q0 + rand(parent(x))*i

    while euclid(q) != target 
      q = q0 + rand(parent(x))*i
    end
  end

  #@assert q*y == x
  #@assert euclid(q) *euclid(y) == euclid(x)

  return q
end

################################################################################
#
#  Inverse element
#
################################################################################

function inv(x::NfMaxOrdQuoRingElem)
  return divexact(one(parent(x)), x)
end

################################################################################
#
#  Euclidean function
#
################################################################################

function euclid(x::NfMaxOrdQuoRingElem)
  if is_zero(x)
    return fmpz(-1)
  end

  U = vcat(representation_mat(x.elem), basis_mat(parent(x)))

  U = hnf_modular_eldiv(U, minimum(parent(x).ideal))

  z = fmpz(1)

  for i in 1:degree(base_ring(parent(x)))
    mul!(z, z, U[i, i])
  end
  return z
end

################################################################################
#
#  Division with remainder
#
################################################################################

function divrem(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  q = rand(parent(x))
  r = x - q*y
  e = euclid(y)
  while euclid(r) >= e
    q = rand(parent(x))
    r = x - q*y
  end
  return q, r
end

################################################################################
#
#  Random elements
#
################################################################################

function rand(Q::NfMaxOrdQuoRing)
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

function annihilator(x::NfMaxOrdQuoRingElem)
  I = parent(x).ideal
  O = base_ring(parent(x))
  f = NfMaxOrdQuoMap(O, parent(x))
  M_I = basis_mat(I)
  M_x = representation_mat(x.elem)
  U = vcat(M_x, M_I)
  m = _kernel(U)
  #@assert rows(m) == degree(O)
  #@assert cols(m) == 2*degree(O)
  I = ideal(O, _hnf_modular_eldiv(submat(m, 1:degree(O), 1:degree(O)),
                                  minimum(I), :lowerleft))
  return f(I)
end

################################################################################
#
#  GCD
#
################################################################################

function gcd(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  Q = parent(x)
  O = base_ring(Q)

  I = ideal(O, x.elem) + ideal(O, y.elem)

  f = NfMaxOrdQuoMap(O, parent(x))

  return f(I)
end

################################################################################
#
#  Extended extended GCD
#
################################################################################

function xxgcd(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  Q = parent(x)
  O = base_ring(Q)

  d = degree(O)

  if is_zero(x)
    return deepcopy(y), Q(O(0)), Q(O(1)), Q(O(-1)), Q(O(0))
  elseif is_zero(y)
    return deepcopy(x), Q(O(1)), Q(O(0)), Q(O(0)), Q(O(-1))
  end

  g = gcd(x, y)

  e = _divexact_strong(x, g)
  f = _divexact_strong(y, g)

  #@assert euclid(gcd(e, f)) == 1

  M_e = representation_mat(e.elem)
  M_f = representation_mat(f.elem)

  M_I = basis_mat(Q)

  # let us build
  # ( 1  Q(1) 0  0 )
  # ( 0  M_e  I  0 )
  # ( 0  M_f  0  I )
  # ( 0  M_I  0  0 )

  a = elem_in_basis(Q(O(1)).elem)

  V = parent(x).tmp_ann

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

  #@assert g == u*x + v*y
  #@assert Q(O(1)) == u*e - (v*(-f))

  ccall((:fmpz_mat_zero, :libflint), Void, (Ptr{fmpz_mat}, ), &V)

  return g, u, v, -f, e
end

################################################################################
#
#  Triangularization
#
################################################################################

function _pivot(A, start_row, col)
  if !is_zero(A[start_row, col])
    return 1;
  end

  for j in start_row + 1:rows(A)
    if !is_zero(A[j, col])
      swap_rows!(A, j, start_row)
      return -1
    end
  end

  return 0
end

function strong_echelon_form(A::Mat{NfMaxOrdQuoRingElem})
  B = deepcopy(A)

  if rows(B) < cols(B)
    B = vcat(B, MatrixSpace(base_ring(B), cols(B) - rows(B), cols(B))())
  end

  strong_echelon_form!(B)
  return B
end

function triangularize!(A::Mat{NfMaxOrdQuoRingElem})
  n = rows(A)
  m = cols(A)

  row = 1
  col = 1
  while row <= rows(A) && col <= cols(A)
    if _pivot(A, row, col) == 0
      col = col + 1
      continue
    end
    for i in (row + 1):rows(A)
      g,s,t,u,v = xxgcd(A[row, col], A[i, col])

      for k in col:m
        t1 = s*A[row, k] + t*A[i, k]
        t2 = u*A[row, k] + v*A[i, k]
        A[row, k] = t1
        A[i, k] = t2
      end
    end
    row = row + 1;
    col = col + 1;
  end
end

function triangularize(A::Mat{NfMaxOrdQuoRingElem})
  B = deepcopy(A)
  triangularize!(B)
  return B
end

################################################################################
#
#  Strong echelon form
#
################################################################################

function strong_echelon_form!(A::Mat{NfMaxOrdQuoRingElem})
  #A = deepcopy(B)
  n = rows(A)
  m = cols(A)

  @assert n >= m

  triangularize!(A)

  T = MatrixSpace(base_ring(A), 1, cols(A))()

  # We do not normalize!
  for j in 1:m
    if !is_zero(A[j,j]) != 0
      # This is the reduction
      for i in 1:j-1
        q, r = divrem(A[i, j], A[j, j])
        for l in i:m
          A[i, l] = A[i, l] - q*A[j, l]
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
      g,s,t,u,v = xxgcd(A[i, i], T[1, i])

      for k in i:m
        t1 = s*A[i, k] + t*T[1, k]
        t2 = u*A[i, k] + v*T[1, k]
        A[i, k] = t1
        T[1, k] = t2
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

function howell_form!(A::Mat{NfMaxOrdQuoRingElem})
  @assert rows(A) >= cols(A)

  k = rows(A)

  strong_echelon_form!(A)

  for i in 1:rows(A)
    if is_zero_row(A, i)
      k = k - 1

      for j in (i + 1):rows(A)
        if !is_zero_row(A, j)
          swap_rows!(A, i, j)
          j = rows(A)
          k = k + 1
        end
      end
    end
  end
  return k
end

function howell_form(A::Mat{NfMaxOrdQuoRingElem})
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

function det(M::Mat{NfMaxOrdQuoRingElem})
  rows(M) != cols(M) && error("Matrix must be square matrix")
  N = triangularize(M)
  z = one(base_ring(M))
  for i in 1:rows(N)
    z = z * N[i, i]
  end
  return z
end

################################################################################
#
#  Functions for matrix spaces
#
################################################################################

function call(M::MatrixSpace{NfMaxOrdQuoRingElem}, x::Mat{NfOrdElem})
  base_ring(base_ring(M)) != base_ring(parent(x)) &&
      error("Base rings do not coincide")
  return M(map(base_ring(M), x.entries))
end

################################################################################
#
#  Hensel Lifting
#
################################################################################

## Hensel lifting of roots
# This will fail for too large input
# Need to incorporate the explicit lifting bounds
function _root_hensel(f::Poly{NfOrdElem})
  O = base_ring(f)

  # First we find a prime ideal such that f is squarefree modulo P 
  # (The discriminant of f has only finitely many divisors).

  p = 3

  fder = derivative(f)

  found_prime = false

  # Dummy variable
  Q = NfMaxOrdIdl(O)
  pi_F = NfMaxOrdToFqNmodMor()
  lin_factor = Array{fq_nmod_poly, 1}()

  while !found_prime
    p = next_prime(p)

    if is_index_divisor(O, p) || isramified(O, p)
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

      for i in keys(fac)
        if degree(i) == 1
          push!(lin_factor, i)
        end
      end
      
      Q = P[1]
      found_prime = true
      break
    end
  end

  fmodQ = pi_F(f)


  for j in 1:length(lin_factor)

    zero_mod_Q = - coeff(lin_factor[j], 0)
    
    # The following should be a uniformizing element
    Q_pi = Q.gen_two

    @assert fmodQ(zero_mod_Q) == 0

    # This is the first step

    R, pi_R = quo(O, Q^2)

    t1 = divexact(pi_R(f(pi_F\zero_mod_Q)), pi_R(Q_pi))
    t2 = -inv(pi_R(fder(pi_F\zero_mod_Q)))
    new_a = pi_R\(pi_R(pi_F\zero_mod_Q) + t1*t2*pi_R(Q_pi))
    #return pi_R(f)

    old_a = new_a

    RR, pi_RR = R, pi_R

    I = Q^2

    reconstructed_new = old_a
    reconstructed_old = reconstructed_new

    stabilized = -1

    for i in 2:20
      if reconstructed_new == reconstructed_old
        stabilized = stabilized + 1
      else
        stabilized = 0
      end

      if stabilized >= 3
        if f(reconstructed_new) == 0
          return reconstructed_new
        else
          stabilized = 0
        end
      end

      reconstructed_old = reconstructed_new
      old_a = new_a
      R, pi_R = RR, pi_RR
      I = I * Q

      # From Q^i -> Q^(i+1)

      RR, pi_RR = quo(O, I)
      t1 = divexact(pi_RR(f(old_a)), pi_RR(Q_pi)^(i))
      t2 = pi_RR(pi_F\(-inv(pi_F(fder(old_a)))))
      new_a = pi_RR\(pi_RR(old_a) + t1*t2*pi_RR((Q_pi))^(i))

      # Try to reconstruct:

      B = basis_mat(I)
      L = lll(B)

      rhs = MatrixSpace(ZZ, degree(O), 1)(elem_in_basis(new_a)'')
      lhs = transpose(L)

      X, d = solve(lhs, rhs)

      zz = [ fmpq(BigInt(X[i, 1])//BigInt(d) - round(BigInt(X[i, 1])//BigInt(d))) for i in 1:degree(O)]

      cden = den(zz[1])

      for i in 2:degree(O)
        cden = lcm(cden, den(zz[i]))
      end

      zz_num = [ num(cden*zz[i]) for i in 1:degree(O) ]

      v = MatrixSpace(FlintZZ, 1, degree(O))(zz_num')

      w = v*L

      # There is no slower function

      reconstructed_new = O(fmpz[ divexact(w[1, i], cden) for i in 1:degree(O) ])

      @assert iszero(pi_RR(f(new_a)))
    end
  end
end

