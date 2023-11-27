#=
    Copyright (C) 2008, Martin Albrecht
    Copyright (C) 2008, 2009 William Hart.
    Copyright (C) 2010, Fredrik Johansson

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.

    to julia:
    Copyright (C) 2020, Claus Fieker
=#

module Strassen
using Hecke
using LinearAlgebra, Profile, Base.Intrinsics
import Hecke.AbstractAlgebra, Hecke.Nemo
import Hecke.Nemo: add!, mul!, zero!, sub!, solve_triu!, solve_tril!

const cutoff = 1500

#creates an unimodular n x n matrix where the inverse is much larger
#than the original matrix. Entries are chosen in U
function rand_mat(n::Int, U::AbstractArray=1:10)
  C = zero_matrix(ZZ, n, n)
  for i=1:n-1
    C[i, i+1] = 1
  end
  for i=2:n
    C[n, i] = rand(U)
  end
  C[n,1] = 1
  for i=2:n-1
    C[i,i] = rand(U)
  end
  return C
end

function perturb!(A, n::Int = 100, c::AbstractRange = -10:10)
  for i=1:n 
    x = rand(c)
    while iszero(x)
      x = rand(c)
    end
    if rand(0:1) == 1
      k = rand(1:nrows(A))
      l = rand(1:nrows(A))
      while l == k
        l = rand(1:nrows(A))
      end
      A[k, :] += x*A[l, :]
    else
      k = rand(1:ncols(A))
      l = rand(1:ncols(A))
      while l == k
        l = rand(1:ncols(A))
      end
      A[:, k] += x*A[:, l]
    end
  end
end

function Nemo.mul!(C::AbstractArray, A::AbstractArray, B::AbstractArray, add::Bool = false)
  @assert size(C) == (2,2) && size(A) == (2,2) && size(B) == (2,2)
  C[1,1] = A[1,1] * B[1,1] + A[1,2] * B[2,1]
  C[1,2] = A[1,1] * B[1,2] + A[1,2] * B[2,2]
  C[2,1] = A[2,1] * B[1,1] + A[2,2] * B[2,1]
  C[2,2] = A[2,1] * B[1,2] + A[2,2] * B[2,2]
  return C
  if add
    C .+= A*B
  else
    C .= A*B
  end
end

function mul_strassen!(C::AbstractArray, A::AbstractArray, B::AbstractArray)
  sA = size(A)
  sB = size(B)
  sC = size(C)
  a = sA[1]
  b = sA[2]
  c = sB[2]

  @assert a == sC[1] && b == sB[1] && c == sC[2]

  if (a <= cutoff || b <= cutoff || c <= cutoff)
      Nemo.mul!(C, A, B)
      return
  end

  anr = div(a, 2)
  anc = div(b, 2)
  bnr = anc
  bnc = div(c, 2)

  #nmod_mat_window_init(A11, A, 0, 0, anr, anc);
  #nmod_mat_window_init(A12, A, 0, anc, anr, 2*anc);
  #nmod_mat_window_init(A21, A, anr, 0, 2*anr, anc);
  #nmod_mat_window_init(A22, A, anr, anc, 2*anr, 2*anc);
  A11 = view(A, 1:anr, 1:anc)
  A12 = view(A, 1:anr, anc+1:2*anc)
  A21 = view(A, anr+1:2*anr, 1:anc)
  A22 = view(A, anr+1:2*anr, anc+1:2*anc)

  #nmod_mat_window_init(B11, B, 0, 0, bnr, bnc);
  #nmod_mat_window_init(B12, B, 0, bnc, bnr, 2*bnc);
  #nmod_mat_window_init(B21, B, bnr, 0, 2*bnr, bnc);
  #nmod_mat_window_init(B22, B, bnr, bnc, 2*bnr, 2*bnc);
  B11 = view(B, 1:bnr, 1:bnc)
  B12 = view(B, 1:bnr, bnc+1:2*bnc)
  B21 = view(B, bnr+1:2*bnr, 1:bnc)
  B22 = view(B, bnr+1:2*bnr, bnc+1:2*bnc)

  #nmod_mat_window_init(C11, C, 0, 0, anr, bnc);
  #nmod_mat_window_init(C12, C, 0, bnc, anr, 2*bnc);
  #nmod_mat_window_init(C21, C, anr, 0, 2*anr, bnc);
  #nmod_mat_window_init(C22, C, anr, bnc, 2*anr, 2*bnc);
  C11 = view(C, 1:anr, 1:bnc)
  C12 = view(C, 1:anr, bnc+1:2*bnc)
  C21 = view(C, anr+1:2*anr, 1:bnc)
  C22 = view(C, anr+1:2*anr, bnc+1:2*bnc)

  #nmod_mat_init(X1, anr, FLINT_MAX(bnc, anc), A->mod.n);
  #nmod_mat_init(X2, anc, bnc, A->mod.n);

  #X1->c = anc;

  #=
      See Jean-Guillaume Dumas, Clement Pernet, Wei Zhou; "Memory
      efficient scheduling of Strassen-Winograd's matrix multiplication
      algorithm"; http://arxiv.org/pdf/0707.2347v3 for reference on the
      used operation scheduling.
  =#

  #nmod_mat_sub(X1, A11, A21);
  X1 = A11 .- A21
  #nmod_mat_sub(X2, B22, B12);
  X2 = B22 .- B12
  #nmod_mat_mul(C21, X1, X2);
  mul_strassen!(C21, X1, X2)

  #nmod_mat_add(X1, A21, A22);
  X1 .= A21 .+ A22
  #nmod_mat_sub(X2, B12, B11);
  X2 .= B12 .- B11
  #nmod_mat_mul(C22, X1, X2);
  mul_strassen!(C22, X1, X2)

  #nmod_mat_sub(X1, X1, A11);
  X1 .-= A11
  #nmod_mat_sub(X2, B22, X2);
  X2 .= B22 .- X2
  #nmod_mat_mul(C12, X1, X2);
  mul_strassen!(C12, X1, X2)

  #nmod_mat_sub(X1, A12, X1);
  X1 .= A12 .- X1
  #nmod_mat_mul(C11, X1, B22);
  mul_strassen!(C11, X1, B22)

  #X1->c = bnc;
  #nmod_mat_mul(X1, A11, B11);
  X1 = similar(C11)
  mul_strassen!(X1, A11, B11)

  #nmod_mat_add(C12, X1, C12);
  C12 .+= X1
  #nmod_mat_add(C21, C12, C21);
  C21 .+= C12
  #nmod_mat_add(C12, C12, C22);
  C12 .+= C22
  #nmod_mat_add(C22, C21, C22);
  C22 .+= C21
  #nmod_mat_add(C12, C12, C11);
  C12 .+= C11
  #nmod_mat_sub(X2, X2, B21);
  X2 .-= B21
  #nmod_mat_mul(C11, A22, X2);
  mul_strassen!(C11, A22, X2)

  #nmod_mat_sub(C21, C21, C11);
  C21 .-= C11

  #nmod_mat_mul(C11, A12, B21);
  mul_strassen!(C11, A12, B21)

  #nmod_mat_add(C11, X1, C11);
  C11 .+= X1

  if c > 2*bnc #A by last col of B -> last col of C
    error("missing")
    #=
  {
      nmod_mat_t Bc, Cc;
      nmod_mat_window_init(Bc, B, 0, 2*bnc, b, c);
      nmod_mat_window_init(Cc, C, 0, 2*bnc, a, c);
      nmod_mat_mul(Cc, A, Bc);
      nmod_mat_window_clear(Bc);
      nmod_mat_window_clear(Cc);
  }
    =#
  end

  if a > 2*anr #last row of A by B -> last row of C
    error("missing")
    #=
  {
      nmod_mat_t Ar, Cr;
      nmod_mat_window_init(Ar, A, 2*anr, 0, a, b);
      nmod_mat_window_init(Cr, C, 2*anr, 0, a, c);
      nmod_mat_mul(Cr, Ar, B);
      nmod_mat_window_clear(Ar);
      nmod_mat_window_clear(Cr);
  }
    =#
  end

  if b > 2*anc # last col of A by last row of B -> C
    error("missing")
    #=
  {
      nmod_mat_t Ac, Br, Cb;
      nmod_mat_window_init(Ac, A, 0, 2*anc, 2*anr, b);
      nmod_mat_window_init(Br, B, 2*bnr, 0, b, 2*bnc);
      nmod_mat_window_init(Cb, C, 0, 0, 2*anr, 2*bnc);
      nmod_mat_addmul(Cb, Cb, Ac, Br);
      nmod_mat_window_clear(Ac);
      nmod_mat_window_clear(Br);
      nmod_mat_window_clear(Cb);
  }
    =#
  end
end

function mul_strassen!(A::Generic.Mat, B::Generic.Mat, C::Generic.Mat)
  mul_strassen!(C.entries, A.entries, B.entries)
end

function zero!(A::MatElem{T}) where {T}
  error("not done yet")
end

#function zero!(A::fpMatrix)
#  ccall((:nmod_mat_zero, Nemo.libflint), Cvoid, (Ref{fpMatrix}, ), A)
#end

#function zero!(A::ZZMatrix)
#  ccall((:fmpz_mat_zero, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, ), A)
#end
#
#function sub!(A::ZZMatrix, B::ZZMatrix, C::ZZMatrix)
#  ccall((:fmpz_mat_sub, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZMatrix}), A, B, C)
#end

#function sub!(A::fpMatrix, B::fpMatrix, C::fpMatrix)
#  ccall((:fmpz_mat_sub, Nemo.libflint), Cvoid, (Ref{fpMatrix}, Ref{fpMatrix}, Ref{fpMatrix}), A, B, C)
#end

function mul_strassen(A::MatElem{T}, B::MatElem{T}; cutoff::Int = cutoff) where {T}
  C = zero_matrix(base_ring(A), nrows(A), ncols(B))
  mul_strassen!(C, A, B; cutoff)
  return C
end

function mul_strassen!(C::MatElem{T}, A::MatElem{T}, B::MatElem{T}; cutoff::Int = cutoff) where {T}
  sA = size(A)
  sB = size(B)
  sC = size(C)
  a = sA[1]
  b = sA[2]
  c = sB[2]

  @assert a == sC[1] && b == sB[1] && c == sC[2]

  if (a <= cutoff || b <= cutoff || c <= cutoff)
      Nemo.mul!(C, A, B)
      return
  end

  anr = div(a, 2)
  anc = div(b, 2)
  bnr = anc
  bnc = div(c, 2)

  #nmod_mat_window_init(A11, A, 0, 0, anr, anc);
  #nmod_mat_window_init(A12, A, 0, anc, anr, 2*anc);
  #nmod_mat_window_init(A21, A, anr, 0, 2*anr, anc);
  #nmod_mat_window_init(A22, A, anr, anc, 2*anr, 2*anc);
  A11 = view(A, 1:anr, 1:anc)
  A12 = view(A, 1:anr, anc+1:2*anc)
  A21 = view(A, anr+1:2*anr, 1:anc)
  A22 = view(A, anr+1:2*anr, anc+1:2*anc)

  #nmod_mat_window_init(B11, B, 0, 0, bnr, bnc);
  #nmod_mat_window_init(B12, B, 0, bnc, bnr, 2*bnc);
  #nmod_mat_window_init(B21, B, bnr, 0, 2*bnr, bnc);
  #nmod_mat_window_init(B22, B, bnr, bnc, 2*bnr, 2*bnc);
  B11 = view(B, 1:bnr, 1:bnc)
  B12 = view(B, 1:bnr, bnc+1:2*bnc)
  B21 = view(B, bnr+1:2*bnr, 1:bnc)
  B22 = view(B, bnr+1:2*bnr, bnc+1:2*bnc)

  #nmod_mat_window_init(C11, C, 0, 0, anr, bnc);
  #nmod_mat_window_init(C12, C, 0, bnc, anr, 2*bnc);
  #nmod_mat_window_init(C21, C, anr, 0, 2*anr, bnc);
  #nmod_mat_window_init(C22, C, anr, bnc, 2*anr, 2*bnc);
  C11 = view(C, 1:anr, 1:bnc)
  C12 = view(C, 1:anr, bnc+1:2*bnc)
  C21 = view(C, anr+1:2*anr, 1:bnc)
  C22 = view(C, anr+1:2*anr, bnc+1:2*bnc)

  #nmod_mat_init(X1, anr, FLINT_MAX(bnc, anc), A->mod.n);
  #nmod_mat_init(X2, anc, bnc, A->mod.n);

  #X1->c = anc;

  #=
      See Jean-Guillaume Dumas, Clement Pernet, Wei Zhou; "Memory
      efficient scheduling of Strassen-Winograd's matrix multiplication
      algorithm"; http://arxiv.org/pdf/0707.2347v3 for reference on the
      used operation scheduling.
  =#

  X1 = A11 - A21
  X2 = B22 - B12
  #nmod_mat_mul(C21, X1, X2);
  mul_strassen!(C21, X1, X2; cutoff)

  add!(X1, A21, A22);
  sub!(X2, B12, B11);
  #nmod_mat_mul(C22, X1, X2);
  mul_strassen!(C22, X1, X2; cutoff)

  sub!(X1, X1, A11);
  sub!(X2, B22, X2);
  #nmod_mat_mul(C12, X1, X2);
  mul_strassen!(C12, X1, X2; cutoff)

  sub!(X1, A12, X1);
  #nmod_mat_mul(C11, X1, B22);
  mul_strassen!(C11, X1, B22; cutoff)

  #X1->c = bnc;
  #nmod_mat_mul(X1, A11, B11);
  zero!(X1)
  mul_strassen!(X1, A11, B11; cutoff)

  add!(C12, X1, C12);
  add!(C21, C12, C21);
  add!(C12, C12, C22);
  add!(C22, C21, C22);
  add!(C12, C12, C11);
  sub!(X2, X2, B21);
  #nmod_mat_mul(C11, A22, X2);
  mul_strassen!(C11, A22, X2; cutoff)

  sub!(C21, C21, C11);

  #nmod_mat_mul(C11, A12, B21);
  mul_strassen!(C11, A12, B21; cutoff)

  add!(C11, X1, C11);

  if c > 2*bnc #A by last col of B -> last col of C
      #nmod_mat_window_init(Bc, B, 0, 2*bnc, b, c);
      Bc = view(B, 1:b, 2*bnc+1:c)
      #nmod_mat_window_init(Cc, C, 0, 2*bnc, a, c);
      Cc = view(C, 1:a, 2*bnc+1:c)
      #nmod_mat_mul(Cc, A, Bc);
      Nemo.mul!(Cc, A, Bc)
  end

  if a > 2*anr #last row of A by B -> last row of C
      #nmod_mat_window_init(Ar, A, 2*anr, 0, a, b);
      Ar = view(A, 2*anr+1:a, 1:b)
      #nmod_mat_window_init(Cr, C, 2*anr, 0, a, c);
      Cr = view(C, 2*anr+1:a, 1:c)
      #nmod_mat_mul(Cr, Ar, B);
     Nemo.mul!(Cr, Ar, B)
  end

  if b > 2*anc # last col of A by last row of B -> C
      #nmod_mat_window_init(Ac, A, 0, 2*anc, 2*anr, b);
      Ac = view(A, 1:2*anr, 2*anc:b)
      #nmod_mat_window_init(Br, B, 2*bnr, 0, b, 2*bnc);
      Br = view(B, 2*bnr+1:b, 1:2*bnc)
      #nmod_mat_window_init(Cb, C, 0, 0, 2*anr, 2*bnc);
      Cb = view(C, 1:2*anr, 1:2*bnc)
      #nmod_mat_addmul(Cb, Cb, Ac, Br);
      Nemo.mul!(Cb, Ac, Br, true)
  end
end

function apply!(A::fpMatrix, P::Perm{Int}; offset::Int = 0)
  n = length(P.d)
  t = zeros(Int, n-offset)
  for i=1:n-offset
    t[i] = unsafe_load(reinterpret(Ptr{Int}, A.rows), P.d[i] + offset)
  end
  for i=1:n-offset
    unsafe_store!(reinterpret(Ptr{Int}, A.rows), t[i], i + offset)
  end
end

function apply!(Q::Perm{Int}, P::Perm{Int}; offset::Int = 0)
  n = length(P.d)
  t = zeros(Int, n-offset)
  for i=1:n-offset
    t[i] = Q.d[P.d[i] + offset]
  end
  for i=1:n-offset
    Q.d[i + offset] = t[i]
  end
end

#takes the result of lu! and turns it into a proper lu
function Nemo.lu(P::Perm, U, r::Int)
  m = nrows(U)
  n = ncols(U)
  R = base_ring(U)
  L = similar(U, m, m)

  for i = 1:m
    for j = 1:n
      if i > j
        L[i, j] = U[i, j]
        U[i, j] = R(0)
      elseif i == j
        L[i, j] = R(1)
      elseif j <= m
        L[i, j] = R(0)
      end
    end
  end
  return r, P, L, U
end

function lu!_strassen(P::Perm{Int}, Ai; cutoff::Int = 300)
  m = nrows(A)

  @assert length(P.d) == m
  n = ncols(A)
  if n < cutoff
    return lu!(P, A)
  end
  n1 = div(n, 2)
  for i=1:m
    P.d[i] = i
  end
  P1 = Hecke.AbstractAlgebra.Perm(m)
  A0 = view(A, 1:m, 1:n1)
  r1 = lu!_strassen(P1, A0; cutoff)
  @assert r1 == n1
  if r1 > 0 
    apply!(A, P1)
    apply!(P, P1)
  end

  A00 = view(A, 1:r1, 1:r1)
  A10 = view(A, r1+1:m, 1:r1)
  A01 = view(A, 1:r1, n1+1:n)
  A11 = view(A, r1+1:m, n1+1:n)

  if r1 > 0
    #Note: A00 is a view of A0 thus a view of A
    # A0 is lu!, thus implicitly two triangular matrices giving the
    # lu decomosition. solve_tril! looks ONLY at the lower part of A00
    Nemo.solve_tril!(A01, A00, A01, 1)
    X = A10 * A01
    Nemo.sub!(A11, A11, X)
  end

  P1 = Perm(nrows(A11))
  r2 = lu!_strassen(P1, A11)
  apply!(A, P1, offset = r1)
  apply!(P, P1, offset = r1)

  if (r1 != n1)
    for i=1:m-r1
      for j=1:min(i, r2)
        A[r1+i-1, r1+j-1] = A[r1+i-1, n1+j-1]
        A[r1+i-1, n1+j-1] = 0
      end
    end
  end
  return r1 + r2
end

#
# see https://arxiv.org/pdf/1901.00904.pdf
# p2
#
#  A B  = I       0  * A 0 * I A^-1 B
#  C D   C A^-1   I    0 X   0  I
#
# for X = D - C A^-1 B
#
# inv( I A; 0 I) = I -A; 0 I
#
# TODO:
#    inplace
#    pre-alloced tmp for the recursion
#
function inv_strassen(A)
#  @show size(A)
  if isodd(ncols(A)) || ncols(A) < 400
    return inv(A)
  end
#  @show :strassen, ncols(A)
  @assert nrows(A) == ncols(A)
  @assert iseven(ncols(A))
  n = div(ncols(A), 2)
  A11 = view(A, 1:n, 1:n)
  A12 = view(A, 1:n, n+1:2*n)
  A21 = view(A, n+1:2*n, 1:n)
  A22 = view(A, n+1:2*n, n+1:2*n)

#  I = identity_matrix(base_ring(A), n)
#  Z = zero_matrix(base_ring(A), n, n)


  A11_i = inv_strassen(A11)
  A11_i_A12 = A11_i*A12
  delta = A22-A21*A11_i_A12
  X22 = delta_i = inv_strassen(delta)
  A21_A11_i = A21*A11_i
  X21 = -delta_i*A21_A11_i
  X12 = -A11_i_A12*delta_i
  X11 = A11_i-A11_i_A12*X21

  X = similar(A)
  ccall((:nmod_mat_set, Hecke.libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), view(X, 1:n, 1:n), X11)
  ccall((:nmod_mat_set, Hecke.libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), view(X, 1:n, n+1:n+n), X12)
  ccall((:nmod_mat_set, Hecke.libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), view(X, n+1:n+n, 1:n), X21)
  ccall((:nmod_mat_set, Hecke.libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), view(X, n+1:n+n, n+1:n+n), X22)

  return X

  return [X11 X12; X21 X22]
end

function solve_triu_strassen(T::MatElem, b::MatElem; cutoff::Int = cutoff)
  #b*inv(T), thus solves Tx = b for T upper triangular
  n = ncols(T)
  if n <= 50
    R = solve_triu(T, b)
    return R
  end

  n2 = div(n, 2) + n % 2
  m = nrows(b)
  m2 = div(m, 2) + m % 2

  U = view(b, 1:m2, 1:n2)
  V = view(b, 1:m2, n2+1:n)
  X = view(b, m2+1:m, 1:n2)
  Y = view(b, m2+1:m, n2+1:n)

  A = view(T, 1:n2, 1:n2)
  B = view(T, 1:n2, 1+n2:n)
  C = view(T, 1+n2:n, 1+n2:n)

  S = solve_triu_strassen(A, U; cutoff)
  R = solve_triu_strassen(A, X; cutoff)

  SS = mul_strassen(S, B; cutoff)
  sub!(SS, V, SS)
  SS = solve_triu_strassen(C, SS; cutoff)

  RR = mul_strassen(R, B; cutoff)
  sub!(RR, Y, RR)
  RR = solve_triu_strassen(C, RR; cutoff)

  return [S SS; R RR]
end

function AbstractAlgebra.solve_triu(U::ZZMatrix, b::ZZMatrix)
   n = ncols(U)
   m = nrows(b)
   R = base_ring(U)
   X = zero(b)
   tmp = zero_matrix(ZZ, 1, n)
   t = R()
   s = R()
   for i = 1:m
      tmp_p = Nemo.mat_entry_ptr(tmp, 1, 1)
      X_p = Nemo.mat_entry_ptr(X, i, 1)
      for j = 1:n
         ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ptr{fmpz}, Ptr{fmpz}), tmp_p, X_p)
         X_p += sizeof(ZZRingElem)
         tmp_p += sizeof(ZZRingElem)
      end
      for j = 1:n
         ccall((:fmpz_zero, Nemo.libflint), Cvoid, (Ref{fmpz}, ), s) 

         tmp_p = Nemo.mat_entry_ptr(tmp, 1, 1)
         for k = 1:j-1
            U_p = Nemo.mat_entry_ptr(U, k, j)
            ccall((:fmpz_addmul, Nemo.libflint), Cvoid, (Ref{fmpz}, Ptr{fmpz}, Ptr{fmpz}), s, U_p, tmp_p)
            tmp_p += sizeof(ZZRingElem)
         end
         ccall((:fmpz_sub, Nemo.libflint), Cvoid, 
          (Ref{fmpz}, Ptr{fmpz}, Ref{fmpz}), s, Nemo.mat_entry_ptr(b, i, j), s)
         ccall((:fmpz_divexact, Nemo.libflint), Cvoid, 
          (Ptr{fmpz}, Ref{fmpz}, Ptr{fmpz}), Nemo.mat_entry_ptr(tmp, 1, j), s, Nemo.mat_entry_ptr(U, j, j))
      end
      tmp_p = Nemo.mat_entry_ptr(tmp, 1, 1)
      X_p = Nemo.mat_entry_ptr(X, i, 1)
      for j = 1:n
         ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ptr{fmpz}, Ptr{fmpz}), X_p, tmp_p)
         X_p += sizeof(ZZRingElem)
         tmp_p += sizeof(ZZRingElem)
      end
   end
   return X
end

function Hecke.hadamard_bound2(M::ZZMatrix)
  is_square(M) || error("Matrix must be square")
  H = ZZ(1);
  r = ZZ(0)
  n = nrows(M)
  for i in 1:n
    ccall((:fmpz_set_si, Nemo.libflint), Cvoid, (Ref{ZZRingElem}, Int), r, 0)
    M_ptr = Nemo.mat_entry_ptr(M, i, 1)
    for j in 1:n
      ccall((:fmpz_addmul, Nemo.libflint), Cvoid, (Ref{ZZRingElem}, Ptr{ZZRingElem}, Ptr{ZZRingElem}), r, M_ptr, M_ptr)
      M_ptr += sizeof(ZZRingElem)
    end
    if iszero(r)
      return r
    end
    Nemo.mul!(H, H, r)
  end
  return H
end

function Base.maximum(::typeof(nbits), M::ZZMatrix)
  mx = 0
  n = nrows(M)
  m = ncols(M)
  M_ptr = Nemo.mat_entry_ptr(M, 1, 1)
  for i in 1:n
    for j in 1:m
      if !iszero(unsafe_load(reinterpret(Ptr{Int}, M_ptr)))
        mx = max(mx, ccall((:fmpz_bits, Nemo.libflint), Int, (Ptr{fmpz},), M_ptr))
      end
      M_ptr += sizeof(ZZRingElem)
    end
  end
  return mx
end


# Triangular denominator: for a solution matrix "s", given denominator d and A= d*s.
#  Uses presumably the following function
## [17] gcdx(a::ZZRingElem, b::ZZRingElem)
##     @ Nemo ~/OSCAR/GIT/Nemo.jl/src/flint/fmpz.jl:1293
# NOTE: mod(,) seems to return least-non-negative remainder
function hcol(A::ZZMatrix, d::ZZRingElem)  # why not Vector{ZZRingElem}???
  n = nrows(A)
  w = deepcopy(A)
  g = d
  t = Array(ZZ,n)
  h = zero_matrix(ZZ,n,n)
  s = 1
  v = 1
  for i = 1:n
    k = n-(i-1)
    gg,e,f = gcdx(g,A[k,1])
    t[k] = f
    h[k,k] = g/gg
    g = gg
  end
  for i = 1:n
    if h[i,i] == 1
      continue
    end
    for k = 1:i-1
      h[k,i] = mod(-t[i]*w[k,1], h[i,i])
      w[k,1] = mod(w[k,1]+h[k,i]*w[i,1], d)   
    end
    w[i,1] = h[i,i]*w[i,1]
    d = d/h[i,i]
    divexact!(w, w, h[i,i])
  end
  return h
end

function infinity_norm(A::ZZMatrix)
  return maximum(abs, A)
end

@inline function Nemo.mat_entry_ptr(b::fpMatrix, i::Int, j::Int)
  unsafe_load(reinterpret(Ptr{Ptr{Culong}}, b.rows), i) + (j-1)*sizeof(Culong)
end

function induce_crt!(A::ZZMatrix, p::ZZRingElem, B::fpMatrix, ::Integer; signed::Bool = false)
  #the second modulus is implicit in B: B.n

  ccall((:fmpz_mat_CRT_ui, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZRingElem}, Ref{fpMatrix}, Int), A, A, p, B, signed)
  Nemo.mul!(p, p, B.n)
  return
end

function vector_int(a::fpMatrix)
  b = zeros(Int, nrows(a) * ncols(a))
  vector_int!(b, a)
  return b
end

function vector_int!(a::Vector{Int}, b::fpMatrix)
  ccall(:memcpy, Cvoid, (Ref{Int}, Ptr{Clong}, Int), a, b.entries, nrows(b)*ncols(b) * 8)
end

function _map_entries(k::Nemo.fpField, A::ZZMatrix)
  #turns A into a fpMatrix with julias memory manager,
  #create a "view" where the view_parent is a julia-Uint array with the
  #entries
  # => no finaliser
  # => matrix(entries) can be used as a 1-dim julia array
  #    (for broadcast)
  u = zeros(Int, nrows(A)*ncols(A))
  a = Nemo.fpMatrix()
  a.base_ring = k
  a.entries = reinterpret(Ptr{Cvoid}, pointer(u))
  v = zeros(UInt, nrows(A))
  for i=1:nrows(A)
    v[i] = a.entries + (i-1)*ncols(A)*8
  end
  a.view_parent = (u, v)
  a.rows = reinterpret(Ptr{Cvoid}, pointer(v))
  a.r = nrows(A)
  a.c = ncols(A)
  change_prime(a, UInt(characteristic(k)))
  map_entries!(a, k, A)
  return a
end

@inline myround(a, p, pi) = @fastmath a-p*Base.rint_llvm(a*pi)

function Nemo.mod!(A::AbstractArray{Float64}, p::Int)
  return Nemo.mod!(A, Float64(p), 1.0/Float64(p))
end

function Nemo.mod!(A::AbstractArray{Float64}, pf::Float64, pfi::Float64)
#  pf = Float64(p)
#  pfi = 1/pf
#  A = reshape(A, nrows(A)*ncols(A))
#  A .= (x->myround(x, pf, pfi)).(A) 
#  return
  Ap = pointer(A)
  @fastmath for i= 1:length(A)
    a = Base.Intrinsics.pointerref(Ap, 1, 1)
#    a = unsafe_load(Ap)
    a -= pf*Base.rint_llvm(a*pfi)
#     a = Base.modf(a, pf)
    Base.Intrinsics.pointerset(Ap, a, 1, 1)
#    unsafe_store!(Ap, a)
    Ap += sizeof(Float64)
  end
end

# Input: B vector of matrices as Double64 meant to be mod q[i]
# Output: RE vector of matrices ...                       p[i]

function change_rns!(RE::Vector{Matrix{Float64}}, p::Vector{Int}, q::Vector{Int}, B::Vector{<:AbstractArray{Float64}}, U::Vector{Matrix{Float64}} = []) 
  T = Float64
  bd = Int[]  # mixed radix rep (wrt to q) of (prod(q)-1)/2
  pr = mapreduce(ZZ, *, q)
  pr = div(pr, 2)
  for i = q
    push!(bd, pr % i)
    pr = divexact(pr - bd[end], i)
  end

  qinv = Int[0]
  for i=2:length(B)
    push!(qinv, invmod(Int(mapreduce(ZZ, *, q[1:i-1]) % q[i]), q[i]))
  end
  cp = [x-Int(mapreduce(ZZ, *, q) % x) for x = p]

  if length(U) < 1
    push!(U, copy(B[1]))
  else
    U[1] .= B[1]
  end
  @fastmath for i=2:length(B)
    if length(U) < i
      push!(U, copy(U[i-1]))
    else
      U[i] .= U[i-1]
    end
    for j=i-2:-1:1
      BLAS.scal!((q[j] % T(q[i])), U[i])
      BLAS.axpy!(1.0, U[j], U[i])
      mod!(U[i], q[i])
    end
    BLAS.scal!(T((qinv[i]*(q[i]-1)) % q[i]), U[i])
    BLAS.axpy!(T(qinv[i]), B[i], U[i])
    mod!(U[i], q[i])
  end

  for j = 1:length(p)
    if length(RE) < j
      push!(RE, copy(U[length(B)]))
    else
      RE[j] .= U[length(B)]
    end
    mod!(RE[j], p[j])
    @fastmath for i=length(B)-1:-1:1
      BLAS.scal!(T(q[i] % p[j]), RE[j])
      BLAS.axpy!(1.0, U[i], RE[j])
      mod!(RE[j], p[j])
    end
  end

  for i=1:length(RE[1])
    for j=1:length(B)
      if U[j][i] > bd[j]
        for k=1:length(p)
          RE[k][i] = (RE[k][i] + cp[k]) % p[k]
        end
        break
      elseif U[j][i] < bd[j]
        break
      end
    end
  end
  return RE
end

# Storjohann's unimodular certification
# We use CRT to obtain the modular inverse B0
# The p-adic Hensel-lifting version (below) seems to be faster
function UniCertZ_CRT_rns(A::ZZMatrix)
  n = nrows(A);
  #assume ncols == n
  H = hadamard_bound2(A)
  EntrySize = maximum(nbits, A)
  e = max(16, 2+ceil(Int, 2*log2(n)+EntrySize))
  println("Modulus X has  $e bits");
  
  B0 = Matrix{Float64}[]
  m = ZZ(1); p = 2^21;  # MAGIC NUMBER (initial prime, probably should be about 2^29?)
  Xp = Int[]
  @time while nbits(m) < e
    p = next_prime(p);
    push!(Xp, p)
    ZZmodP = GF(p, cached = false);
    MatModP = map_entries(ZZmodP, A)
    B00 = inv_strassen(MatModP)
    push!(B0, map(Float64, lift(B00)).entries)
    Nemo.mul!(m, m, p)
  end
  println("Got modular inverses");
  #m is the X

  Ap = Matrix{Float64}[]
  m_inv = fpFieldElem[]
  Y = ZZ(1)
  Yp = Int[]
  while nbits(Y) < Int(1+ceil(log2(n)+EntrySize)) 
    p = next_prime(p)
    push!(Yp, p)
    k = GF(p, cached = false)
    push!(Ap, map(Float64, lift(map_entries(k, A))).entries)
    push!(m_inv, inv(k(m)))
    Nemo.mul!(Y, Y, p)
  end

  # Compute max num iters in k
  k = (n-1)*(EntrySize+log2(n)/2) - (2*log2(n) + EntrySize);
  k = k/log2(m);
  k = 2+ceil(Int, log2(k));
  println("Max num iters is k=$(k)");

  t = similar(B0[1])
  RY = Matrix{Float64}[]
  U = Matrix{Float64}[]
  change_rns!(RY, Yp, Xp, B0, U)
  for i = 1:length(Ap)
    x = Ap[i]
    t = RY[i]
    t .= -x*t
    mod!(t, Yp[i])
    for j=1:n
      t[j,j] += 1.0
    end
    BLAS.scal!(Float64(lift(m_inv[i])), t)
    mod!(t, Yp[i])
  end

  if all(iszero, RY)
    return true
  end

  RX = map(similar, B0)
  MY = map(similar, Ap)
  R = similar(B0[1])
  M = similar(B0[1])
  T = similar(M)

  MX = Matrix{Float64}[]

  for i in 0:k-1
    println("UniCertZ: loop: i=$(i)");
    @time change_rns!(RX, Xp, Yp, RY, U)
    @time for t = 1:length(RX)
      BLAS.gemm!('n', 'n', 1.0, RX[t], RX[t], 0.0, M)
      Nemo.mod!(M, Xp[t])
      if length(MX) < t
        push!(MX, B0[t] * M)
      else
        BLAS.gemm!('n', 'n', 1.0, B0[t], M, 0.0, MX[t])
      end
      Nemo.mod!(MX[t], Xp[t])
    end
    @time change_rns!(MY, Yp, Xp, MX, U)
    @time for k=1:length(Ap)
      S = RY[k]
      M = similar(S)
      BLAS.gemm!('n', 'n', 1.0, S, S, 0.0, M)
#      change_rns2!(M, Yp[k], Xp, MX, U)
#      S .= S*S
      BLAS.gemm!('n', 'n', -1.0, Ap[k], MY[k], 1.0, M)
#      S .-= Ap[k] * M
      mod!(M, Yp[k])
      BLAS.scal!(Float64(lift(m_inv[k])), M)
      mod!(M, Yp[k])
      RY[k], M = M, RY[k]
    end

    if all(iszero, RY)
      return true
    end
  end #for
  return false
end


# Storjohann's unimodular certification
# We use CRT to obtain the modular inverse B0
# The p-adic Hensel-lifting version (below) seems to be faster
function UniCertZ_CRT(A::ZZMatrix)
  n = nrows(A);
  #assume ncols == n
  H = hadamard_bound2(A)
  EntrySize = infinity_norm(A)
  e = max(16, Int(2+ceil(2*log2(n)+log2(EntrySize))));
  println("Modulus has  $e bits");
  
  B0 = MatrixSpace(ZZ,n,n)(0); ## will be computed by crt in loop below
  m = ZZ(1); p = 2^29;  # MAGIC NUMBER (initial prime, probably should be about 2^29?)
  @time while (nbits(m) < e)
    p = next_prime(p);
    ZZmodP = GF(p, cached = false);
    MatModP = map_entries(ZZmodP, A)
    B00 = inv_strassen(MatModP)
    induce_crt!(B0,m, B00,p, signed = true);  #  also updates:  m = m*p;
  end
  println("Got modular inverse");

  # Compute max num iters in k
  k = (n-1)*(log2(EntrySize)+log2(n)/2) - (2*log2(n) + log2(EntrySize));
  k = k/log2(m);
  k = 2+Int(ceil(log2(k)));
  println("Max num iters is k=$(k)");

  ZZmodM = residue_ring(ZZ,m);
  B0_modm = map_entries(ZZmodM, B0);
  I = MatrixSpace(ZZ,n,n)(1)
  R = (I-A*B0)/m
  if is_zero(R)
    return true;
  end
  for i in 0:k-1
    println("UniCertZ: loop: i=$(i)");
    @time R_bar = R^2;
    @time M = lift(B0_modm*map_entries(ZZmodM, R_bar));
    Hecke.mod_sym!(M, m)
    @time R = (R_bar - A*M)/m;
    if is_zero(R)
      return true
    end
  end #for
  return false
end

function _det(a::fpMatrix)
  a.r < 10 && return det(a)
  #_det avoids a copy: det is computed destructively
  r = ccall((:_nmod_mat_det, Nemo.libflint), UInt, (Ref{fpMatrix}, ), a)
  return ZZ(r)
end


# Determinant algorithm: U is the range for random RHS matrix (default -100:100)
# Answer is !!! CORRECT UP TO SIGN !!!
function DetS(A::ZZMatrix, U::AbstractArray= -100:100)
  n = ncols(A)
  T = ZZMatrix[]
  AT = A
  d1 = ZZ(1) # will be the det

  p = UInt(next_prime(2^60))
  det_p = ZZ(0)
  prod_p = ZZ(1)
  Ainf = maximum(nbits, A)
  Had = div(nbits(Hecke.hadamard_bound2(A)), 2)+1

  #Dixon cost
  # lifting has (at least) Had/60 many steps (as the numerator will be
  # of maximal size)
  # Each step uses (Ainf+60+n)/60 many modular products
  #                +1 for lifting
  #so that should be the number of quadratic steps
  #
  function dixon_cost(::fmpz)
    ceil(Int, (((Ainf+60+n)/60 + 1) * Had/60)/n)
  end
  #this should estimate the number of modular dets that will cost
  #as much as the next dixon step.
  #if we are close enough to Had, we move to crt.
  function crt_cost(d::fmpz)
    return ceil(Int, (Had-nbits(d))/60)
  end
  function hnf_cost(d::fmpz)
    ceil(Int, nbits(d)/60)
  end
  function uni_cost(d::fmpz)
    ceil(Int, log(n)*(2*n+Ainf)/60)
  end

  f = true
  local Ap::fpMatrix
  small = Ainf+n
  @time while nbits(prod_p) < small + 20
    if f
      f = false
      Ap = map_entries(Nemo.fpField(p, false), A)
    else
      change_prime(Ap, p)
      map_entries!(Ap, Nemo.fpField(p, false), A)
    end
    d = _det(Ap)
    if det_p == 0
      det_p = d
    else
      det_p = crt(det_p, prod_p, d, ZZ(p))
    end
    Nemo.mul!(prod_p, prod_p, p)
    p = next_prime(p)
  end
  det_p = mod_sym(det_p, prod_p)
  det_small = false
  if nbits(prod_p) - nbits(det_p) > 30
    @show "det small", det_p
    det_small = true
  end

  local D::DixonCtx
  f = true
  while !det_small
    b = rand(matrix_space(ZZ,n,1),U); 
    if f
      D = dixon_init(A, b)
      f = false
    end
    @time TS, d = dixon_solve(D, b)
    for i=1:length(T)
      TS = T[i]*TS
    end
    c = content(TS)
    g = gcd(c, d)
    divexact!(TS, TS, g)
    d = divexact(d, g)
    println("DetS: loop: nbits(d)=$(nbits(d))");
    global last_bad = b, T, d
    @assert !isone(d)  #should never happen, the det_p should catch that
    isone(d) && break
    d1 *= d
    @show  (Had - nbits(d1) - nbits(prod_p))/60
    if Had - nbits(d1) < nbits(prod_p)
      @show "at H-bound",  (Had - nbits(d1) - nbits(prod_p))/60
      return d1
    end
    if (Had - nbits(d1) - nbits(prod_p))/60 < dixon_cost(d)
      @show "finishing with CRT"
      while nbits(prod_p)+nbits(d1) < Had
        change_prime(Ap, p)
        map_entries!(Ap, Nemo.fpField(p, false), A)
        d = _det(Ap)
        det_p = crt(det_p, prod_p, d, ZZ(p))
        Nemo.mul!(prod_p, prod_p, ZZ(p))
      end
      mis = mod_sym(det_p*invmod(d1, prod_p), prod_p)
      return d1*mis
    end
    @time T1 = hcol(TS, d)  
    push!(T, T1)
    @show :solve
    @time AT = solve_triu_strassen(T1, AT)
    @show nbits(prod_p), nbits(d1)
    @show nbits(abs(mod_sym(invmod(d1, prod_p)*det_p, prod_p)))
    if nbits(abs(mod_sym(invmod(d1, prod_p)*det_p, prod_p))) < small 
      break
    end
    @show nbits(d), Ainf
    if nbits(d) < Ainf + n
      @show :doin_hnf
      global last_hnf = (AT, d)
      h = hnf_modular_eldiv(AT, d)
      d1 *= prod([h[i,i] for i=1:n])
    @show Had / nbits(d1)  
      AT = solve_triu_strassen(h, AT)
      if nbits(abs(mod_sym(invmod(d1, prod_p)*det_p, prod_p))) < small
        break
      end
    end
  end
  det_p = invmod(d1, prod_p)*det_p
  @show det_p = mod_sym(det_p, prod_p)
  @assert nbits(abs(det_p)) < small
  h = hnf_modular_eldiv(AT, det_p)
  @show det(h) // det_p, det(h)
  d1 *= det(h)
  AT = solve_triu_strassen(h, AT)
    println("DOING UNICERTZ");
    @show uni_cost(d1)
    @show crt_cost(d1)
    #need to cost this as well
    global last_AT = AT
    @time fl = UniCertZ_CRT(AT)
    #           @assert fl == is_unit(det(ZAT));
    if fl
      return d1
    end
    return d1
    error("unimod failed")
end

#adaptive rational_reconstruction: if solution is unbalanced with
#denominator smaller than numerator
function ratrec(a::ZZMatrix, b::ZZRingElem)
  A = similar(a)
  D = ZZ(1)
  T = ZZ()
  n = ZZ()
  d = ZZ()
  for i=1:nrows(a)
    a_ptr = Nemo.mat_entry_ptr(a, i, 1)
    A_ptr = Nemo.mat_entry_ptr(A, i, 1)
    for j=1:ncols(a)
#      @show i, j
      ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ref{fmpz}, Ptr{fmpz}), T, a_ptr)
      Nemo.mul!(T, T, D)
      Nemo.mod!(T, T, b)
      fl = ratrec!(n, d, T, b)
      fl || return fl, A, D
      if !isone(d)
        D = D*d
        Nemo.mul!(A, A, d)
      end
      ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ptr{fmpz}, Ref{fmpz}), A_ptr, n)

      a_ptr += sizeof(ZZRingElem)
      A_ptr += sizeof(ZZRingElem)
    end
  end
  return true, A, D
end

function Nemo.div!(a::ZZRingElem, b::ZZRingElem, c::ZZRingElem)
  ccall((:fmpz_tdiv_q, Nemo.libflint), Cvoid, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), a, b, c)
end

function shift_right!(a::ZZRingElem, b::ZZRingElem, i::Int)
  ccall((:fmpz_fdiv_q_2exp, Nemo.libflint), Cvoid, (Ref{fmpz}, Ref{fmpz}, Int), a, b, i)
end

function ratrec(a::ZZRingElem, b::ZZRingElem)
  n = ZZ()
  d = ZZ()
  fl = ratrec!(n, d, a, b)
  return fl, n, d
end

function ratrec!(n::ZZRingElem, d::ZZRingElem, a::ZZRingElem, b::ZZRingElem)
  k = nbits(b)
  l = 1
  N = deepcopy(b)
  D = ZZ(2)

#  @assert 0<a<b
  done = false
  while !done && D <= N
    Nemo.mul!(D, D, D)
    div!(N, b, D)
    shift_right!(N, N, 1)
    if D>N
      D = N = iroot(b, 2)
      D = div(D, 2)
      done = true
    end

#    @assert 2*N*D < b

    fl = ccall((:_fmpq_reconstruct_fmpz_2, Nemo.libflint), Bool, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), n, d, a, b, N, D)

    if fl && (nbits(n)+nbits(d) < k - 30 || D>N)
      return fl
    end
    l += 1
  end
  return false
end

function Hecke.map_entries(k::Nemo.fpField, A::ZZMatrix)
  a = zero_matrix(k, nrows(A), ncols(A))
  return map_entries!(a, k, A)
end

function map_entries!(a::fpMatrix, k::Nemo.fpField, A::ZZMatrix)
  ccall((:fmpz_mat_get_nmod_mat, Nemo.libflint), Cvoid, (Ref{fpMatrix}, Ref{ZZMatrix}), a, A)
  return a
end

function change_prime(a::fpMatrix, p::UInt)
  a.n = p  #in flint 3.0 available as nmod_mat_set_mod
  a.norm = leading_zeros(p)
  a.ninv = ccall((:n_preinvert_limb_prenorm, Nemo.libflint), UInt, (UInt, ), p << a.norm)
end

function lift!(A::ZZMatrix, a::fpMatrix)
  ccall((:fmpz_mat_set_nmod_mat, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, Ref{fpMatrix}), A, a)
end

mutable struct DixonCtx
  bound::ZZRingElem
  Ainv::fpMatrix
  p::UInt
  crt_primes::Vector{UInt}
  A_mod::Vector{fpMatrix}
  d_mod::fpMatrix
  y_mod::fpMatrix
  Ay_mod::fpMatrix
  Ay::ZZMatrix
  x::ZZMatrix
  d::ZZMatrix
  A::ZZMatrix
  function DixonCtx()
    return new()
  end
end
#copied from flint to allow the use of adaptive reconstruction,
#support cases with small primes and Float64
function dixon_init(A::ZZMatrix, B::ZZMatrix)
  D = DixonCtx()
  D.A = A

  n = nrows(A)
  cols = ncols(B)

  _N = ZZ()
  _D = ZZ()
  ccall((:fmpz_mat_solve_bound, Nemo.libflint), Cvoid, (Ref{fmpz}, Ref{fmpz}, Ref{ZZMatrix}, Ref{ZZMatrix}), _N, _D, A, B)
  Ainv = zero_matrix(GF(2, cached = false), n, n)
  p = ccall((:fmpz_mat_find_good_prime_and_invert, Nemo.libflint), UInt, (Ref{fpMatrix}, Ref{ZZMatrix}, Ref{fmpz}), Ainv, A, _D)
  @assert p != 0
  D.p = p
  D.Ainv = Ainv

  D.bound = 2*maximum(abs, [_D, _N])^2 * 2^30
  D.crt_primes = UInt[]
  D.A_mod = fpMatrix[]
 
  pr = ZZ(1)
  xp = p
  maxA = maximum(abs, A) *(p-1)*n*2

  while true
    push!(D.crt_primes, xp)
    push!(D.A_mod, map_entries(Nemo.fpField(xp, false), A))
    pr *= xp
    if pr > maxA
      break
    end
    xp = next_prime(xp)
  end

  k = Nemo.fpField(p, false)
  D.d_mod = zero_matrix(k, nrows(B), ncols(B))
  D.y_mod = zero_matrix(k, nrows(B), ncols(B))
  D.Ay_mod = zero_matrix(k, nrows(B), ncols(B))
  D.Ay = zero_matrix(ZZ, nrows(B), ncols(B))
  D.x = zero_matrix(ZZ, nrows(B), ncols(B))

  return D
end

function dixon_solve(D::DixonCtx, B::ZZMatrix)
  zero!(D.x)
  d = deepcopy(B)
  ppow = ZZ(1)
  i = 1
  nexti = 1
  while ppow <= D.bound
    map_entries!(D.d_mod, Nemo.fpField(D.p, false), d)
    Nemo.mul!(D.y_mod, D.Ainv, D.d_mod)

    ccall((:fmpz_mat_scalar_addmul_nmod_mat_fmpz, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, Ref{fpMatrix}, Ref{fmpz}), D.x, D.y_mod, ppow)

    Nemo.mul!(ppow, ppow, D.p)
    if ppow > D.bound
      break
    end

    stabilised = i == nexti;

    if stabilised
      nexti = ceil(Int,(i*1.4)) + 1;
      fl, num, den = ratrec(D.x, ppow)

      if fl
        # fl = (D.A*num == den*B)
        sz = max(maximum(nbits, D.A) + maximum(nbits, num) 
                                     + nbits(ncols(B)) + 1, 
                 maximum(nbits, B) + nbits(den))
        if sz < nbits(ppow)
          @show "no prod neccessary"
        else
          xp = next_prime(D.p)
          @show ceil(Int, (sz - nbits(ppow))/60)
          for i=1:ceil(Int, (sz - nbits(ppow))/60)
            k = Nemo.fpField(xp, false)
            Ap = map_entries(k, D.A)
            Bp = map_entries(k, B)
            nump = map_entries(k, num)
            fl = Ap*nump == Bp*k(den)
            fl || break
            xp = next_prime(xp)
          end
        end
        @show fl
        fl && return num, den
      end
    end
  
    i += 1
#    i % 100 == 0 && @show i
#    i % 1000 == 0 && return

    prod = ZZ(1)
    if false
      Nemo.mul!(D.Ay, D.A, lift(D.y_mod))
    else
      for j=1:length(D.crt_primes)
        change_prime(D.y_mod, D.crt_primes[j])
        change_prime(D.Ay_mod, D.crt_primes[j])

        Nemo.mul!(D.Ay_mod, D.A_mod[j], D.y_mod)
        if j == 1
          lift!(D.Ay, D.Ay_mod)
          prod = ZZ(D.crt_primes[j])
        else
          induce_crt!(D.Ay, prod, D.Ay_mod, D.crt_primes[j], signed = true)
        end
      end
      change_prime(D.y_mod, D.p)
    end
    sub!(d, d, D.Ay)
    divexact!(d, d, ZZ(D.p))
  end
  fl, num, den = ratrec(D.x, ppow)

  @assert fl
#  @time @assert D.A*num == den*B
  return num, den
end


#= example

 A=rand(MatrixSpace(ZZ,10,10),1:10);
 DetS(A, -10:10)

 A=rand(MatrixSpace(ZZ,300,300),10:100);
 @time DetS(A)

=#


end # module
