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
    Copyright (C) 2020,2023 Claus Fieker
=#

module Strassen
using Hecke
using LinearAlgebra, Profile, Base.Intrinsics
import Hecke.AbstractAlgebra, Hecke.Nemo
import Hecke.Nemo: add!, mul!, zero!, sub!, AbstractAlgebra._solve_triu!, AbstractAlgebra._solve_tril!

const cutoff = 1500

#base case for the strassen
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

#see AbstractAlgebra.Strassen for an MatElem version

end # module
