################################################################################
#
#             acb_root_ctx.jl: handling roots using arb
#
# This file is part of hecke.
#
# Copyright (c) 2015: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2015 Tommy Hofmann
#
################################################################################
#
#  TODO:
#  - Documentation
#
################################################################################

export acb_root_ctx, complex_roots

################################################################################
#
#  Types and memory management
#
################################################################################

function BigFloat(x::arb)
  a = BigFloat()
  b = BigFloat()
  ccall((:arb_get_interval_mpfr, :libarb), Void, (Ptr{BigFloat}, Ptr{BigFloat}, Ptr{arb}, Clong), &a, &b, &x, precision(BigFloat))
  return (a+b)/2
end

type acb_root_ctx
  poly::fmpq_poly
  _roots::Ptr{acb_struct}
  prec::Int
  roots::Array{acb, 1}
  real_roots::Array{acb, 1}
  complex_roots::Array{acb, 1}

  function acb_root_ctx(x::fmpq_poly)
    p = 32 
    y = ccall((:_acb_vec_init, :libarb), Ptr{acb_struct}, (Clong, ), degree(x))
    t = acb_poly(x, p)
    n = ccall((:acb_poly_find_roots, :libarb), Clong,
                (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{Void}, Clong , Clong),
                y, &t, C_NULL, 0, p)
    while n < degree(x)
      p *= 2
      n = ccall((:acb_poly_find_roots, :libarb), Clong,
                  (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{Void}, Clong , Clong),
                  y, &t, y, 0, p)
    end
    z = new()
    z._roots = y
    z.prec = p
    z.poly = x
    finalizer(z, _acb_root_ctx_clear_fn)
    _find_real(z)
    return z
  end

  function acb_root_ctx(x::fmpq_poly, p::Int)
    z = new()
    z._roots = ccall((:_acb_vec_init, :libarb), Ptr{acb_struct},
                            (Clong, ), degree(x))
    finalizer(z, _acb_root_ctx_clear_fn)
    t = acb_poly(x, p)
    n = ccall((:acb_poly_find_roots, :libarb), Clong,
                (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{Void}, Clong , Clong),
                z._roots, &t, C_NULL, 0, p)
    n < degree(x) && error("Precision not high enough")
    z.prec = p
    z.poly = x
    _find_real(z)
    return z
  end
end

function _acb_root_ctx_clear_fn(x::acb_root_ctx)
  ccall((:_acb_vec_clear, :libarb), Void,
              (Ptr{acb_struct}, Clong), x._roots, degree(x.poly))
end

################################################################################
#
#  Field access
#
################################################################################

prec(x::acb_root_ctx) = x.prec

poly(x::acb_root_ctx) = x.poly

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::acb_root_ctx)
  print(io, "acb_root_ctx of $(poly(x)) with precision $(prec(x))")
end

################################################################################
#
#  Refining
#
################################################################################

# This will refine the roots to given target_prec
# If none is given, double the precision

function refine(x::acb_root_ctx, target_prec::Int = 2*prec(x))
  if target_prec < prec(x)
    return nothing
  end
  p = prec(x)
  f = acb_poly(x.poly, p)
  n = ccall((:acb_poly_find_roots, :libarb), Clong,
          (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{Void}, Clong , Clong),
          x._roots, &f, x._roots, 0, p)
  while n != degree(x.poly) || !Bool(ccall((:check_accuracy, :libarb),
                                     Cint, (Ptr{acb_struct}, Clong, Clong),
                                     x._roots, degree(x.poly), target_prec))
    p *= 2
    f = acb_poly(poly(x), p)
    n = ccall((:acb_poly_find_roots, :libarb), Clong,
                (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{Void}, Clong , Clong),
                x._roots, &f, C_NULL, 0, p)
  end
  x.prec = target_prec
  _find_real(x)
  nothing
end

# I don't think this function is correct
# Need a way to prove that some ball contains real root (or not)
# Change of sign? Sturm?

function _find_real(x::acb_root_ctx)
  r,s = signature(x.poly)
  R = Array(acb, r)
  C = Array(acb, s)
  j = 0
  k = 0
  A = Array(acb, degree(x.poly))
  for i in 1:degree(x.poly)
    _r = unsafe_load(x._roots, i)
    r = AcbField(x.prec)()
    ccall((:acb_set, :libarb), Void, (Ptr{acb}, Ptr{acb_struct}), &r, &_r)
    A[i] = r
    #println("trying to insert $r")
    if contains_zero(imag(A[i]))
      j += 1
      R[j] = A[i]
    else
      b = true
      for l in 1:k
        if contains_zero(imag(A[i]) + imag(C[l])) &&
                      contains_zero(real(A[i]) - real(C[l]))
          b = false
        end
      end
      if b
        k += 1
        C[k] = A[i]
      end
    end
  end
  x.roots = A
  x.real_roots = R
  x.complex_roots = C
end

function _evaluate(x::fmpq_poly, y::acb)
  z = parent(y)(0)
  for i in 0:degree(x)
    z = z + coeff(x,i)*y^i
  end
  return z
end

################################################################################
#
#  Complex root isolation for fmpz_poly/fmpq_poly
#
################################################################################

function complex_roots(f::fmpz_poly; target_prec::Clong = 32,
                                     initial_prec::Clong = 16)
  res = Array(acb, degree(f))
  r = ccall((:_acb_vec_init, :libarb), Ptr{acb_struct}, (Clong, ), degree(f))
  ccall((:poly_roots, :libarb), Void, (Ptr{acb_struct},
              Ptr{fmpz_poly}, Clong, Clong), r, &f, initial_prec, target_prec)
  #r = reinterpret(Ptr{_raw_acb}, r)
  for i in 1:degree(f)
    res[i] = AcbField(target_prec)()
    # slick julia pointer arithmetic
    ccall((:acb_set, :libarb), Void, (Ptr{acb}, Ptr{acb_struct}),
                &res[i], r + (i-1)*sizeof(acb_struct))
  end
  ccall((:_acb_vec_clear, :libarb), Void, (Ptr{acb_struct}, Clong), r, degree(f))
  return res
end

