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
  real_roots::Array{arb, 1}
  complex_roots::Array{acb, 1}
  signature::Tuple{Int, Int}

  function acb_root_ctx(x::fmpq_poly, p::Int = 32)
    z = new()
    z.roots = _roots(x, p, p)
    z.poly = x
    z.prec = p
    z._roots = acb_vec(degree(x))
    r, s = signature(x)
    z.signature = (r, s)

    for i = 1:degree(x)
      ccall((:acb_set, :libarb), Void, (Ptr{acb_struct}, Ptr{acb}),
            z._roots + (i - 1) * sizeof(acb_struct), &z.roots[i])
    end

    z.prec = p
    A = Array(arb, z.signature[1])
    B = Array(acb, z.signature[2])

    for i in 1:r
      @assert isreal(z.roots[i])
      A[i] = real(z.roots[i])
    end

    j = 0
    for i in r+1:degree(x)
      if ispositive(imag(z.roots[i]))
        j += 1
        B[j] = z.roots[i]
      end
    end

    @assert j == s

    z.real_roots = A
    z.complex_roots = B

    finalizer(z, _acb_root_ctx_clear_fn)

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

  x.roots = _roots(x.poly, x._roots, target_prec, target_prec)
  x.prec = target_prec

  r, s = x.signature

  for i in 1:r
    x.real_roots[i] = real(x.roots[i])
  end

  j = 0
  for i in r+1:degree(x.poly)
    if ispositive(imag(x.roots[i]))
      j += 1
      x.complex_roots[j] = x.roots[i]
    end
  end
  @assert j == s
  nothing
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

