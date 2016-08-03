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

function BigFloat(x::arb)
  a = BigFloat()
  b = BigFloat()
  ccall((:arb_get_interval_mpfr, :libarb), Void, (Ptr{BigFloat}, Ptr{BigFloat}, Ptr{arb}, Clong), &a, &b, &x, precision(BigFloat))
  return (a+b)/2
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

#function complex_roots(f::fmpz_poly; target_prec::Clong = 32,
#                                     initial_prec::Clong = 16)
#  res = Array(acb, degree(f))
#  r = ccall((:_acb_vec_init, :libarb), Ptr{acb_struct}, (Clong, ), degree(f))
#  ccall((:poly_roots, :libarb), Void, (Ptr{acb_struct},
#              Ptr{fmpz_poly}, Clong, Clong), r, &f, initial_prec, target_prec)
#  #r = reinterpret(Ptr{_raw_acb}, r)
#  for i in 1:degree(f)
#    res[i] = AcbField(target_prec)()
#    # slick julia pointer arithmetic
#    ccall((:acb_set, :libarb), Void, (Ptr{acb}, Ptr{acb_struct}),
#                &res[i], r + (i-1)*sizeof(acb_struct))
#  end
#  ccall((:_acb_vec_clear, :libarb), Void, (Ptr{acb_struct}, Clong), r, degree(f))
#  return res
#end

function _roots(x::Union{fmpq_poly, fmpz_poly}, abs_tol = 32, initial_prec = 0, max_iter = 0)
  roots = acb_vec(degree(x))
  deg = degree(x)

  initial_prec = (initial_prec >= 2) ? initial_prec : 32

  wp = initial_prec

  while true
    in_roots = (wp == initial_prec) ? C_NULL : roots
    step_max_iter = (max_iter >= 1) ? max_iter : min(max(deg, 32), wp)
    y = acb_poly(x, wp) 
    isolated = ccall((:acb_poly_find_roots, :libarb), Int,
            (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{acb_struct}, Int, Int),
            roots, &y, in_roots, step_max_iter, wp)


    if isolated == deg
      ok = true
      if abs_tol > 0
        for i = 0 : deg-1
          re = ccall((:acb_real_ptr, :libarb), Ptr{Nemo.arb_struct},
                (Ptr{acb}, ), roots + i * sizeof(acb_struct))
          im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                (Ptr{acb}, ), roots + i * sizeof(acb_struct))
          t = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), re)
          u = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), im)
          ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), t, -abs_tol) <= 0)
          ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), u, -abs_tol) <= 0)
        end
      end
      real_ok = ccall((:acb_poly_validate_real_roots, :libarb),
          Bool, (Ptr{acb_struct}, Ptr{acb_poly}, Int), roots, &y, wp)

      if !real_ok
          ok = false
      end

      if real_ok
          for i = 0 : deg - 1
              im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                  (Ptr{acb}, ), roots + i * sizeof(acb_struct))
              if ccall((:arb_contains_zero, :libarb), Bool, (Ptr{Nemo.arb_struct}, ), im)
                  ccall((:arb_zero, :libarb), Void, (Ptr{Nemo.arb_struct}, ), im)
              end
          end
      end

      if ok
        break
      end
    end

  wp = wp * 2
    if wp > 2^16
      error("Something wrong")
    end
  end
         ccall((:_acb_vec_sort_pretty, :libarb), Void,
            (Ptr{acb_struct}, Int), roots, deg)
        res = array(AcbField(wp), roots, deg)
  acb_vec_clear(roots, deg)
  return res
end


function _roots(x::Union{fmpq_poly, fmpz_poly}, roots::Ptr{acb_struct}, abs_tol = 32, initial_prec = 0, max_iter = 0)
  deg = degree(x)

  initial_prec = (initial_prec >= 2) ? initial_prec : 32

  wp = initial_prec

  while true
    in_roots = roots
    step_max_iter = (max_iter >= 1) ? max_iter : min(max(deg, 32), wp)
    y = acb_poly(x, wp) 
    isolated = ccall((:acb_poly_find_roots, :libarb), Int,
            (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{acb_struct}, Int, Int),
            roots, &y, in_roots, step_max_iter, wp)


    if isolated == deg
      ok = true
      if abs_tol > 0
        for i = 0 : deg-1
          re = ccall((:acb_real_ptr, :libarb), Ptr{Nemo.arb_struct},
                (Ptr{acb}, ), roots + i * sizeof(acb_struct))
          im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                (Ptr{acb}, ), roots + i * sizeof(acb_struct))
          t = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), re)
          u = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), im)
          ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), t, -abs_tol) <= 0)
          ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), u, -abs_tol) <= 0)
        end
      end
      real_ok = ccall((:acb_poly_validate_real_roots, :libarb),
          Bool, (Ptr{acb_struct}, Ptr{acb_poly}, Int), roots, &y, wp)

      if !real_ok
          ok = false
      end

      if real_ok
          for i = 0 : deg - 1
              im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                  (Ptr{acb}, ), roots + i * sizeof(acb_struct))
              if ccall((:arb_contains_zero, :libarb), Bool, (Ptr{Nemo.arb_struct}, ), im)
                  ccall((:arb_zero, :libarb), Void, (Ptr{Nemo.arb_struct}, ), im)
              end
          end
      end

      if ok
        break
      end
    end

  wp = wp * 2
    if wp > 2^16
      error("Something wrong")
    end
  end
         ccall((:_acb_vec_sort_pretty, :libarb), Void,
            (Ptr{acb_struct}, Int), roots, deg)
        res = array(AcbField(wp), roots, deg)
  return res
end

function radiuslttwopower(x::arb, e::Int)
  t = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), &x)
  b = ccall((:mag_cmp_2exp_si, :libarb), Cint,
          (Ptr{Nemo.mag_struct}, Int), t, e) <= 0
  return b
end

function radiuslttwopower(x::acb, e::Int)
  re = ccall((:acb_real_ptr, :libarb), Ptr{Nemo.arb_struct},
          (Ptr{acb}, ), &x)
  im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
          (Ptr{acb}, ), &x)
  t = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), re)
  u = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), im)
  ok = (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), t, e) <= 0)
  ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), u, e) <= 0)
  return ok
end

