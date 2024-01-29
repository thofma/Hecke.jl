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

function fillacb!(r::Ptr{acb_struct}, s::Vector{AcbFieldElem})
  for i in 1:length(s)
    ccall((:acb_set, libarb), Nothing, (Ptr{acb_struct}, Ref{AcbFieldElem}),
          r + (i - 1) * sizeof(acb_struct), s[i])
  end
end

################################################################################
#
#  Field access
#
################################################################################

precision(x::acb_root_ctx) = x.prec

poly(x::acb_root_ctx) = x.poly

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::acb_root_ctx)
  print(io, "acb_root_ctx of $(poly(x)) with precision $(precision(x))")
end

################################################################################
#
#  Refining
#
################################################################################

# This will refine the roots to given target_prec
# If none is given, double the precision
function refine(x::acb_root_ctx, target_prec::Int = 2*precision(x))

  if target_prec < precision(x)
    return nothing
  end

  x.roots = _refine_roots!(x.poly, x._roots, target_prec, target_prec)
  x.prec = target_prec

  r, s = x.signature

  for i in 1:r
    x.real_roots[i] = real(x.roots[i])
  end

  j = 0
  for i in r+1:degree(x.poly)
    if is_positive(imag(x.roots[i]))
      j += 1
      x.complex_roots[j] = x.roots[i]
    end
  end
  @assert j == s
  nothing
end

function _evaluate(x::QQPolyRingElem, y::AcbFieldElem)
  z = parent(y)(0)
  for i in 0:degree(x)
    z = z + coeff(x,i)*y^i
  end
  return z
end

################################################################################
#
#  Complex root isolation for ZZPolyRingElem/QQPolyRingElem
#
################################################################################

# Assume that roots points to an array of deg many AcbFieldElem's.
# This function checks if the radius of the real and imaginary parts
# are smaller then 2^(-abs_tol).
function _validate_size_of_zeros(roots::Ptr{acb_struct}, deg::Int, abs_tol::Int)
  ok = true
  if abs_tol < 0
    return true
  end

  for i = 0 : deg-1
    re = ccall((:acb_real_ptr, libarb), Ptr{Nemo.arb_struct},
          (Ptr{AcbFieldElem}, ), roots + i * sizeof(acb_struct))
    im = ccall((:acb_imag_ptr, libarb), Ptr{Nemo.arb_struct},
          (Ptr{AcbFieldElem}, ), roots + i * sizeof(acb_struct))
    t = ccall((:arb_rad_ptr, libarb), Ptr{Nemo.mag_struct}, (Ptr{ArbFieldElem}, ), re)
    u = ccall((:arb_rad_ptr, libarb), Ptr{Nemo.mag_struct}, (Ptr{ArbFieldElem}, ), im)
    ok = ok && (ccall((:mag_cmp_2exp_si, libarb), Cint,
        (Ptr{Nemo.mag_struct}, Int), t, -abs_tol) <= 0)
    ok = ok && (ccall((:mag_cmp_2exp_si, libarb), Cint,
        (Ptr{Nemo.mag_struct}, Int), u, -abs_tol) <= 0)
    if !ok
      break
    end
  end
  if !ok
    return false
  end
  return true
end

# Return the roots of x with radii < 2^(-abs_tol) as Vector{AcbFieldElem}.
# It is assumed that x is squarefree
function _roots(x::Union{QQPolyRingElem, ZZPolyRingElem}, abs_tol::Int = 32, initial_prec::Int = abs_tol, max_iter = 0::Int)
  d = degree(x)
  roots = acb_vec(d)

  wp = _roots!(roots, x, abs_tol, initial_prec, max_iter, false)

  res = array(AcbField(wp, cached = false), roots, d)
  acb_vec_clear(roots, d)
  return res
end

# Assume that roots points to approximations of the roots of x.
# This function updates roots inplace to radii <= 2^(-abs_tol) and returns
# the roots as Vector{AcbFieldElem}.
# It is assumed that x is squarefree
function _refine_roots!(x::Union{QQPolyRingElem, ZZPolyRingElem}, roots::Ptr{acb_struct},
                                                        abs_tol::Int = 32,
                                                        initial_prec::Int = abs_tol,
                                                        max_iter::Int = 0)
  wp = _roots!(roots, x, abs_tol, initial_prec, max_iter, true)
  res = array(AcbField(wp, cached = false), roots, degree(x))
  return res
end

# This is the workhorse.
# It computes the roots of x with with radii <= 2^(-abs_tol)
# The result will be stored in roots
# If have_approx = true, it is assumed that roots contains approximations
# to the roots.
function _roots!(roots::Ptr{acb_struct}, x::Union{QQPolyRingElem, ZZPolyRingElem},
                                         abs_tol::Int = 32,
                                         initial_prec::Int = 0,
                                         max_iter::Int = 0,
                                         have_approx::Bool = false)
  deg = degree(x)

  initial_prec = (initial_prec >= 2) ? initial_prec : abs_tol

  wp = initial_prec

  while true
    in_roots = roots
    step_max_iter = (max_iter >= 1) ? max_iter : min(max(deg, div(wp, 4)), wp)
    y = AcbPolyRingElem(x, wp)

    if have_approx
      isolated = ccall((:acb_poly_find_roots, libarb), Int,
              (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int),
              roots, y, in_roots, step_max_iter, wp)
    else
      isolated = ccall((:acb_poly_find_roots, libarb), Int,
              (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int),
              roots, y, C_NULL, step_max_iter, wp)
    end

    if isolated < deg
      wp *= 2
      continue
    end
    have_approx = true

    if isolated == deg
      have_approx = true
      ok = _validate_size_of_zeros(roots, deg, abs_tol)
      real_ok = ccall((:acb_poly_validate_real_roots, libarb),
          Bool, (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Int), roots, y, wp)

      if !real_ok
          ok = false
      else
        for i = 0 : deg - 1
            im = ccall((:acb_imag_ptr, libarb), Ptr{Nemo.arb_struct},
                (Ptr{AcbFieldElem}, ), roots + i * sizeof(acb_struct))
            if ccall((:arb_contains_zero, libarb), Bool, (Ptr{Nemo.arb_struct}, ), im)
                ccall((:arb_zero, libarb), Nothing, (Ptr{Nemo.arb_struct}, ), im)
            end
        end
      end

      if ok
        break
      end
    end

    wp = wp * 2
    if wp > 2^22
      error("Aborting since required precision is > 2^22")
    end
  end

  ccall((:_acb_vec_sort_pretty, libarb), Nothing,
        (Ptr{acb_struct}, Int), roots, deg)

  return wp
end

function radiuslttwopower(x::ArbFieldElem, e::Int)
  GC.@preserve x begin
    t = ccall((:arb_rad_ptr, libarb), Ptr{Nemo.mag_struct}, (Ref{ArbFieldElem}, ), x)
    b = ccall((:mag_cmp_2exp_si, libarb), Cint,
            (Ptr{Nemo.mag_struct}, Int), t, e) <= 0
  end
  return b
end

function radiuslttwopower(x::AcbFieldElem, e::Int)
  GC.@preserve x begin
    re = ccall((:acb_real_ptr, libarb), Ptr{Nemo.arb_struct},
            (Ref{AcbFieldElem}, ), x)
    im = ccall((:acb_imag_ptr, libarb), Ptr{Nemo.arb_struct},
            (Ref{AcbFieldElem}, ), x)
    t = ccall((:arb_rad_ptr, libarb), Ptr{Nemo.mag_struct}, (Ptr{ArbFieldElem}, ), re)
    u = ccall((:arb_rad_ptr, libarb), Ptr{Nemo.mag_struct}, (Ptr{ArbFieldElem}, ), im)
    ok = (ccall((:mag_cmp_2exp_si, libarb), Cint,
                (Ptr{Nemo.mag_struct}, Int), t, e) <= 0)
    ok = ok && (ccall((:mag_cmp_2exp_si, libarb), Cint,
                (Ptr{Nemo.mag_struct}, Int), u, e) <= 0)
  end
  return ok
end

function arb_trim(x::ArbFieldElem)
  z = ArbFieldElem()
  ccall((:arb_trim, libarb), Nothing, (Ref{Nemo.ArbFieldElem}, Ref{Nemo.ArbFieldElem}), z, x)
  z.parent = ArbField(arb_bits(z), cached = false)
  return z
end

function rel_error_bits(x::ArbFieldElem)
  return ccall((:arb_rel_error_bits, libarb), Int, (Ref{Nemo.ArbFieldElem}, ), x)
end

function rel_accuracy(x::ArbFieldElem)
  return ccall((:arb_rel_accuracy_bits, libarb), Int, (Ref{Nemo.ArbFieldElem}, ), x)
end

function set!(z::ArbFieldElem, x::ArbFieldElem)
  ccall((:arb_set, libarb), Nothing, (Ref{Nemo.ArbFieldElem}, Ref{Nemo.ArbFieldElem}), z, x)
  return z
end

function rel_error_bits(x::AcbFieldElem)
  return ccall((:acb_rel_error_bits, libarb), Int, (Ref{Nemo.AcbFieldElem}, ), x)
end

function rel_accuracy(x::AcbFieldElem)
  return ccall((:acb_rel_accuracy_bits, libarb), Int, (Ref{Nemo.AcbFieldElem}, ), x)
end

function set!(z::AcbFieldElem, x::AcbFieldElem)
  ccall((:acb_set, libarb), Nothing, (Ref{Nemo.AcbFieldElem}, Ref{Nemo.AcbFieldElem}), z, x)
  return z
end

function expand!(x::Union{ArbFieldElem, AcbFieldElem}, max_radius_2exp::Int)
  if rel_accuracy(x) < 0
    # Radius has less precision then the midpoint
    # Think of 0.100001 +/- 10
    # Reducing the precision of the midpoint won't help.
    return x
  end
  if is_exact(x)
    return x
  end
  z = deepcopy(x)
  p = bits(x)
  q = div(p, 2)
  if q < 2
    return x
  end
  y = round(x, q)
  while radiuslttwopower(y, max_radius_2exp) && q > 4
    q = div(q, 2)
    set!(x, y)
    y = round!(y, y, q)
  end
  x.parent = parent_type(typeof(x))(max(2, bits(x)), cached = false)
  @assert radiuslttwopower(x, max_radius_2exp)
  return x
end

function expand(x::Union{ArbFieldElem, AcbFieldElem}, max_radius_2exp::Int)
  z = deepcopy(x)
  expand!(z, max_radius_2exp)
  return z
end
