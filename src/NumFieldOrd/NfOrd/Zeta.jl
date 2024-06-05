################################################################################
#
#        NfOrdClsZeta.jl: Zeta functions of orders in number fields
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
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

export zeta_log_residue

################################################################################
#
# Macros to make floating point life (hopefully) easier
#
################################################################################

macro with_round_down(expr, T)
  quote
    setrounding($(esc(T)), RoundDown) do
      $(esc(expr))
    end
  end
end

macro with_round_up(expr, T)
  quote
    setrounding($(esc(T)), RoundUp) do
      $(esc(expr))
    end
  end
end

################################################################################
#
#  Helper
#
################################################################################


# compute largest m such that a^m < b (strictly less then!)

function _max_power_in(a::ZZRingElem, b::Int)
  m = flog(ZZRingElem(b), a)
  if a^m == b
    m = m - 1
  end
  return m
end

_max_power_in(a::Int, b::Int) = _max_power_in(ZZRingElem(a), b)

################################################################################
#
#  Residue approximation apres
#  Belabas, Friedmann, "Computing the residue of the Dedekind zeta function"
#
################################################################################

# bounding the error
function _approx_error_bf(O::AbsSimpleNumFieldOrder, Tc = BigFloat)
  return _approx_error_bf(discriminant(O), degree(O), Tc)
end

# This function gives an upper bound on the error term of the Belabas-Friedmann
# approximation.
function _approx_error_bf(disc::ZZRingElem, degree::Int, Tc = BigFloat)

  logd_up = Tc(0)::Tc
  logd_down = Tc(0)::Tc
  sqrt_logd_up = Tc(0)::Tc

  setrounding(Tc,RoundDown) do
    logd_down = log(Tc(abs(disc)))
  end

  setrounding(Tc,RoundUp) do
    logd_up = log(Tc(abs(disc)))
    sqrt_logd_up = sqrt(logd_up)
  end

  n = BigFloat(degree)

  C1 = @with_round_down(Tc(FlintQQ(2324)//FlintQQ(1000)),Tc)
  C2 = @with_round_down(Tc(FlintQQ(388)//FlintQQ(100)),Tc)
  C3 = Tc(2)
  C4 = @with_round_down(Tc(FlintQQ(426)//FlintQQ(100)),Tc)

  function F(X)#(X::Tc)
    A1 = @with_round_down(C1*logd_down/(@with_round_up(sqrt(X)*log(3*X),Tc)),Tc)
    A2 = @with_round_down(1 + C2/@with_round_up(log(X/9),Tc),Tc)
    A3 = @with_round_down(1 + 2/sqrt_logd_up,Tc)
    A4 = @with_round_down(C4*(n-1)/@with_round_up(sqrt(X)*logd_up,Tc),Tc)

    return A1*(A2*A3^2 + A4)
  end
  return F
end

# Given f and C, this function computes a small x such that f(x) < C.
# It is assumed that f is monotone
function _find_threshold(f, C, ste, decreasing::Bool, Tc = BigFloat)
  T = Tc
  x0 =  T(70)
  x1 = x0

  y = f(x0)

  while y > C
    x0 = x1
    x1 = 2*x0
    y = f(x1)
  end

  dista = abs(x0-x1)

  while !( y < C && dista < ste)
    if y > C
      x1 = x0 + 3*dista/2
    else
      x1 = x0 - dista/2
    end

    dista = abs(x1-x0)

    x0 = x1
    y = f(x0)
  end
  return x0::Tc
end

  function _comp_summand(R, p::ZZRingElem, m::Int, aa::ArbFieldElem)
    logp = log(R(p))

    pm2 = R(p)^(R(FlintZZ(m)//FlintZZ(2)))

    pm2inv = inv(pm2)

    pro = logp * pm2inv

    # now p^(m/2) m log(p)

    pro2 = logp*pm2
    pro2 = pro2*m

    # Now the inverse
    inv2 = inv(pro2)

    # Now sqrt(x)log(X)/p^(m/2)*m*p
    pro3 = aa*inv2
    pro3 = pro3 - 1

    return pro*pro3
  end

  function _comp_summand(R, p::Int, m::Int, aa::ArbFieldElem)
    return _comp_summand(R, ZZRingElem(p), m, aa)
  end

# Computing the g_K(X) term of Belabas-Friedmann
function _term_bf(O::AbsSimpleNumFieldOrder, B::Int, R::ArbField)

  xx0 = B

  # I want xx0 to be divisible by 9!
  # Because I want xx0/9 to be an integer

  while !(mod(xx0,9) == 0)
    xx0 += 1
  end

  x = Float64(0)

  xx09 = div(xx0,9)

  p = 2

  summ = R(0)
  esumm = R(0)

  logxx0 = log(R(xx0))
  logxx09 = log(R(xx09))
  sqrtxx0 = sqrt(R(xx0))
  sqrtxx09 = sqrt(R(xx09))
  prodx = logxx0 * sqrtxx0
  prodx9 = logxx09 * sqrtxx09

  # small helper function (is this fast?)

  while p < xx0
    max_exp = _max_power_in(p, xx0)

    #println("maximal power is $max_exp")

    for m in 1:max_exp
      summand = _comp_summand(R, p, m, prodx)
      summ = summ - summand
    end

    #x += @elapsed

    lP = prime_decomposition_type(O, p)
    for P in lP
      Pnorm = ZZRingElem(p)^P[1]
      if Pnorm < xx0
        max_exp = _max_power_in(Pnorm, xx0)

        for m in 1:max_exp
          summand = _comp_summand(R, Pnorm, m, prodx)
          summ = summ + summand
        end
      end
    end

    if p < xx09

      max_exp = _max_power_in(p, xx09)

      for m in 1:max_exp
        summand  = _comp_summand(R, p, m, prodx9)
        summ = summ + summand
      end

      for P in lP
        Pnorm = ZZRingElem(p)^P[1]
        if (Pnorm < xx09)
          max_exp = _max_power_in(Pnorm, xx09)

          for m in 1:max_exp
            summand = _comp_summand(R, Pnorm, m, prodx9)
            summ = summ - summand
          end
        end
      end
    end
    p = next_prime(p)
  end

  log3xx0 = log(R(3*xx0))
  pr = sqrtxx0*2
  pr = pr * log3xx0
  pr = inv(pr)
  pr = pr*3
  pr = pr*summ

  return pr
end

# Approximate the residue
function _residue_approx_bf(O::AbsSimpleNumFieldOrder, error::Float64)
  F = _approx_error_bf(O, BigFloat)

  # magic constant
  # should be adapted to the input

  der = Int(20)

  @assert error > 0.5^der

  error_prime = @with_round_down(error - 0.5^der, BigFloat)

  error_prime = Float64(error_prime) # Do some correct rounding

  error_prime_arf = arf_struct(0, 0, 0, 0)
  ccall((:arf_init, libarb), Nothing, (Ref{arf_struct}, ), error_prime_arf)
  ccall((:arf_set_d, libarb), Nothing, (Ref{arf_struct}, Float64), error_prime_arf, error_prime)

  error_arf = arf_struct(0, 0, 0, 0)
  ccall((:arf_init, libarb), Nothing, (Ref{arf_struct}, ), error_arf)
  ccall((:arf_set_d, libarb), Nothing, (Ref{arf_struct}, Float64), error_arf, error)

  x0 = Int(ceil(_find_threshold(F, error_prime, Float64(10), true, Float64)))
  x0 = x0 + 1

  prec = 64

  val = _term_bf(O, x0, ArbField(prec, cached = false))

  valaddederror = deepcopy(val)
  ccall((:arb_add_error_arf, libarb), Nothing,
              (Ref{ArbFieldElem}, Ref{arf_struct}), valaddederror, error_prime_arf)

  while (!radiuslttwopower(val, -der)) ||
                !((radius(valaddederror)) < error)

    #println("Precision is now $prec")

    if prec > 2048
      error("Something wrong")
    end

    prec = 2*prec
    #println("increasing precision to $prec")
    val = _term_bf(O, x0, ArbField(prec, cached = false))
    valaddederror = deepcopy(val)
    ccall((:arb_add_error_arf, libarb), Nothing,
                (Ref{ArbFieldElem}, Ref{arf_struct}), valaddederror, error_prime_arf)
  end

  ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), error_prime_arf)
  ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), error_arf)

  return valaddederror
end

################################################################################
#
#  Toplevel function for users
#
################################################################################

@doc raw"""
    zeta_log_residue(O::AbsSimpleNumFieldOrder, error::Float64) -> ArbFieldElem

Computes the residue of the zeta function of $\mathcal O$ at $1$.
The output will be an element of type `ArbFieldElem` with radius less then
`error`.
"""
function zeta_log_residue(O::AbsSimpleNumFieldOrder, abs_error::Float64)
  degree(O) == 1 && error("Number field must be of degree > 1")
  return _residue_approx_bf(O, abs_error)
end
