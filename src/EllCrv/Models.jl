################################################################################
#
#          EllCrv/Models.jl : Different models of elliptic curves
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
# (C) 2016 Tommy Hofmann
# (C) 2016 Robin Ammon
# (C) 2016 Sofia Brenner
# (C) 2022 Jeroen Hanselman
#
################################################################################

export short_weierstrass_model, is_short_weierstrass_model, simplified_model, 
is_simplified_model, integral_model, is_integral_model

################################################################################
#
# Short Weierstrass model
#
################################################################################

@doc Markdown.doc"""
    short_weierstrass_model(E::EllCrv{fmpq}) -> 
      (EE::EllCrv, EllCrvIso, EllCrvIso)

Transform a curve given in long Weierstrass form over QQ to short Weierstrass
form. Return short form and both transformations for points on the curve;
first transformation from E (long form) to EE (short form), 
second transformation is the inverse of this map.
"""
function short_weierstrass_model(E::EllCrv)
  
  R = base_field(E)
  p = characteristic(R)

  if p == 2 || (p == 3 && j_invariant(E) == 0)
      error("Conversion to short weierstrass form is not possible.")
  end
  return simplified_model(E)
  #return _short_weierstrass_model(E)
end

function _short_weierstrass_model(E::EllCrv{T}) where T
  R = base_field(E)
  p = characteristic(R)

  if (p == 2) || (p == 3)
      error("Converting to short form not possible in characteristic 2 and 3")
  end

  a1, _, a3= a_invars(E)

  b2, b4, b6, b8 = b_invars(E)

  c4, c6 = c_invars(E)

  Anew = -divexact(c4, 48)
  Bnew = -divexact(c6, 864)

  EE = EllipticCurve([Anew, Bnew])::EllCrv{T}

  # we are hitting https://github.com/JuliaLang/julia/issues/15276

  _b2 = deepcopy(b2)
  _a1 = deepcopy(a1)
  _a3 = deepcopy(a3)

  # transforms a point on E (long form) to a point on EE (short form)
  trafo = function(P::EllCrvPt)

    if P.is_infinite
      return infinity(EE)
    end

    xnew = P.coordx + divexact(_b2, 12)
    ynew = P.coordy + divexact(_a1*P.coordx + _a3, 2)
    Q = EE([xnew, ynew])::EllCrvPt{T}
    return Q
  end

  # transforms a point on EE (short form) back to a point on E (long form)
  ruecktrafo = function(R::EllCrvPt)
    if R.is_infinite
        return infinity(E)
    end

    xnew = R.coordx - divexact(_b2, 12)
    ynew = R.coordy - divexact(_a1*xnew + _a3, 2)
    S = E([xnew, ynew])
    return S::EllCrvPt{T}
  end

  # type annotation necessary due to #15276
  return EE::EllCrv{T}, trafo, ruecktrafo
end


@doc Markdown.doc"""
    is_short_weierstrass_model(E::EllCrv) -> Bool

Return true if E is in short Weierstrass form. 
"""
function is_short_weierstrass_model(E::EllCrv)
  return E.short
end



################################################################################
#
#  Simplified models
#
################################################################################

@doc Markdown.doc"""
    simplified_model(E::EllCrv) -> 
      (EE::EllCrv, function(EllCrvPt), function(EllCrvPt))

Transform an elliptic curve to simplified Weierstrass form as defined in Connell. 
Return simplified form and both transformations for points on the curve;
first transformation from E (original) to EE (simplified), 
second transformation is the inverse of this map.

Returns short Weierstrass form if $\char K \neq 2, 3$,
Returns equation of the form $y^2 + xy = x^3 + a2x^2 + a6$ 
if $\char K = 2$  and $j(E) \neq 0$,
Returns equation of the form $y^2 + a3y = x^3 + a4x + a6$ 
if $\char K = 2$ and $j(E) = 0$.
Returns equation of the form $y^2 = x^3 + a2x^2 + a6$ 
if $\char K = 3$ and $j(E) \neq 0$,
Returns equation of the form $y^2 = x^3 + a4x + a6$ 
if $\char K = 3$ and $j(E) = 0$.
"""
#Magma returns minimal model if base field is QQ. Not sure if we want the same.
function simplified_model(E::EllCrv) 
  K = base_field(E)
  a1, a2, a3, a4, a6 = a_invars(E)
  if characteristic(K) == 2 
    if j_invariant(E) == 0
      return transform_rstu(E, [a2, 0, 0, 1])
    else
      return transform_rstu(E, [a3//a1, 0, a4//a1 + a3^2//a1^3, a1])
    end
  end
  
  if characteristic(K)==3
    if j_invariant(E) == 0
      return transform_rstu(E, [0, a1, a3, 1])
    else
      b2, b4 = b_invars(E)
      return transform_rstu(E, [-b4//b2, a1, a3 - a1*b4//b2, 1])
    end
  end
  
  b2, b4 = b_invars(E)
  
  return transform_rstu(E, [-b2//12, -a1//2, -a3//2 + a1*b2//24, 1])
end


@doc Markdown.doc"""
    is_simplified_model(E::EllCrv) -> Bool

Return true if E is a simplified model. 
"""
function is_simplified_model(E::EllCrv)
  K = base_field(E)
  a1, a2, a3, a4, a6 = a_invars(E)
  if characteristic(K) == 2
    if j_invariant(E) == 0
      return (a1, a2) == (0, 0)
    else
      return (a1, a3, a4) == (1, 0, 0)
    end
  end
  
  if characteristic(K) == 3
    if j_invariant(E) == 0
      return (a1, a2, a3) == (0, 0, 0)
    else
      return (a1, a3, a4) == (0, 0, 0)
    end
  end
  
  return is_short_weierstrass_model(E)
end


################################################################################
#
#  Integral models
#
################################################################################

@doc Markdown.doc"""
    integral_model(E::EllCrv{fmpq}) -> (F::EllCrv{fmpz}, function, function)

Given an elliptic curve $E$ over $\mathbf Q$ in short form, returns an
isomorphic curve $F$ with model over $\mathbf Z$. The second and third
return values are the isomorpisms $E \to F$ and $F \to E$.
"""
function integral_model_old(E::EllCrv{fmpq})
  _, _, _, A, B = a_invars(E)

  mue = lcm(denominator(A), denominator(B))
  Anew = mue^4 * A
  Bnew = mue^6 * B
  E_int = EllipticCurve([Anew, Bnew])

  trafo_int = function(P) # transformes a point on E into a point on E_int
    if P.is_infinite
      return infinity(E_int)
    end

    xnew = mue^2 * P.coordx
    ynew = mue^3 * P.coordy
    Q = E_int([xnew, ynew])
    return Q
  end

  trafo_rat = function(R) # transformes a point on E_int back into a point on E
    if R.is_infinite
      return infinity(E)
    end

    xnew = divexact(R.coordx, mue^2)
    ynew = divexact(R.coordy, mue^3)
    S = E([xnew, ynew])
    return S
  end

  return E_int::EllCrv{fmpq}, trafo_int, trafo_rat
end

@doc Markdown.doc"""
    integral_model(E::EllCrv{T}) -> (F::EllCrv{T}, EllCrvIso, EllCrvIso) 
      where T<:Union{fmpq, nf_elem}

Given an elliptic curve $E$ over QQ or a number field $K$, returns an
isomorphic curve $F$ with model over $\mathcal{O}_K$. The second and third
return values are the isomorpisms $E \to F$ and $F \to E$.
"""
function integral_model(E::EllCrv{T}) where T<:Union{fmpq, nf_elem}

  a1, a2, a3, a4, a6 = map(denominator, a_invars(E))
  mu = lcm(a1, a2, a3, a4, a6)
  return transform_rstu(E, [0, 0, 0, 1//mu])
end

@doc Markdown.doc"""
    is_integral_model(E::EllCrv{T}) -> Bool where T<:Union{fmpq, nf_elem}

Given an elliptic curve $E$ over QQ or a number field $K$, return
true if $E$ is an integral model of $E$.
"""
function is_integral_model(E::EllCrv{T}) where T<:Union{fmpq, nf_elem}

  a1, a2, a3, a4, a6 = map(denominator, a_invars(E))
  mu = lcm(a1, a2, a3, a4, a6)
  if mu == 1
    return true
  end
  
  return false
end


