################################################################################
#
#       DedekindCriterion.jl : Dedekinds Criterion for maximality
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
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

function dedekind_test(O::NfOrd, p::fmpz, compute_order::Type{Val{S}} = Val{true}) where S
  !isequation_order(O) && error("Order must be an equation order")

  if rem(discriminant(O), p^2) != 0
    if compute_order == Val{true}
      return true, O
    else
      return true
    end
  end

  Zy, y = PolynomialRing(FlintZZ, "y")
  Kx, x = PolynomialRing(ResidueRing(FlintZZ, p, cached=false), "x", cached=false)

  f = nf(O).pol

  Zyf = Zy(f)

  fmodp = Kx(Zyf) 
 
  fac = factor_squarefree(fmodp)

  g = prod(x for x in keys(fac.fac))
  h = divexact(fmodp,g)

  # first build 1/p ( f - g*h)
  gZ = lift(Zy,g)
  hZ = lift(Zy, h)

  g1 = Zyf - gZ*hZ

  for i in 0:degree(g1)
    q,r = divrem(coeff(g1,i),p)
    @assert r == 0
    setcoeff!(g1,i,q)
  end
  
  g1modp = Kx(g1)

  if compute_order == Val{false}
    if isone(gcd(g,h, g1modp))
      return true
    else
      return false
    end
  else
    pmaximal = true

    U = gcd(gcd(g, h), g1modp)
    pmaximal = (isone(U)) 

    if pmaximal
      return true, O
    end

    @hassert :NfOrd 1 rem(fmodp, U) == zero(Kx)
    U = divexact(fmodp, U)

    @hassert :NfOrd 1 rem(O.disc, p^2) == 0

    alpha = nf(O)(parent(f)(lift(Zy,U)))

    # build the new basis matrix
    # we have to take the representation matrix of alpha!
    # concatenating the coefficient vector won't help
    n = _hnf_modular_eldiv(representation_mat(alpha), p, :lowerleft)
    b = FakeFmpqMat(n,p)
    @hassert :NfOrd 1 defines_order(nf(O), b)[1]
    OO = Order(nf(O), b, false)

    OO.isequation_order = false

    OO.disc = divexact(O.disc, p^(2*(degree(O)-degree(U))))

    return false, OO
  end
end



dedekind_test(O::NfOrd, p::Integer) = dedekind_test(O, FlintZZ(p))

dedekind_ispmaximal(O::NfOrd, p::fmpz) = dedekind_test(O, p, Val{false})

dedekind_ispmaximal(O::NfOrd, p::Integer) = dedekind_ispmaximal(O, FlintZZ(p))

dedekind_poverorder(O::NfOrd, p::fmpz) = dedekind_test(O, p)[2]

dedekind_poverorder(O::NfOrd, p::Integer) = dedekind_poverorder(O, FlintZZ(p))


###############################################################################
#
#  Non-prime case
#
###############################################################################

function dedekind_test_composite(O::NfOrd, p::fmpz)
  !isequation_order(O) && error("Order must be an equation order")

  if rem(discriminant(O), p) != 0
    return fmpz(1), true, O
  end

  Zy, y = PolynomialRing(FlintZZ, "y")
  R = ResidueRing(FlintZZ, p, cached=false)
  Kx, x = PolynomialRing(R, "x", cached=false)

  f = nf(O).pol

  Zyf = Zy(f)

  fmodp = Kx(Zyf) 
  
  # Now, I would like to have the squarefree factorization of fmodp
  # I go for the f/gcd(f,f')
 
  divs, gcdfderf = _gcd_with_failure(fmodp, derivative(fmodp))
  
  if !isone(divs)
    return gcd(lift(divs), p), false, O
  end
  
  sqff=divexact(fmodp,gcdfderf)
  

  # first build 1/p ( f - g*h)
  gZ = lift(Zy,sqff)
  hZ = lift(Zy,gcdfderf)

  g1 = Zyf - gZ*hZ

  for i in 0:degree(g1)
    q,r = divrem(coeff(g1,i),p)
    @assert r == 0
    setcoeff!(g1,i,q)
  end
  
  g1modp = Kx(g1)

  pmaximal = true

  divs, par1= _gcd_with_failure(gcdfderf, sqff) 
  if !isone(divs)
    return gcd(lift(divs), p), false, O
  end
  divs, U = _gcd_with_failure(par1, g1modp)  
  if !isone(divs)
    return gcd(lift(divs), p), false, O
  end
  pmaximal = (isone(U)) 

  if pmaximal
    return fmpz(1), true, O
  end

  U = divexact(fmodp, U)
  alpha = nf(O)(parent(f)(lift(Zy,U)))

  n=_hnf_modular_eldiv(vcat(representation_mat(alpha), MatrixSpace(FlintZZ, degree(O), degree(O), false)(p)), p, :lowerleft)
  b = FakeFmpqMat(sub(n, degree(O)+1:2*degree(O), 1:degree(O)),p)

  OO = Order(nf(O), b)
  OO.isequation_order = false

  OO.disc = divexact(O.disc, p^(2*(degree(O)-degree(U))))

  return fmpz(1), false, OO
end


function _gcd_with_failure(a::fmpz_mod_poly, b::fmpz_mod_poly)
  Rx=parent(a)
  R=Rx.base_ring
  f=deepcopy(a)
  g=deepcopy(b)
  while true
    if degree(f)<degree(g)
      f, g = g, f
    end
    
    if !isunit(lead(g))
      return lead(g), g
    end
    
    f=rem(f,g)
    
    if degree(f)<1
      if iszero(f)
        return R(1), g
      end
      if isunit(coeff(f,0))
        return R(1), Rx(1)
      end
      return coeff(f,0), g
    end
  end

end
