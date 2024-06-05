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

function dedekind_test(O::AbsSimpleNumFieldOrder, p::ZZRingElem, ::Val{compute_order} = Val(true)) where compute_order
  !is_equation_order(O) && error("Order must be an equation order")

  if rem(discriminant(O), p^2) != 0
    if compute_order
      return true, O
    else
      return true
    end
  end

  Zy, y = polynomial_ring(FlintZZ, "y")
  Kx, x = polynomial_ring(GF(p, cached=false), "x", cached=false)

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
  U = gcd(gcd(g, h), g1modp)

  if !compute_order
    if isone(U)
      return true
    else
      return false
    end
  else

    pmaximal = (isone(U))

    if pmaximal
      return true, O
    end

    @hassert :AbsNumFieldOrder 1 rem(fmodp, U) == zero(Kx)
    U = divexact(fmodp, U)

    @hassert :AbsNumFieldOrder 1 rem(O.disc, p^2) == 0

    alpha = nf(O)(parent(f)(lift(Zy,U)))

    # build the new basis matrix
    # we have to take the representation matrix of alpha!
    # concatenating the coefficient vector won't help
    Malpha, d = representation_matrix_q(alpha)
    @assert isone(d)
    n = _hnf_modular_eldiv(Malpha, p, :lowerleft)
    b = FakeFmpqMat(n, p)
    @hassert :AbsNumFieldOrder 1 defines_order(nf(O), b)[1]
    OO = Order(nf(O), b, check = false)

    OO.is_equation_order = false

    OO.disc = divexact(O.disc, p^(2*(degree(O)-degree(U))))

    return false, OO
  end
end



dedekind_test(O::AbsSimpleNumFieldOrder, p::Integer) = dedekind_test(O, FlintZZ(p))

dedekind_ispmaximal(O::AbsSimpleNumFieldOrder, p::ZZRingElem) = dedekind_test(O, p, Val(false))

dedekind_ispmaximal(O::AbsSimpleNumFieldOrder, p::Integer) = dedekind_ispmaximal(O, FlintZZ(p))

dedekind_poverorder(O::AbsSimpleNumFieldOrder, p::ZZRingElem) = dedekind_test(O, p)[2]

dedekind_poverorder(O::AbsSimpleNumFieldOrder, p::Integer) = dedekind_poverorder(O, FlintZZ(p))


###############################################################################
#
#  Non-prime case
#
###############################################################################

function dedekind_test_composite(O::AbsSimpleNumFieldOrder, p::ZZRingElem)
  @assert is_equation_order(O)

  Zy = polynomial_ring(FlintZZ, "y")[1]
  R = residue_ring(FlintZZ, p, cached = false)[1]
  Rx = polynomial_ring(R, "x", cached=false)[1]

  f = Zy(nf(O).pol)

  fmodp = Rx(f)

  # Now, I would like to have the squarefree factorization of fmodp
  # I go for the f/gcd(f,f')

  divs, gcdfderf = _gcd_with_failure(fmodp, derivative(fmodp))

  if !isone(divs)
    return gcd(divs, p), O
  end

  sqff = divexact(fmodp, gcdfderf)


  # first build 1/p ( f - g*h)
  gZ = lift(Zy,sqff)
  hZ = lift(Zy,gcdfderf)

  g1 = f - gZ*hZ
  g1 = divexact(g1, p)

  g1modp = Rx(g1)

  divs, par1 = _gcd_with_failure(gcdfderf, sqff)
  if !isone(divs)
    return gcd(divs, p), O
  end
  divs, U = _gcd_with_failure(par1, g1modp)
  if !isone(divs)
    return gcd(divs, p), O
  end

  if isone(U)
    return ZZRingElem(1), O
  end

  U = divexact(fmodp, U)
  alpha = nf(O)(parent(f)(lift(Zy,U)))

  Malpha, d = representation_matrix_q(alpha)
  hnf_modular_eldiv!(Malpha, p, :lowerleft)
  b = FakeFmpqMat(Malpha, p)

  @hassert :AbsNumFieldOrder 1 defines_order(nf(O), b)[1]
  OO = AbsSimpleNumFieldOrder(nf(O), b)
  temp = divexact(b.den^degree(O), prod_diagonal(b.num))
  fl, qq = divides(discriminant(O), temp^2)
  @assert fl
  OO.disc = qq
  @hassert :AbsNumFieldOrder 1 discriminant(basis(OO)) == OO.disc
  OO.index = temp

  return ZZRingElem(1), OO
end
