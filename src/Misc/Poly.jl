
export rational_reconstruction, farey_lift, div, valence, leading_coefficient,
       trailing_coefficient, constant_coefficient

function PolynomialRing(R::Ring)
  return PolynomialRing(R, "_x")
end

function FiniteField(p::Integer)
  return ResidueRing(ZZ, p)
end

function FiniteField(p::fmpz)
  return ResidueRing(ZZ, p)
end

function fmpz(a::Residue{Nemo.fmpz})
  return a.data
end

function lift(R::FlintIntegerRing, a::Residue{Nemo.fmpz})
  return a.data
end

function Base.call(R::FlintIntegerRing, a::Residue{Nemo.fmpz})
  return a.data
end

## given some r/s = a mod b and deg(r) = n, deg(s) <= m find r,s
## a and b better be polynomials in the same poly ring.
## seems to work for Q (Qx) and Fp experimentally
#
# possibly should be rewritten to use an asymptotically (and practically)
# faster algorithm. For Q possibly using CRT and fast Fp techniques
# Algorithm copies from the bad-primes paper

function rational_reconstruction{S}(a::PolyElem{S}, b::PolyElem{S}, n::Int, m::Int)
  R = a.parent
  if degree(a) <= n return true, a, R(1); end

  M = MatrixSpace(R, 2, 2)()
  M[1,1] = b
  M[2,1] = a
  M[2,2] = R(1)

  T = MatrixSpace(R, 2, 2)()
  T[1,2] = R(1)
  T[2,1] = R(1)
  while degree(M[2,1]) > n
    q, r = divrem(M[1,1], M[2,1])
    T[2,2] = -q
    M = T*M
  end
  if degree(M[2,2]) <= m 
    return true, M[2,1], M[2,2]
  end

  return false, M[2,1], M[2,2]
end

function rational_reconstruction{T}(a::PolyElem{T}, b::PolyElem{T})
  return rational_reconstruction(a, b, div(degree(b), 2), div(degree(b), 2))
end

# to appease the Singular crowd...
farey_lift = rational_reconstruction


# in at least 2 examples produces the same result as Magma
# can do experiments to see if dedicated Berlekamp Massey would be
# faster as well as experiments if Berlekamp Massey yields faster 
# rational_reconstruction as well.
# Idea of using the same agorithm due to E. Thome
#

function berlekamp_massey{T}(a::Array{T, 1})
  Rx,x = PolynomialRing(parent(a[1]))
  f = Rx(a)
  xn= x^length(a)

  fl, n, d = rational_reconstruction(f, xn)
  if fl
    return true, d*(inv(trailing_coefficient(d)))
  else
    return false, Rx(0)
  end
end


function div(f::PolyElem, g::PolyElem)
  q,r = divrem(f,g)
  return q
end

# probably better off in c and faster
function valence(f::PolyElem)
  c = f(0)
  while c==0 && degree(f)>0
    f = div(f, gen(parent(f)))
    c = f(0)
  end
  return c
end

function leading_coefficient(f::PolyElem)
  return coeff(f, degree(f))
end

function trailing_coefficient(f::PolyElem)
  return coeff(f, 0)
end

constant_coefficient = trailing_coefficient

################################################################################
#
#  Functions for nmod_poly
#
################################################################################

#CF: div is neccessary for general Euc operations!
div(x::nmod_poly, y::nmod_poly) = divexact(x,y)

################################################################################
#
# Valuation
#
################################################################################
#CF TODO: use squaring for fast large valuation
#         use divrem to combine steps

function valuation(z::nmod_poly, p::nmod_poly)
  check_parent(z, p)
  z == 0 && error("Not yet implemented")
  v = 0
  while mod(z, p) == 0
    z = div(z, p)
    v += 1
  end
  return v, z
end 

function resultant(f::fmpz_poly, g::fmpz_poly, d::fmpz, nb::Int)
  z = fmpz()
  ccall((:fmpz_poly_resultant_modular_div, :libflint), Void, 
     (Ptr{fmpz}, Ptr{fmpz_poly}, Ptr{fmpz_poly}, Ptr{fmpz}, Int), 
     &z, &f, &g, &d, nb)
  return z
end

################################################################################
#
#  Replace coeff function
#
################################################################################

function coeff(x::nmod_poly, n::Int)
  (n < 0 || n > degree(x)) && return base_ring(x)(0)
  return base_ring(x)(ccall((:nmod_poly_get_coeff_ui, :libflint), UInt,
          (Ptr{nmod_poly}, Int), &x, n))
end
