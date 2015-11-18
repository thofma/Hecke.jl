

## given some r/s = a mod b and deg(r) = n, deg(s) <= m find r,s
## a and b better be polynomials in the same poly ring.
## seems to work for Q (Qx) and Fp experimentally
#
# possibly should be rewritten to use an asymptotically (and practically)
# faster algorithm. For Q possibly using CRT and fast Fp techniques
# Algorithm copies from the bad-primes paper

function rational_reconstruction{P}(a::P, b::P, n::Int, m::Int)
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

function rational_reconstruction{P}(a::P, b::P)
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
  Qx,x = PolynomialRing(parent(a[1]), "x")
  f = Qx(a)
  xn= x^length(a)

  fl, n, d = rational_reconstruction(f, xn)
  if fl
    return true, d*(1//d(0))
  else
    return false, Qx(0)
  end
end

