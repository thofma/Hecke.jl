@testset "Misc/MPolyFactor" begin

  function check_factorization(num::Integer, a)
    f = factor(a)
    g = f.unit
    for i in f.fac
      num -= i[2]
      g *= i[1]^i[2]
    end
    @test num <= 0
    @test g == a
  end

  R, (x, y, z) = PolynomialRing(Hecke.QQ, ["x", "y", "z"])
  check_factorization(6, x^24-y^24*z^12)

  R, (x, y, z) = PolynomialRing(Hecke.QQ, ["x", "y", "z"])
  check_factorization(2, ((x^2+y^2+z^2+2)*(x+1)*(y+2)*(z+3)+x*y*z)*(x^2+y^2+z^2+3))

  R, (x, y, z, t) = PolynomialRing(Hecke.QQ, ["x", "y", "z", "t"])
  for n in 1:8
    count = 0
    for i in 1:2:n
        if n%i == 0
            count += 1
        end
    end
    check_factorization(count, ((1+x+y+z+t)^n+1)*((1+x+y+z+t)^n+2))
  end

  R, (x, y, z, u, v) = PolynomialRing(Hecke.QQ, ["x", "y", "z", "u", "v"])
  check_factorization(2, (y^2*v*(z+v)*x+v+y)*(v^2*(y+z)*x+z^2))

  QA, A = PolynomialRing(Hecke.QQ, "A")
  K, a = number_field(A^3 - 2, "a")
  R, (x, y, z) = PolynomialRing(K, ["x", "y", "z"])
  check_factorization(0, R(0))
  check_factorization(0, R(1))
  check_factorization(0, R(2))
  check_factorization(6, 2*x^2*y*(1+y)*(x^3-2))
  check_factorization(7, 2*x^2*y*(1+y)*(2*x^3-1)*(a*x+a^2*y+1)*(a^2*x+a*y+1)^2)
  check_factorization(2, x^6-2*y^3)
  check_factorization(2, (y*z*x^2+z-1)*(x+a*z^3*y))
  check_factorization(3, (x+y+a)*(x+a*y+1)*(x+y+2*a))
  check_factorization(3, (x^2+y^2+a)*(x^3+a*y^3+1)*(x^2+y+2*a))
  check_factorization(8, (1+x+a*y+x*y)^3*(1+x+a^2*y+x*y^2)^5)
  check_factorization(4, (x-(a+1)^4*y+z)*(a*x+y+z)*(x+a*y+z)*(x+y+a*z))
  
end

