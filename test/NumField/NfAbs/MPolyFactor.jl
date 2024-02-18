@testset "Misc/MPolyFactor" begin

  check_fac(esum, a) = check_fac(esum, esum, a)

  function check_fac(low, hi, a)
      f = factor(a)
      g = f.unit
      esum = 0
      for i in f.fac
          g *= i[1]^i[2]
          esum += i[2]
      end
      @test g == a
      @test low <= esum <= hi
  end

  QA, A = polynomial_ring(Hecke.QQ, "A")
  K, a = number_field(A^3 - 2, "a")
  Kxyz, (x, y, z, t) = polynomial_ring(K, ["x", "y", "z", "t"])

  check_fac(0, Kxyz(0))
  check_fac(0, Kxyz(1))
  check_fac(0, Kxyz(2))
  check_fac(6, 2*x^2*y*(1+y)*(x^3-2))
  check_fac(9, 2*x^2*y*(1+y)*(2*x^3-1)*(a*x+a^2*y+1)*(a^2*x+a*y+1)^2)
  check_fac(2, x^6-2*y^3)
  check_fac(2, (3*a*y*z*x^2+z-a)*(7*x+a*z^3*y))
  check_fac(3, (x+y+a)*(x+a*y+1)*(x+y+2*a))
  check_fac(3, (x^2+y^2+a)*(x^3+a*y^3+1)*(x^2+y+2*a))
  check_fac(8, (1+x+a*y+x*y)^3*(1+x+a^2*y+x*y^2)^5)
  check_fac(4, (x-(a+1)^4*y+z)*(a*x+y+z)*(x+a*y+z)*(x+y+a*z))
  check_fac(4, (1+x+y+x^2*(1+z+a*y)+y^2*(z+a*x^2))*
               (a*x+y+z*y)*(1+x+a*y*z+z)*(a+x*y+y+a*z))
  check_fac(2, x^99-2*y^99*z^33)
  check_fac(4, x^66-y^66*z^33)

  function dodd(n::Int)
    count = 0
    for i in 1:2:n
      if n%i == 0
        count += 1
      end
    end
    return count
  end
  for i in 1:10
    check_fac(1 + dodd(i) + Int(i%3 == 0), ((1+x+y+z+t)^i+1)*((1+x+y+z+t)^i+2))
  end

  QA, A = polynomial_ring(Hecke.QQ, "A")
  K,e3 = number_field(A^2+A+1, "e3")
  R,(a,x,y,z,t,u,v,w) = polynomial_ring(K, ["a", "x", "y", "z", "t", "u", "v", "w"])
  check_fac(24,
    3*(x+y)*(x-y)*(x-e3*y)*(x+e3*y)*(x+(-e3-1)*y)*(x+(e3+1)*y)*
    (a^2*y*z^2+e3*x*t*u*v*w)*(a^2*y*u^2+e3*x*z*t*v*w)*(a^2*y*t^2-e3*x*z*u*v*w)*
    (a^2*y*t^2+e3*x*z*u*v*w)*(a^2*y*z^2-e3*x*t*u*v*w)*(a^2*y*u^2-e3*x*z*t*v*w)*
    (a*x*z*t*v+(e3+1)*y*u^2*w^2)*(a*x*t*u*v+(e3+1)*y*z^2*w^2)*
    (a*x*z*t*v+(-e3-1)*y*u^2*w^2)*(a*x*z*u*w+(-e3-1)*y*t^2*v^2)*
    (a*x*z*u*w+(e3+1)*y*t^2*v^2)*(a*x*z*t*w+(e3+1)*y*u^2*v^2)*
    (a*x*z*t*w+(-e3-1)*y*u^2*v^2)*(a*x*z*u*v+(-e3-1)*y*t^2*w^2)*
    (a*x*t*u*w+(e3+1)*y*z^2*v^2)*(a*x*z*u*v+(e3+1)*y*t^2*w^2)*
    (a*x*t*u*v+(-e3-1)*y*z^2*w^2)*(a*x*t*u*w+(-e3-1)*y*z^2*v^2))

   QQxy, (x, y) = QQ["x", "y"]
   f = (x^3+5*y^3)*(x^2+2*y^2)
   # not a real test, just check that it does not crash
   @test length(factor_absolute(f)) == 3

   # non-integral defining equation
   Qx, x = QQ["x"]
   K, a = number_field(x^2 - 1//3*x + 1);
   R, (u, v) = polynomial_ring(K, ["u", "v"])
   f = (u + a)*(v^2 + a)
   fa = factor(f)
   @test unit(fa) * prod(g^e for (g, e) in fa) == f

end
