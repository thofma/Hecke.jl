@testset "Poly" begin

  function _test_sturm()
    s = rand(1:20)
    Zx = Hecke.Globals.Zx
    M = random_symmetric_matrix(s)
    f = charpoly(Zx, M)

    while iszero(f)
      M = random_symmetric_matrix(s)
      f = charpoly(Zx, M)
    end

    npos = Hecke.n_positive_roots(f)
    nreal = Hecke.n_real_roots(f)

    p = 64

    local sgtpos
    local l

    while p < 4096
      l = roots(f, ArbField(p, cached = false))
      sgtpos = count(ispositive, l)
      sgtneg = count(isnegative, l)
      sgtz = count(iszero, l)
      if sgtpos + sgtneg + sgtz != length(l)
        p *= 2
      else
        break
      end
      if p > 4096
        error("Precision issue")
      end
    end
    return sgtpos == npos && nreal == length(l) 
  end

  function random_symmetric_matrix(x::Int)
    M = zero_matrix(FlintZZ, x, x)
    for i = 1:x
      for j= i:x
        a = rand(1:5)
        M[i, j] = a
        M[j, i] = a
      end
    end
    return M
  end

  for i = 1:20
    @test _test_sturm()
  end

  for R in [ZZ, QQ]
    _, x = R["x"]
    f = x^5 + x^2 - x

    @test Hecke.n_real_roots(f) == 3
    @test Hecke.n_real_roots(f^2) == 3
    @test Hecke.n_positive_roots(f) == 1
    @test Hecke.n_positive_roots(f * x^3) == 1

    f = x^10 + x^9 - x^8 + x^7 - x^6 + x^5 - x^4 - x^3 - x
    @test Hecke.n_real_roots(f) == 4
    @test Hecke.n_real_roots(f^2) == 4
    @test Hecke.n_positive_roots(f) == 1
    @test Hecke.n_positive_roots(f^2 * x^3) == 1

    @test Hecke.n_positive_roots((x - 1)^2) == 1
    @test Hecke.n_positive_roots((x - 1)^2, multiplicities = true) == 2
  end
end

@testset "roots" begin
  o = CyclotomicField(2)[1](1)
  @test issetequal(roots(o, 2), [o, -o])  
  o = CyclotomicField(1)[1](1)
  @test issetequal(roots(o, 2), [o, -o])

  o, a = CyclotomicField(4)
  _, x = o["x"]
  @test length(roots(x^2-a^2//4)) == 2

  Qx,x = PolynomialRing(QQ,"x")                                                   
  K, a = NumberField(x^4+2, "a")
  R, y = PolynomialRing(K,"y") 
  f = y^2 + 2*y + 1
  @test roots(f) == [K(-1)]

  K, a = NumberField(x^2-5, "a")
  R, x = PolynomialRing(K)
  f = 3*x^4 + 5*x^3 - 15*x^2 + 15*x
  @test roots(f) == [K(0)]

  K, a = NumberField(x^4+2, "a") #relative
  R, y = PolynomialRing(K,"y") 
  f = y^2 + 2*y + 1
  @test roots(f) == [K(-1)]

end

