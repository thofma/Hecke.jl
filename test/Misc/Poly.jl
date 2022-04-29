@testset "Poly" begin

  function _test_sturm()
    s = rand(1:20)
    Zx, x = FlintZZ["x"]
    M = random_symmetric_matrix(s)
    f = charpoly(Zx, M)
    while !issquarefree(f) || iszero(coeff(f, 0))
      M = random_symmetric_matrix(s)
      f = charpoly(Zx, M)
    end
    npos = Hecke.number_positive_roots(f)
    ff=factor(f)
    sgtpos=0
    sgtneg=0
    for (h,v) in ff.fac
      if degree(h)==1
        if coeff(h,0)>0
          sgtneg+=v
        else
          sgtpos+=v
        end
        continue
      end
      p=64
      while p<4096
        sgtposf=0
        sgtnegf=0
        R=AcbField(p, cached = false)
        Rx=AcbPolyRing(R, Symbol("x"), false)
        g=Rx(h)
        l=roots(g)
        for i=1:length(l)
          y=real(l[i])
          if ispositive(y)
            sgtposf+=1
          end
          if isnegative(y)
            sgtnegf+=1
          end
        end
        if sgtposf+sgtnegf==degree(h)
          sgtpos+=sgtposf*v
          sgtneg+=sgtnegf*v
          break
        else
          p*=2
        end
      end
      if p > 4096
        error("Precision issue")
      end
    end
    return sgtpos == npos
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
  @test roots(f) == [K(-1), K(-1)]

  K, a = NumberField(x^2-5, "a")
  R, x = PolynomialRing(K)
  f = 3*x^4 + 5*x^3 - 15*x^2 + 15*x
  @test roots(f) == [K(0)]

  K, a = NumberField(x^4+2, "a") #relative
  R, y = PolynomialRing(K,"y") 
  f = y^2 + 2*y + 1
  @test roots(f) == [K(-1), K(-1)]

end

