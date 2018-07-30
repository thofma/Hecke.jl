@testset "Poly" begin

  function _test_sturm()
    s = rand(1:20)
    Zx, x = FlintZZ["x"]
    M = random_symmetric_matrix(s)
    f = charpoly(Zx, M)
    while !issquarefree(f) && iszero(coeff(f, 0))
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
        R=AcbField(p, false)
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
