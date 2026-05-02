using Hecke.RiemannSurfaces

function _endomorphism_structure_case(f, F, v)
  RS = RiemannSurface(f, v, 500, integration_method = "heuristic")
  P = big_period_matrix(RS)
  EndoRep = geometric_endomorphism_representation(P)
  return Hecke.RiemannSurfaces.endomorphism_structure(EndoRep; calc_pic = true)
end

@testset "EndomorphismStructure" begin
  R, t = polynomial_ring(QQ)

  @testset "Curves over x^2 - 5" begin
    F, r = number_field(t^2 - 5)
    S, (x, y) = polynomial_ring(F, [:x, :y])
    v = infinite_places(F)[2]

    @testset "y^2 = x^6 + r" begin
      f = x^6 + r - y^2
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc

      @test EndoDescRR == [(2, 2)]
      @test length(EndoDescQQ) == 1
      @test EndoDescQQ[1].m == 2
      @test EndoDescQQ[1].dimalg == 2
      @test degree(EndoDescQQ[1].center) == 2
      @test EndoDescQQ[1].disc == 1
      @test EndoDescQQ[1].dimfac == 1
      @test EndoDescZZ.index == 16
      @test EndoDescZZ.eichler == -1
      @test is_isomorphic(
        EndoDescQQ[1].center,
        number_field(t^2 - t + 1)[1],
      )
      @test pic == 4
    end

    @testset "y^2 = x^5 + x + 1" begin
      f = x^5 + x + 1 - y^2
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc

      @test EndoDescRR == [(1, 1)]
      @test length(EndoDescQQ) == 1
      @test EndoDescQQ[1].m == 1
      @test EndoDescQQ[1].dimalg == 1
      @test degree(EndoDescQQ[1].center) == 1
      @test EndoDescQQ[1].disc == 1
      @test EndoDescQQ[1].dimfac == 2
      @test EndoDescZZ.index == 1
      @test EndoDescZZ.eichler == -1
      @test is_isomorphic(EndoDescQQ[1].center, number_field(t - 1)[1])
      @test pic == 1
    end

    @testset "y^2 = x^5 + r*x^3 + x" begin
      f = x^5 + r*x^3 + x - y^2
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc

      @test EndoDescRR == [(2, 2)]
      @test length(EndoDescQQ) == 1
      @test EndoDescQQ[1].m == 2
      @test EndoDescQQ[1].dimalg == 2
      @test degree(EndoDescQQ[1].center) == 2
      @test EndoDescQQ[1].disc == 1
      @test EndoDescQQ[1].dimfac == 1
      @test EndoDescZZ.index == 1
      @test EndoDescZZ.eichler == -1
      @test is_isomorphic(EndoDescQQ[1].center, number_field(t^2 + 5)[1])
      @test pic == 4
    end
  end

  @testset "Curves over x^2 - x + 1" begin
    F, r = number_field(t^2 - t + 1)
    S, (x, y) = polynomial_ring(F, [:x, :y])
    v = infinite_places(F)[1]

    @testset "y^2 = x^6 + r" begin
      f = x^6 + r - y^2
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc

      @test EndoDescRR == [(2, 2)]
      @test length(EndoDescQQ) == 1
      @test EndoDescQQ[1].m == 2
      @test EndoDescQQ[1].dimalg == 2
      @test degree(EndoDescQQ[1].center) == 2
      @test EndoDescQQ[1].disc == 1
      @test EndoDescQQ[1].dimfac == 1
      @test EndoDescZZ.index == 16
      @test EndoDescZZ.eichler == -1
      @test is_isomorphic(
        EndoDescQQ[1].center,
        number_field(t^2 - t + 1)[1],
      )
      @test pic == 4
    end

    @testset "y^2 = (-22*r + 62)*x^6 + ..." begin
      f = (-22*r + 62)*x^6 + (156*r - 312)*x^5 + (-90*r + 126)*x^4 +
          (-1456*r + 1040)*x^3 + (-66*r + 186)*x^2 + (-156*r + 312)*x +
          -30*r + 42 - y^2
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc

      @test EndoDescRR == [(2, 1)]
      @test length(EndoDescQQ) == 1
      @test EndoDescQQ[1].m == 1
      @test EndoDescQQ[1].dimalg == 4
      @test degree(EndoDescQQ[1].center) == 1
      @test EndoDescQQ[1].disc == 6
      @test EndoDescQQ[1].dimfac == 2
      @test EndoDescZZ.index == 1
      @test EndoDescZZ.eichler == 1
      @test is_isomorphic(EndoDescQQ[1].center, number_field(t - 1)[1])
      @test pic == 3
    end
  end

  @testset "Curves over QQ" begin
    F, r = rationals_as_number_field()
    S, (x, y) = polynomial_ring(F, [:x, :y])
    v = infinite_places(F)[1]

    @testset "y^2 = x^6 - 8*x^4 - 8*x^3 + 8*x^2 + 12*x - 8" begin
      f = x^6 - 8*x^4 - 8*x^3 + 8*x^2 + 12*x - 8 - y^2
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc

      @test EndoDescRR == [(1, 2), (1, 2)]
      @test length(EndoDescQQ) == 1
      @test EndoDescQQ[1].m == 1
      @test EndoDescQQ[1].dimalg == 4
      @test degree(EndoDescQQ[1].center) == 4
      @test EndoDescQQ[1].disc == 1
      @test EndoDescQQ[1].dimfac == 2
      @test EndoDescZZ.index == 1
      @test EndoDescZZ.eichler == -1
      @test is_isomorphic(
        EndoDescQQ[1].center,
        number_field(t^4 - t^3 + 2*t^2 + 4*t + 3)[1],
      )
      @test pic == 2
    end

    @testset "y^2 = x^7 + 56*x^6 + ... + 7235200" begin
      f = x^7 + 56*x^6 + 966*x^5 + 2184*x^4 - 77175*x^3 - 397152*x^2 +
          1400720*x + 7235200 - y^2
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc

      @test EndoDescRR == [(1, 1), (1, 1), (1, 1)]
      @test length(EndoDescQQ) == 2
      @test any(EndoDescQQ) do desc
        desc.m == 1 && desc.dimalg == 1 && degree(desc.center) == 1 &&
          desc.disc == 1 && desc.dimfac == 1 &&
          is_isomorphic(desc.center, number_field(t - 1)[1])
      end
      @test any(EndoDescQQ) do desc
        desc.m == 1 && desc.dimalg == 2 && degree(desc.center) == 2 &&
          desc.disc == 1 && desc.dimfac == 2 &&
          is_isomorphic(desc.center, number_field(t^2 - 3)[1])
      end
      @test EndoDescZZ.index == 3
      @test EndoDescZZ.eichler == -1
      @test pic == 3
    end

    @testset "y^2 = 10*x^10 + ... + 10" begin
      f = 10*x^10 + 24*x^9 + 23*x^8 + 48*x^7 + 35*x^6 + 35*x^4 - 48*x^3 +
          23*x^2 - 24*x + 10 - y^2
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc

      @test EndoDescRR == [(2, 1)]
      @test length(EndoDescQQ) == 1
      @test EndoDescQQ[1].m == 2
      @test EndoDescQQ[1].dimalg == 1
      @test degree(EndoDescQQ[1].center) == 1
      @test EndoDescQQ[1].disc == 1
      @test EndoDescQQ[1].dimfac == 2
      @test EndoDescZZ.index == 36
      @test EndoDescZZ.eichler == 0
      @test is_isomorphic(EndoDescQQ[1].center, number_field(t - 1)[1])
      @test pic == 3
    end

    @testset "x^4 - y^3*z + z^4" begin
      f = x^4 - y^3 + 1
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc
      @test EndoDescRR == [(1, 2), (2, 2)]
      @test length(EndoDescQQ) == 2
      @test any(EndoDescQQ) do desc
        desc.m == 1 && desc.dimalg == 2 && degree(desc.center) == 2 &&
          desc.disc == 1 && desc.dimfac == 1 &&
          is_isomorphic(desc.center, number_field(t^2 - t + 1)[1])
      end
      @test any(EndoDescQQ) do desc
        desc.m == 2 && desc.dimalg == 2 && degree(desc.center) == 2 &&
          desc.disc == 1 && desc.dimfac == 1 &&
          is_isomorphic(desc.center, number_field(t^2 + 1)[1])
      end
      @test EndoDescZZ.index == 16
      @test EndoDescZZ.eichler == -1
      @test pic == 5
    end

    @testset "x^3*z + 2*x^2*y^2 + x^2*y*z + 3*x^2*z^2 - 4*x*y^3 - x*y^2*z + 5*x*y*z^2 + x*z^3 + 2*y^4 + 6*y^3*z + 6*y^2*z^2 + 2*y*z^3" begin
      f = x^3*1 + 2*x^2*y^2 + x^2*y*1 + 3*x^2*1^2 - 4*x*y^3 - x*y^2*1 + 5*x*y*1^2 + x*1^3 + 2*y^4 + 6*y^3*1 + 6*y^2*1^2 + 2*y*1^3
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc
      @test EndoDescRR == [(1, 1), (1, 1)]
      @test length(EndoDescQQ) == 2
      @test any(EndoDescQQ) do desc
        desc.m == 1 && desc.dimalg == 1 && degree(desc.center) == 1 &&
          desc.disc == 1 && desc.dimfac == 1 &&
          is_isomorphic(desc.center, number_field(t - 1)[1])
      end
      @test any(EndoDescQQ) do desc
        desc.m == 1 && desc.dimalg == 1 && degree(desc.center) == 1 &&
          desc.disc == 1 && desc.dimfac == 2 &&
          is_isomorphic(desc.center, number_field(t - 1)[1])
      end
      @test EndoDescZZ.index == 5
      @test EndoDescZZ.eichler == -1
      @test pic == 2
    end

    @testset "x^4 + 3/2*x^3*y + 2*x^3*z + 3*x^2*y^2 + 2*x^2*y*z + 7/2*x^2*z^2 + 2*x*y^3 + 2*x*y^2*z + 7/2*x*y*z^2 + 2*x*z^3 + 3/2*y^4 + y^3*z + 3/2*y^2*z^2 + 5/2*y*z^3 + z^4" begin
      f = x^4 + 3//2*x^3*y + 2*x^3*1 + 3*x^2*y^2 + 2*x^2*y*1 + 7//2*x^2*1^2 + 2*x*y^3 + 2*x*y^2*1 + 7//2*x*y*1^2 + 2*x*1^3 + 3//2*y^4 + y^3*1 + 3//2*y^2*1^2 + 5//2*y*1^3 + 1^4
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc
      @test EndoDescRR == [(1, 1), (1, 1)]
      @test length(EndoDescQQ) == 2
      @test any(EndoDescQQ) do desc
        desc.m == 1 && desc.dimalg == 1 && degree(desc.center) == 1 &&
          desc.disc == 1 && desc.dimfac == 1 &&
          is_isomorphic(desc.center, number_field(t - 1)[1])
      end
      @test any(EndoDescQQ) do desc
        desc.m == 1 && desc.dimalg == 1 && degree(desc.center) == 1 &&
          desc.disc == 1 && desc.dimfac == 2 &&
          is_isomorphic(desc.center, number_field(t - 1)[1])
      end
      @test EndoDescZZ.index == 5
      @test EndoDescZZ.eichler == -1
      @test pic == 2
    end

    @testset "x^4 - x^3*y + 2*x^3*z + 2*x^2*y*z + 2*x^2*z^2 - 2*x*y^2*z + 4*x*y*z^2 - y^3*z + 3*y^2*z^2 + 2*y*z^3 + z^4" begin
      f = x^4 - x^3*y + 2*x^3*1 + 2*x^2*y*1 + 2*x^2*1^2 - 2*x*y^2*1 + 4*x*y*1^2 - y^3*1 +  3*y^2*1^2 + 2*y*1^3 + 1^4
      EndoAlg, EndoDesc = _endomorphism_structure_case(f, F, v)
      EndoDescRR, EndoDescQQ, EndoDescZZ, pic = EndoDesc
      @test EndoDescRR == [(1, 2), (1, 2), (1, 2)]
      @test length(EndoDescQQ) == 1
      @test any(EndoDescQQ) do desc
        desc.m == 1 && desc.dimalg == 6 && degree(desc.center) == 6 &&
          desc.disc == 1 && desc.dimfac == 3 &&
          is_isomorphic(desc.center, number_field(R([7, -5, -1, 8, 2, -1, 1]))[1])
      end
      @test EndoDescZZ.index == 1
      @test EndoDescZZ.eichler == -1
      @test pic == 3
    end
  end
end
