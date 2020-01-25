@testset "Eisenstein extension" begin

    Qp = PadicField(7,10)
    R, x = PolynomialRing(Qp,"x")
    K,θ = Hecke.EisensteinField(x^6-7, "θ")

    f = x^5 - 7*x + 4
    fK = change_base_ring(K,f)

    Ql = QadicField(17,3,10)
    S, y = PolynomialRing(Ql, "y")
    L,a = Hecke.EisensteinField(y^3-17*y^2+17*y-17, "a")

    g = change_base_ring(L, L.pol)
    Y = change_base_ring(L, y)

    @testset "Basic arithmetic" begin
        @test fK - 4 == change_base_ring(K, x^5 - 7*x)
        @test 2*θ == θ + θ
    end

    @testset "Root finding" begin
        rts1 = roots(fK)
        correct = fmpz(5) + 138118274 + O(Qp,7^10)
        # + O(7^10)

        @test length(rts1) == 1 && K(correct) == rts1[1][1]

        rts2 = roots(x^6 - 7, K)

        correct = [
            (2 + 4*7^1 + 6*7^2 + 3*7^3 + 2*7^5 + 6*7^6 + 2*7^7 + 4*7^8 + O(Qp,7^9))*θ
            (3 + 4*7^1 + 6*7^2 + 3*7^3 + 2*7^5 + 6*7^6 + 2*7^7 + 4*7^8 + O(Qp,7^9))*θ        
            (5 + 2*7^1 + 3*7^3 + 6*7^4 + 4*7^5 + 4*7^7 + 2*7^8 + O(Qp,7^9))*θ                
            θ                                                                             
            (4 + 2*7^1 + 3*7^3 + 6*7^4 + 4*7^5 + 4*7^7 + 2*7^8 + O(Qp,7^9))*θ                
            (6 + 6*7^1 + 6*7^2 + 6*7^3 + 6*7^4 + 6*7^5 + 6*7^6 + 6*7^7 + 6*7^8 + O(Qp,7^9))*θ
        ]

        @test [r[1] for r in rts2] == correct
    end

    @testset "Valuation normalizations" begin
        @test valuation(zero(K)) == precision(K)

        @test precision(gen(K)) == 10
    end
end
   

