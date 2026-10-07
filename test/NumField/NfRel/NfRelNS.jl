@testset "NumField/NfRel/NfResNS.jl" begin
    R, x = universal_polynomial_ring(ZZ, 5; cached = false)

    # Simple shared root in first variable
    @test resultant((x[1] - 1)^2, x[1] - 1, x[1]) == 0

    # Coprime in second variable
    @test resultant(x[2]^2 + 1, x[2] + 2, x[2]) != 0

    # Mixed variables
    f = x[1] + x[2]
    g = x[1]^2 + x[2]
    @test resultant(f, g, x[1])  == x[2]^2 + x[2]

    # Variable not from parent ring
    S, y = universal_polynomial_ring(ZZ, 5; cached = false)
    @test_throws ErrorException resultant(x[1] + 1, x[1] + 2, y[1])

    # Symbol is not a generator
    @test_throws ArgumentError resultant(x[1] + 1, x[1] + 2, x[1] + 1)

    # Result type should be in same ring
    r = resultant(x[1]^2 - 1, x[1] - 1, x[1])
    @test parent(r) === R
    @test isa(r, UniversalPolyRingElem)

    # Generic multivariate polynomials from different rings
    K, t = polynomial_ring(QQ, :t)
    P, (a, b) = polynomial_ring(K, [:a, :b]; cached = false)
    Q, (c, d) = polynomial_ring(K, [:a, :b]; cached = false)
    @test resultant(a + b, a^2 + b, 1) == b^2 + b
    @test_throws ErrorException resultant(a + b, c^2 + d, 1)
end
