@testset "to_magma" begin
  R, _ = polynomial_ring(QQ, [:a, :b])
  mktemp() do path, io
    close(io)
    Hecke.to_magma(path, R)
    @test read(path, String) == "R<a,b> := PolynomialRing(S, 2);\n"
    Hecke.to_magma(path, R; name = "T", mode = "a")
    @test read(path, String) == "R<a,b> := PolynomialRing(S, 2);\nT<a,b> := PolynomialRing(S, 2);\n"
  end
end
