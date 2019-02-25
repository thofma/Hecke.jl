@testset "Hilbert symbols" begin
  v = [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, 1, 1,
       -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, 1,
       -1, -1, -1, -1, 1, 1, -1, 1, 1, -1, -1, 1, 1, 1, -1, 1, -1, -1, 1, 1 ]

  for i in 1:8
    for j in 1:8
      @test hilbert_symbol(i, j, 2) == v[(i - 1) * 8 + j]
      @test hilbert_symbol(fmpz(i), fmpz(j), 2) == v[(i - 1) * 8 + j]
      @test hilbert_symbol(fmpz(i), fmpz(j), fmpz(2)) == v[(i - 1) * 8 + j]
      @test hilbert_symbol(fmpq(i), fmpq(j), 2) == v[(i - 1) * 8 + j]
      @test hilbert_symbol(fmpq(i), fmpq(j), fmpz(2)) == v[(i - 1) * 8 + j]
    end
  end

  for p in PrimesSet(3, 100)
    for a in 1:100
      for b in 1:00
        h = hilbert_symbol(a, b, p)
        a = fmpz(a)
        b = fmpz(b)
        r = (-1)^(valuation(a, p) * valuation(b, p)) * a^(valuation(b, p)) * b^(valuation(a, p))
        @test h == jacobi(r, fmpz(p))
      end
    end
  end

  Qx, x = PolynomialRing(FlintQQ, "x")
  K, b = NumberField(x^3-3*x-1, "a")
  OK = maximal_order(K)
  for P in prime_ideals_up_to(OK, 200)
    @test hilbert_symbol(b, -3, P) == 1
  end
end
