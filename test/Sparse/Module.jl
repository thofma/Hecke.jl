@testset "ModuleCtx_fmpz" begin
  # the elementary divisors different from 1 of the row span
  function essential_elementary_divisors(rows)
    M = Hecke.ModuleCtx_fmpz(length(rows[1]))
    for r in rows
      Hecke.add_gen!(M, sparse_row(ZZ, [(j, ZZ(r[j])) for j in eachindex(r) if r[j] != 0]))
    end
    return elementary_divisors(M)
  end

  @test essential_elementary_divisors([[1, 0, 0], [0, 1, 0], [0, 0, 1]]) == ZZRingElem[]
  @test essential_elementary_divisors([[2, 0, 0], [0, 4, 0], [0, 0, 8]]) == [2, 4, 8]
  @test essential_elementary_divisors([[2, 1, 0], [0, 3, 1], [0, 0, 5], [1, 1, 1]]) == [5]
  @test essential_elementary_divisors([[2, 0, 0], [0, 6, 0], [0, 0, 12], [1, 1, 1]]) == [2, 6]

  # not of full rank
  @test essential_elementary_divisors([[2, 0, 0], [0, 6, 0]]) == ZZRingElem[]
end
