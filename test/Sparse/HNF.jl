@testset "Hermite normal form" begin
  for i in 1:10
    r = 20
    c = 10
    A = matrix(ZZ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    As = sparse_matrix(A)
    @test hnf(A) == ZZMatrix(hnf(As))

    H, T = Hecke.hnf_kannan_bachem(As, Val(true))
    B = deepcopy(As)

    for t in T
      Hecke.apply_left!(B, t)
    end

    @test ZZMatrix(B) == hnf(A)
  end

  p = 23
  m = matrix(ZZ, 30, 20, [powermod(i, j, p) for i=1:30 for j=1:20])
  hm = hnf(m)
  sm = sparse_matrix(m)
  @test hm == matrix(hnf(sm))
  @test hm == matrix(hnf(sm; auto = true))
  h = hnf(hcat(sm, identity_matrix(SMat, ZZ, 30)); limit = 20, auto = true)
  @test matrix(sub(h, 1:30, 1:20)) == hm
  @test abs(det(sub(h, 1:30, 21:50))) == 1

  @test elementary_divisors(hm) == elementary_divisors(sm)
end



