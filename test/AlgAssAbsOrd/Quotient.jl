@testset "Quotient orders" begin
  G = small_group(8, 4)
  QG = QQ[G]
  ZG = order(QG, basis(QG); cached = false)
  N, NtoG = subgroups(G, order = 2)[1]
  I = sum([QG(NtoG(n)) for n in N]) * ZG
  OO, h = Hecke.quotient_order(ZG, I)

  for i in 1:10
    for j in 1:10
      a = rand(QG, -10:10)
      b = rand(QG, -10:10)
      @test h(a * b) == h(a) * h(b)
      @test h(a) + h(b) == h(a) + h(b)

      a = rand(algebra(OO), -10:10)
      b = rand(algebra(OO), -10:10)
      @test h(h\(a * b)) == a * b
      @test h(h\(a + b)) == a + b
    end
  end

  @test OO == order(algebra(OO), [h(elem_in_algebra(b)) for b in basis(ZG)])
end
