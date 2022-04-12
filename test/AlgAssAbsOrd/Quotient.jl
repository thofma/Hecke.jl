@testset "Quotient orders" begin
  G = small_group(8, 4)
  QG = QQ[G]
  ZG = Order(QG, basis(QG); cached = false)
  N, NtoG = subgroups(G, order = 2)[1]
  I = sum([QG(NtoG(n)) for n in N]) * ZG
  OO, h = Hecke.quotient_order(ZG, I)

  for i in 1:10
    for j in 1:10
      for k in 1:10
        a = rand(QG, -10:10)
        b = rand(QG, -10:10)
        c = rand(QG, -10:10)
        @test a * (b + c) == a * b + a * c
        @test (a + b) * c == a * c + b * c
      end
    end
  end

  @test OO == Order(algebra(OO), [h(elem_in_algebra(b)) for b in basis(ZG)])
end
