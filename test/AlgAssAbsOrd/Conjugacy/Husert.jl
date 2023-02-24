@testset "Husert" begin
  a = ZZRingElem[0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 87, -64, 15, -80, 0, 0,
           0, 0, 0, 49]
  b = ZZRingElem[135, -2036, 2457, -243, -22300, -45, 679, -819, 81, 7434, 1658,
           -6743, 23115, -2294, -189610, 14922, -42584, 200191, -19879,
           -1616804, 25, -350, 455, -45, -4081]

  A = matrix(ZZ, 5, 5, a)
  B = matrix(ZZ, 5, 5, b)
  fl, C = Hecke._issimilar_husert(A, B)
  @test fl
  @test C * A == B * C
end
