@testset "CM types" begin
  Qx, x = QQ["x"]
  K, a = number_field(x^4 + 8*x^2 + 4)
  cK = Hecke.complex_embeddings(K)
  @test length(cK) == 4
  E = cK[1]
  @test number_field(E) === K
  @test infinite_place(E) isa InfPlc
  @test overlaps(conj(E)(a), conj(E(a)))
  @test cK[1] == cK[1]
  @test cK[1] != cK[2]

  Ec = conj(E)
  fl, c = Hecke.is_cm_field(K)
  @test c * E == Ec

  sprint(show, E)
  sprint(show, MIME"text/plain"(), E)

  k, b = number_field(x^2 + 16)
  ktoK = hom(k, K, a^3 + 6*a)
  z = rand(k, -10:10)
  @test overlaps(restrict(E, ktoK)(z), E(ktoK(z)))

  ct = cm_types(k)
  cembd = Hecke.complex_embeddings(k)
  C = cm_type(k, cembd[1:1])
  @test number_field(C) === k
  @test Hecke.embeddings(C) == Hecke.complex_embeddings(k)[1:1]
  @test_throws ArgumentError cm_type(k, Hecke.complex_embeddings(k))
  @test_throws ArgumentError cm_type(number_field(x - 1)[1], AbsSimpleNumFieldEmbedding[])
  @test_throws ArgumentError cm_type(K, Hecke.complex_embeddings(K)[1:3]) # they are conjugated
  fl, c = Hecke.is_cm_field(k)
  @test c * C == cm_type(k, cembd[2:2])
  @test id_hom(k) * C == C

  K, a = cyclotomic_field(7)
  ct = Hecke.cm_types(K)
  @test count(is_primitive, ct) == 6

  Qx, x = QQ["x"]
  f = x^4 + 104x^2 + 796 # primitive non-galois quartic CM field
  K, a = number_field(f)
  ct = Hecke.cm_types(K)
  KK = Hecke.reflex(ct[1]).field
  @test is_isomorphic(KK, number_field(x^4 + 52*x^2 + 477)[1])
  @test is_isomorphic(Hecke.reflex(Hecke.reflex(ct[1])).field, K) # since primitive
end
