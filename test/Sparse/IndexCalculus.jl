@testset "idxcalc" begin
  function cryptoprime(N)
    #return a Prime p with N digits. s.t (p-1)/2 is prime
    p = rand(fmpz(10)^(N-1):fmpz(10)^N)
    while true
      p = next_prime(p+1)
      !isprime(div(p-1,2)) || return p
    end 
  end 
 

  #fields of type Nemo.Galois_fmpz_field
  p = fmpz(349086633579683)
  F = GF(p)
  G = GF(p)
  a1 = F(198232795426937)
  a2 = F(2)
  b1 = F(27072022)
  b2 = F(123456789101112)
  b3 = F(1)
  q = fmpz(164911064979503)
  H = GF(q)
  aq = H(5)
  bq = H(3141592653)

  
  g1, _ = Hecke.IdxCalc(a1,b1)    #lift(a1) > qlimit
  @test a1^g1 == b1
  g2, _ = Hecke.IdxCalc(a1,b2,F)  #FB-logs stored on input F
  @test a1^g2 == b2
  set_attribute!(G, :a=>a2)       #lift(a2) on first position in FB
  Hecke.sieve(G)
  g3,_ = Hecke.IdxCalc(a2,b1,G)   #RelMat stored on input G
  @test a2^g3 == b1
  g4,_ = Hecke.IdxCalc(a2,a2)
  @test g4 == fmpz(1)
  g5,_ = Hecke.IdxCalc(a2,b3) 
  @test g5 == fmpz(0)
  g6,_ = Hecke.IdxCalc(aq, bq)    #lift(a3) in FB (not on first position)
  @test aq^g6 == bq


  #fields of type Nemo.GaloisField
  p = 996968291821725359
  F = GF(p)
  a = F(11) #lift(a)<qlimit
  b = F(18)
  g,_ = Hecke.IdxCalc(a,b)
  @test a^g == b

  p = 8773173743
  F = GF(p)
  a = F(5800865131) #lift(a)>qlimit
  b = F(199)
  g,_ = Hecke.IdxCalc(a,b)
  @test a^g == b

  p = Int(cryptoprime(13)) #random example
  F = GF(p)
  a = Hecke.primitive_element(F)
  b = rand(F)
  g,_ = Hecke.IdxCalc(a,b)
  @test a^g == b


  if long_test
    for i = 10:20
      pr = cryptoprime(i)
      F = GF(pr)
      a = Hecke.primitive_element(F)
      b = rand(F)
      c = rand(F)
      g1, _ = Hecke.IdxCalc(a, b)
      g2, _ = Hecke.IdxCalc(a, c)
      @test a^g1==b
      @test a^g2==c
    end
    for i = 7:17
     pr = Int(cryptoprime(i))
     F = GF(pr)
     a = Hecke.primitive_element(F)
     b = rand(F)
     c = rand(F)
     g1, _ = Hecke.IdxCalc(a, b)
     g2, _ = Hecke.IdxCalc(a, c)
     @test a^g1==b
     @test a^g2==c
    end
  end
end


