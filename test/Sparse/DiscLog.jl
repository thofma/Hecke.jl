@testset "disclog" begin
  function rand_dec_prime(N) #returns prime numer of decimal length N
      lower = fmpz(10)^(N-1)
      upper = fmpz(10)^N
      p = rand(lower:upper)
      p = next_prime(p)
      if p >= upper
          return next_prime(lower)
      end
      return p
  end
  

  #without IdxCalc
  p = fmpz(9409016962502068912909)
  F = GF(p)
  a = F(1350741637263611412719)
  b = F(899939368497036385790)
  g = Hecke.disc_log(a,b)
  @test a^g == b

  #uses IdxCalc once
  p = fmpz(2682216710943704337881)
  F = GF(p)
  a = F(1163261382658233061985)
  b = F(968866103873076459441)
  g = Hecke.disc_log(a,b)
  @test a^g == b

  if long_test
    for i = 5:20
      p = rand_dec_prime(i)
      F = GF(p)
      a = Hecke.primitive_element(F)
      b = rand(F)
      g = Hecke.disc_log(a,b)
      @test a^g == b 
    end
  end
end