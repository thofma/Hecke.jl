@testset "NumField/NfAbs/NfAbs" begin
  cyclo_expl = function(n, m)
    Fn, zn = CyclotomicField(n)
    Fnm, znm = CyclotomicField(n*m)
    x = zn
    x_up = Hecke.force_coerce_cyclo(Fnm, x)
    x_down = Hecke.force_coerce_cyclo(Fn, x_up)
    return (x, x_up, x_down)
  end

  res = cyclo_expl(3, 4)
  @test (res[1]^3, res[2]^3) == (1, 1)

  res = cyclo_expl(3, 2)
  z6 = gen(parent(res[2]))
  # Test that z3 is mapped to z6^2
  @test z6^2 == res[2]
end
