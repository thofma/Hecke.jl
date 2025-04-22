@testset "Cyclotomic" begin
  for q in [7, 7^2, 2^2, 2^3, 2^4]
    K, a = cyclotomic_real_subfield(q)
    v = cyclotomic_units_totally_real(K)
    @test length(v) == degree(K) # = unit rank + 1
  end

  K, a = cyclotomic_real_subfield(7)
  v = cyclotomic_units_totally_real(K)
  # Class number of Q(zeta_7)^+ is one, so the cyclotomic units are the units
  @test overlaps(regulator(maximal_order(K)), regulator(v[2:end]))

  R = ArbField(64)
  reg = @inferred cyclotomic_regulator(3^2, 64, maximal_totally_real = true)
  @test contains(reg, big"0.849287450646192528644762004937446736214795179711378610368436838203825791002373")
  reg = @inferred cyclotomic_regulator(3^2, 64, maximal_totally_real = false)
  @test contains(reg, big"3.39714980258477011457904801974978694485918071884551444147374735281530316401")

  reg = @inferred cyclotomic_regulator(3^1, 64, maximal_totally_real = true)
  @test contains(reg, 1)

  reg = @inferred cyclotomic_regulator(5^1, 64, maximal_totally_real = true)
  @test contains(reg, big"0.48121182505960344749775891342436842313")

  reg = @inferred cyclotomic_regulator(5^1, 64, maximal_totally_real = false)
  @test contains(reg, big"0.96242365011920689499551782684873684627")

  reg = @inferred cyclotomic_regulator(2^2, 64, maximal_totally_real = false)
  @test contains(reg, 1)

  reg = @inferred cyclotomic_regulator(2^3, 64, maximal_totally_real = false)
  @test contains(reg, big"1.762747174039086050465218649959584618056320656523270821506591217306754368444002")

  reg = @inferred cyclotomic_regulator(2^3, 64, maximal_totally_real = true)
  @test contains(reg, big"0.8813735870195430252326093249797923090281603282616354107532956086533771842220012")
end
