@testset "Selmer" begin
  k, a = wildanger_field(3, 13);
  zk = maximal_order(k);
  S = collect(keys(factor(6*zk)));
  Sel, map = pselmer_group_fac_elem(2, S);
  g = evaluate(map(Sel[3]));
  K, _ = radical_extension(2, g);
  ZK = maximal_order(K);
  @test issubset(Set(keys(factor(discriminant(ZK)))) , S)

  sel, mmap = pselmer_group_fac_elem(2, [-1, 2, 3]);
  h = hom(Sel, sel, [preimage(mmap, Hecke.factored_norm(map(g), parent = codomain(mmap))) for g = gens(Sel)]);
  k, mk = kernel(h);

  # The auxiliary class-group prime cursor must not overwrite the requested
  # Selmer exponent. Over Q(sqrt(-14)), the primes above 2 leave an even
  # class-group index, so this executes that cursor before forming the
  # 2-Selmer quotient.
  Qx, x = QQ["x"]
  L, _ = number_field(x^2 + 14, "b")
  OL = maximal_order(L)
  S2 = first.(prime_decomposition(OL, 2))
  Sel2, mSel2 = pselmer_group_fac_elem(2, S2)
  @test order(Sel2) == 8
  for value in (L(-1), L(2))
    coordinate = preimage(mSel2, codomain(mSel2)(value))
    @test is_square(evaluate(mSel2(coordinate)) / value)
  end
end
