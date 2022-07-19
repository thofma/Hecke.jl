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
end
