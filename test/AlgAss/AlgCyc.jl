
@testset "Splitting of cyclic algebras" begin
  QQx, x = QQ[:x]
  k1, g1 = number_field(x^2 + 1)
  sigma1 = hom(k1, k1, -g1)
  @test false
  @test is_split(cyclic_algebra(k1, sigma1, QQ(1)))
  @test !is_split(cyclic_algebra(k1, sigma1, QQ(3)))

  c = cyclic_algebra(k1, sigma1, QQ(4))
  splits, iso = is_split_with_map(c)
  @test splits
  @test iso(domain(iso)(1)) == codomain(iso)(1)
  @test all(iso(x) * iso(y) == iso(x * y) for x in basis(c), y in basis(c))

  # Over relative number fields
  k, _ = number_field(x^6 + x^3 + 1)
  _, y = k[:y]
  l, g = number_field(y^2 - 2)
  c = cyclic_algebra(l, hom(l, l, -g), k(-1))
  splits, iso = is_split_with_map(c)
  @test splits
  @test iso(domain(iso)(1)) == codomain(iso)(1)
  @test all(iso(x) * iso(y) == iso(x * y) for x in basis(c), y in basis(c))
end

@testset "Isomorphisms of cyclic algebras" begin
  QQx, x = QQ[:x]
  k1, g1 = number_field(x^2 - 5)
  k2, g2 = number_field(x^2 - 3 * 8^2)
  @test is_isomorphic(
    cyclic_algebra(k1, hom(k1, k1, -g1), QQ(3 * 2^2)),
    cyclic_algebra(k2, hom(k2, k2, -g2), QQ(5 * 123^2))
  )

  @test !is_isomorphic(
    cyclic_algebra(k1, hom(k1, k1, -g1), QQ(3)),
    cyclic_algebra(k2, hom(k2, k2, -g2), QQ(3))
  )

  c1 = cyclic_algebra(k1, hom(k1, k1, -g1), QQ(3 * 2^2))
  c2 = cyclic_algebra(k2, hom(k2, k2, -g2), QQ(5))
  @test is_isomorphic(c1, c2)
  is_iso, iso = is_isomorphic_with_map(c1, c2)
  @test is_iso
  @test iso(domain(iso)(1)) == codomain(iso)(1)
  @test all(iso(x) * iso(y) == iso(x * y) for x in basis(c1), y in basis(c1))

  # Linearly disjoint case for absolute number fields
  k1, _ = number_field(x^3 + 3 * x^2 - 1)
  k2, _ = number_field(x^3 + 15 * x^2 + 14 * x + 3)
  sigma1 = hom(k1, k1, -gen(k1)^2 - 3 * gen(k1) - 1)
  sigma2 = hom(k2, k2, -3 * gen(k2)^2 - 44 * gen(k2) - 28)
  c1 = cyclic_algebra(k1, sigma1, QQ(-30))
  c2 = cyclic_algebra(k2, sigma2, QQ(-60))
  is_iso, iso = is_isomorphic_with_map(c1, c2)
  @test is_iso
  @test iso(domain(iso)(1)) == codomain(iso)(1)
  @test all(iso(x) * iso(y) == iso(x * y) for x in basis(c1), y in basis(c1))

  # Non-linearly disjoint case
  k1, g1 = number_field(x^4 + 2 * x^3 + 4 * x^2 - 2x + 11)
  k2, g2 = number_field(x^4 + 4 * x^3 - 14 * x^2 - x + 11)
  sigma1 = hom(k1, k1, -1//2 * g1^2 - g1 - 3//2)
  sigma2 = hom(k2, k2, 12//19 * g2^3 + 59//19 * g2^2 - 106//19 * g2 - 87//19)
  c1 = cyclic_algebra(k1, sigma1, QQ(3))
  c2 = cyclic_algebra(k2, sigma2, QQ(-3))
  is_iso, iso = is_isomorphic_with_map(c1, c2)
  @test is_iso
  @test iso(domain(iso)(1)) == codomain(iso)(1)
  @test all(iso(x) * iso(y) == iso(x * y) for x in basis(c1), y in basis(c1))

  # Non-linearly disjoint case
  k1, g1 = number_field(x^6 + 9 * x^4 + 14 * x^2 + 1)
  k2, g2 = number_field(x^6 + 18 * x^4 + 56 * x^2 + 8)
  sigma1 = hom(k1, k1, 4//5 * g1^5 + 7 * g1^3 + 51//5 * g1)
  sigma2 = hom(k2, k2, 1//5 * g2^5 + 7//2 * g2^3 + 51//5 * g2)
  c1 = cyclic_algebra(k1, sigma1, QQ(2))
  c2 = cyclic_algebra(k2, sigma2, QQ(1))
  @test !first(is_isomorphic_with_map(c1, c2))
end
