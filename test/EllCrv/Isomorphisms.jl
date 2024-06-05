@testset "Isomorphisms" begin
  K = GF(7)
  E = elliptic_curve(K, [1, 2, 3, 4, 5])
  P = rand(E)
  f = @inferred negation_map(E)
  @test f(P) == -P

  K = GF(2,4)
  a = gen(K)
  E1 = elliptic_curve_from_j_invariant(K(0))
  E2 = elliptic_curve_from_j_invariant(a)

  L = GF(3,2)
  b = gen(L)
  E3 = elliptic_curve_from_j_invariant(L(0))
  E4 = elliptic_curve_from_j_invariant(L(2))
  E5 = elliptic_curve_from_j_invariant(12)

  E8 = elliptic_curve_from_j_invariant(0)

  L, i = quadratic_field(-1)
  E9 = elliptic_curve_from_j_invariant(L(1728))

  L, c = cyclotomic_field(3)
  E10 = base_change(L, E8)

  F1, phi1 = transform_rstu(E1, [1, a, 0, 1])
  F2, phi2 = transform_rstu(E2, [0, 1, 1, a])
  F3, phi3 = transform_rstu(E3, [1, b^2, b, 1])
  F4, phi4 = transform_rstu(E4, [0, 1, b^5, b - 1])
  F5, phi5 = transform_rstu(E5, [2, 0, 1, 3])
  F8, phi8 = transform_rstu(E8, [0, 1, 2, 5])
  F9, phi9 = transform_rstu(E9, [-3, 6, 1, 3])

  @test @inferred is_isomorphic(E1, F1)
  @test @inferred is_isomorphic(E2, F2)
  @test @inferred is_isomorphic(E3, F3)
  @test @inferred is_isomorphic(E4, F4)
  @test @inferred is_isomorphic(E5, F5)
  @test @inferred is_isomorphic(E8, F8)
  @test @inferred is_isomorphic(E9, F9)

  psi1 = @inferred isomorphism(E1, F1)
  psi2 = @inferred isomorphism(E2, F2)
  psi3 = @inferred isomorphism(E3, F3)
  psi4 = @inferred isomorphism(E4, F4)
  psi5 = @inferred isomorphism(E5, F5)
  psi6 = @inferred isomorphism(E8, F8)
  psi7 = @inferred isomorphism(E9, F9)

  @test isomorphism_data(psi2 * inv(phi2)) == isomorphism_data(identity_map(E2)) || isomorphism_data(psi2 * inv(phi2)) == isomorphism_data(negation_map(E2))
  @test (psi4 * inv(phi4)) == identity_map(E4) || (psi4 * inv(phi4)) == negation_map(E4)
  @test (psi5 * inv(phi5)) == identity_map(E5) || (psi5 * inv(phi5)) == negation_map(E5)

  P = points_with_x_coordinate(E4, b)[1]
  @test @inferred preimage(psi4, psi4(P)) == P
  E4oo = infinity(E4)
  @test @inferred preimage(psi4, psi4(E4oo)) == E4oo


  @test @inferred degree(phi1) == 1

  # automorphism group
  E6 = elliptic_curve([1, 2])
  K, = Hecke.rationals_as_number_field()
  E7 = elliptic_curve(K, [1, 2])


  K = GF(2,4)
  a = gen(K)
  E2_a = elliptic_curve_from_j_invariant(a)

  E2_0_2 = elliptic_curve_from_j_invariant(GF(2)(0))
  E2_0_4 = elliptic_curve(K, [0, 0, 1, a^3 + a^2, 0])
  E2_0_6 = elliptic_curve(K, [0, 0, a, 0, 0])
  E2_0_24 = elliptic_curve_from_j_invariant(K(0))

  E3_2 = elliptic_curve_from_j_invariant(L(2))

  K = GF(3, 2)
  a = gen(K)
  E3_0_2 = elliptic_curve_from_j_invariant(GF(3)(0))
  E3_0_4 = elliptic_curve(K, [2*a, 0])
  E3_0_6 = elliptic_curve(K, [0, 0, 0, 2, 1])
  E3_0_12 = elliptic_curve_from_j_invariant(K(0))



  Es = [E5, E6, E7, E8, E9, E10,
    E2_a,
    E2_0_2, E2_0_4, E2_0_6, E2_0_24,
    E3_2,
    E3_0_2, E3_0_4, E3_0_6, E3_0_12]
  ids = [(2, 1), (2, 1), (2, 1), (2, 1), (4, 1), (6, 2), (2, 1), (2, 1), (4, 1), (6, 2), (24, 3),(2, 1), (2, 1), (4, 1), (6, 2), (12, 1)]
  for i in 1:length(Es)
    E = Es[i]
    G, GtoAut = @inferred automorphism_group(E)
    @test Hecke.find_small_group(G)[1] == ids[i]
    for g in G
      a = GtoAut(g)
      @test domain(a) == codomain(a) == E
      for h in G
        @test GtoAut(g) * GtoAut(h) == GtoAut(g * h)
      end
      @test GtoAut\(GtoAut(g)) == g
    end
  end
end

