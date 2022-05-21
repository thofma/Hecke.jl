@testset "Isomorphisms" begin
  K = GF(7)
  E = EllipticCurve(K, [1, 2, 3, 4, 5])
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
  
  F1, phi1 = transform_rstu(E1, [1, a, 0, 1])
  F2, phi2 = transform_rstu(E2, [0, 1, 1, a])
  F3, phi3 = transform_rstu(E3, [1, b^2, b, 1])
  F4, phi4 = transform_rstu(E4, [0, 1, b^5, b - 1])
  F5, phi5 = transform_rstu(E5, [2, 0, 1, 3])
  
  @test @inferred is_isomorphic(E1, F1)
  @test @inferred is_isomorphic(E2, F2)
  @test @inferred is_isomorphic(E3, F3)
  @test @inferred is_isomorphic(E4, F4)
  @test @inferred is_isomorphic(E5, F5)

  psi1 = @inferred isomorphism(E1, F1)
  psi2 = @inferred isomorphism(E2, F2)
  psi3 = @inferred isomorphism(E3, F3)
  psi4 = @inferred isomorphism(E4, F4)
  psi5 = @inferred isomorphism(E5, F5)
  
  @test isomorphism_data(psi2 * inv(phi2)) == isomorphism_data(identity_map(E2)) || isomorphism_data(psi2 * inv(phi2)) == isomorphism_data(negation_map(E2))
  @test (psi4 * inv(phi4)) == identity_map(E4) || (psi4 * inv(phi4)) == negation_map(E4)
  @test (psi5 * inv(phi5)) == identity_map(E5) || (psi5 * inv(phi5)) == negation_map(E5)
  
  # automorphism group
  E6 = EllipticCurve([1, 2])
  K, = Hecke.rationals_as_number_field()
  E7 = EllipticCurve(K, [1, 2])
  Es = [E1, E2, E3, E4, E5, E6, E7]
  ids = [(24, 3), (2, 1), (12, 1), (2, 1), (2, 1), (2, 1), (2, 1)]
  for i in 1:length(Es)
    E = Es[i]
    G, GtoAut = @inferred automorphism_group(E)
    @test find_small_group(G)[1] == ids[i]
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

