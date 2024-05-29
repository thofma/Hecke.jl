function _test_elem(R::PadicField)
  p = prime(R)
  prec = rand(1:R.prec_max)
  r = ZZRingElem(0):p-1
  return R(sum(rand(r)*p^i for i in 0:prec))
end

function _test_elem(R::NonArchLocalField)
  d = degree(R)
  a = gen(R)
  x = R()
  for i in 0:d - 1
    if rand() < 0.5
      # Only fill every second coefficient
      continue
    end
    x += _test_elem(base_field(R))*a^i
  end
  return x
end

function test_elem(R::Hecke.LocalFieldValuationRingResidueRing)
  return R(_test_elem(Hecke._field(R)))
end

@testset "Conformance tests" begin
  # PadicField
  K = padic_field(17)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^3)
  test_Ring_interface(S)

  # the euclidean conformance test seems to assume that the ring is a domain
  S, RtoS = residue_ring(R, pi)
  test_EuclideanRing_interface(S)

  # QadicField
  K, a = qadic_field(17, 2)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^3)
  test_Ring_interface(S)

  # LocalField
  F, _ = cyclotomic_field(3)
  OF = maximal_order(F);
  K, toK = completion(F, 2*OF);
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^3)
  test_Ring_interface(S)
end


@testset "Howell form" begin
  K = padic_field(5)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^3)

  M = matrix(S, [5 1; 0 0])
  @test howell_form(M) == matrix(S, [5 1; 0 5^2])

  M = matrix(S, [10 1; 12 0])
  @test howell_form(M) == matrix(S, [12 0; 0 -1])
end
