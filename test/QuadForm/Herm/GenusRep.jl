@testset "GenusRep" begin

  #
  # Some definite examples
  #

  # Lattice 214 from the database: `a(P) != P` in `_neighbours`

  Qx, x = polynomial_ring(QQ, "x")
  f = x^2 - x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 - a + 3
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gene = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1, 0, 0]), map(E, [0, 1, -1]), map(E, [0, -1//2*a*b - 1//2*a + 3//2, 0])]

  L = hermitian_lattice(E, gene, gram = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test isempty(gens)
  @test def

  gen_rep = @inferred genus_representatives(L)
  @test length(gen_rep) == 2
  @test L in gen_rep
  @test !is_isometric_with_isometry(gen_rep[1], gen_rep[2])[1]


  # Lattice 324 from the database: `special == true` in `_neighbours`

  Qx, x = polynomial_ring(QQ, "x")
  f = x^2 - x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 - a + 3
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, 1, 0, 0]), map(E, [(a + 3//2)*b - 13//2*a + 2, 0, (1//2*a + 1//2)*b + 3*a - 33//2, 0]), map(E, [0, 0, 2, 1]), map(E, [(-92011//2*a - 62822)*b - 15049//2*a + 178467//2, 0, (-126700*a + 60200)*b + 160300*a - 109900, 0])]

  L = hermitian_lattice(E, gens, gram = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test isempty(gens)
  a = involution(L)
  @test a(P0) == P0
  ok, scale = is_modular(L,P0)
  if scale != 0 && is_ramified(base_ring(L), minimum(P0))
    special = isodd(scale)
  end
  @test special

  @test genus_representatives(L) == [L]

  # Lattice 441 from the database: `special == false` in `_neighbours`; calls `_all_row_span`

  Qx, x = polynomial_ring(QQ, "x")
  f = x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 11
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [5//2*b + 121//2, 1//2*b + 55//2, 0, 0]), map(E, [-1, -3, -1, 0]), map(E, [987//2*b - 2407//2, 475//2*b - 679//2, 0, 2*b + 62]), map(E, [3906*b - 16305, 2074*b - 5477, 0, 70*b + 595])]

  L = hermitian_lattice(E, gens, gram = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  a = involution(L)
  @test a(P0) == P0
  ok, scale = is_modular(L,P0)
  @test scale == 0
  gen_rep = @inferred representatives(genus(L))
  @test any(LL -> is_isometric_with_isometry(LL,L)[1], gen_rep)
  @test !all(LL -> is_isometric_with_isometry(LL,L)[1], gen_rep)

  #
  # An indefinite example (see [Kir19, Page 9])
  #


  K, a = rationals_as_number_field()
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 17
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 2, 2, [102, b, -b, 0])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1, 0]), map(E, [b, 0]), map(E, [0, 1]), map(E, [0, b])]

  L = hermitian_lattice(E, gens, gram = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test !def
  @test length(gens) == 1
  P, e = gens[1]
  @test minimum(P) == 3*maximal_order(K)
  @test e == 4
  @test P0 == 1*maximal_order(E)

  gen_rep = @inferred genus_representatives(L)
  @test length(gen_rep) == 4
  @test L in gen_rep
  a = involution(L)
  @test a(P) != P
  PB = [pseudo_basis(LL) for LL in gen_rep]
  @test all(i -> PB[i][1][2] == P^(i-1) && PB[i][2][2]^-1 == a(P)^(i-1), 1:length(PB))

  #
  # Other indefinite examples
  #

  Qx, x = QQ["x"]
  K, a = number_field(x - 1, "a")
  Kt, t = K["t"]
  E, b = number_field(t^2 + 1, "b")
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = genus(HermLat, E, p, [(0, 3, -1, 0)])
  L = @inferred representative(G)
  @test length(@inferred Hecke.genus_representatives(L)) == 1

  Qx, x = polynomial_ring(QQ, "x")
  f = x^6 + x^5 + x^4 + x^3 + x^2 + x + 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 47
  E, z_7 = number_field(g, "b", cached = false)
  b = z_7
  D = matrix(E, 6, 6, [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1, 0, 0, 0, 0, 0]), map(E, [z_7, 0, 0, 0, 0, 0]), map(E, [z_7^2, 0, 0, 0, 0, 0]), map(E, [z_7^3, 0, 0, 0, 0, 0]), map(E, [z_7^4, 0, 0, 0, 0, 0]), map(E, [z_7^5, 0, 0, 0, 0, 0]), map(E, [1//2*b + 1//2, 0, 0, 0, 0, 0]), map(E, [1//2*z_7*b + 1//2*z_7, 0, 0, 0, 0, 0]), map(E, [1//2*z_7^2*b + 1//2*z_7^2, 0, 0, 0, 0, 0]), map(E, [1//2*z_7^3*b + 1//2*z_7^3, 0, 0, 0, 0, 0]), map(E, [1//2*z_7^4*b + 1//2*z_7^4, 0, 0, 0, 0, 0]), map(E, [1//2*z_7^5*b + 1//2*z_7^5, 0, 0, 0, 0, 0]), map(E, [0, 1, 0, 0, 0, 0]), map(E, [0, z_7, 0, 0, 0, 0]), map(E, [0, z_7^2, 0, 0, 0, 0]), map(E, [0, z_7^3, 0, 0, 0, 0]), map(E, [0, z_7^4, 0, 0, 0, 0]), map(E, [0, z_7^5, 0, 0, 0, 0]), map(E, [0, 1//2*b + 1//2, 0, 0, 0, 0]), map(E, [0, 1//2*z_7*b + 1//2*z_7, 0, 0, 0, 0]), map(E, [0, 1//2*z_7^2*b + 1//2*z_7^2, 0, 0, 0, 0]), map(E, [0, 1//2*z_7^3*b + 1//2*z_7^3, 0, 0, 0, 0]), map(E, [0, 1//2*z_7^4*b + 1//2*z_7^4, 0, 0, 0, 0]), map(E, [0, 1//2*z_7^5*b + 1//2*z_7^5, 0, 0, 0, 0]), map(E, [0, 0, 1, 0, 0, 0]), map(E, [0, 0, z_7, 0, 0, 0]), map(E, [0, 0, z_7^2, 0, 0, 0]), map(E, [0, 0, z_7^3, 0, 0, 0]), map(E, [0, 0, z_7^4, 0, 0, 0]), map(E, [0, 0, z_7^5, 0, 0, 0]), map(E, [0, 0, 1//2*b + 1//2, 0, 0, 0]), map(E, [0, 0, 1//2*z_7*b + 1//2*z_7, 0, 0, 0]), map(E, [0, 0, 1//2*z_7^2*b + 1//2*z_7^2, 0, 0, 0]), map(E, [0, 0, 1//2*z_7^3*b + 1//2*z_7^3, 0, 0, 0]), map(E, [0, 0, 1//2*z_7^4*b + 1//2*z_7^4, 0, 0, 0]), map(E, [0, 0, 1//2*z_7^5*b + 1//2*z_7^5, 0, 0, 0]), map(E, [0, 0, 0, 1, 0, 0]), map(E, [0, 0, 0, z_7, 0, 0]), map(E, [0, 0, 0, z_7^2, 0, 0]), map(E, [0, 0, 0, z_7^3, 0, 0]), map(E, [0, 0, 0, z_7^4, 0, 0]), map(E, [0, 0, 0, z_7^5, 0, 0]), map(E, [0, 0, 0, 1//2*b + 1//2, 0, 0]), map(E, [0, 0, 0, 1//2*z_7*b + 1//2*z_7, 0, 0]), map(E, [0, 0, 0, 1//2*z_7^2*b + 1//2*z_7^2, 0, 0]), map(E, [0, 0, 0, 1//2*z_7^3*b + 1//2*z_7^3, 0, 0]), map(E, [0, 0, 0, 1//2*z_7^4*b + 1//2*z_7^4, 0, 0]), map(E, [0, 0, 0, 1//2*z_7^5*b + 1//2*z_7^5, 0, 0]), map(E, [0, 0, 0, 0, 1, 0]), map(E, [0, 0, 0, 0, z_7, 0]), map(E, [0, 0, 0, 0, z_7^2, 0]), map(E, [0, 0, 0, 0, z_7^3, 0]), map(E, [0, 0, 0, 0, z_7^4, 0]), map(E, [0, 0, 0, 0, z_7^5, 0]), map(E, [0, 0, 0, 0, 1//2*b + 1//2, 0]), map(E, [0, 0, 0, 0, 1//2*z_7*b + 1//2*z_7, 0]), map(E, [0, 0, 0, 0, 1//2*z_7^2*b + 1//2*z_7^2, 0]), map(E, [0, 0, 0, 0, 1//2*z_7^3*b + 1//2*z_7^3, 0]), map(E, [0, 0, 0, 0, 1//2*z_7^4*b + 1//2*z_7^4, 0]), map(E, [0, 0, 0, 0, 1//2*z_7^5*b + 1//2*z_7^5, 0]), map(E, [0, 0, 0, 0, 0, 1]), map(E, [0, 0, 0, 0, 0, z_7]), map(E, [0, 0, 0, 0, 0, z_7^2]), map(E, [0, 0, 0, 0, 0, z_7^3]), map(E, [0, 0, 0, 0, 0, z_7^4]), map(E, [0, 0, 0, 0, 0, z_7^5]), map(E, [0, 0, 0, 0, 0, 1//2*b + 1//2]), map(E, [0, 0, 0, 0, 0, 1//2*z_7*b + 1//2*z_7]), map(E, [0, 0, 0, 0, 0, 1//2*z_7^2*b + 1//2*z_7^2]), map(E, [0, 0, 0, 0, 0, 1//2*z_7^3*b + 1//2*z_7^3]), map(E, [0, 0, 0, 0, 0, 1//2*z_7^4*b + 1//2*z_7^4]), map(E, [0, 0, 0, 0, 0, 1//2*z_7^5*b + 1//2*z_7^5])]
  L = hermitian_lattice(E, gens, gram = D)
  @test length(Hecke.genus_representatives(L)) == 15

  #
  # Rank 1 example
  #

  # CM and relative class number 1
  E, b = cyclotomic_field_as_cm_extension(12, cached=false)
  V = hermitian_space(E, 1)
  L = lattice(V)
  @test length(genus_representatives(L)) == 1

  # CM and relative class number 3
  E, b = cyclotomic_field_as_cm_extension(23; cached=false)
  L = lattice(hermitian_space(E, 1))
  @test length(genus_representatives(L)) == 3

  # Non-CM and class number 1; Salem polynomial
  _, x = QQ["x"]
  _, _b = number_field(x^(10)+x^9-x^7-x^6-x^5-x^4-x^3+x+1; cached=false)
  K, a = number_field(minpoly(_b+inv(_b)); cached=false)
  _, t = polynomial_ring(K, "t"; cached=false)
  E, _ = number_field(t^2-a*t+1; cached=false)
  H = lattice(hermitian_space(E, 1))
  @test length(genus_representatives(H)) == 1

  # Non-CM and class number 69; Salem polynomial
  Qx, x = polynomial_ring(QQ, "x")
  f = x^3 - 44*x^2 - 4*x + 175
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 - a*t + 1
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 1, 1, [-573233//59387557*a^2 + 26558651//59387557*a - 1641753//1448477])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [59387557]), map(E, [41//64*a + 773652247//64]), map(E, [1//222784*a^2 + 453//222784*a + 6337027807197//111392]), map(E, [b + 23*a + 53784681]), map(E, [(1//64*a + 63//64)*b + 23//64*a^2 + 26893065//32*a + 3388434903//64]), map(E, [(1//222784*a^2 + 453//222784*a + 86461//111392)*b + 3362257//13924*a^2 + 24368437791//222784*a + 9300554603857//222784])]
  L = hermitian_lattice(E, gens, gram = D)
  @test length(genus_representatives(L)) == 69

  let
    # 1512
    Qx, x = polynomial_ring(QQ, "x")
    f = x^3 - 6*x^2 - 4*x + 23
    K, a = number_field(f, "a", cached = false)
    Kt, t = polynomial_ring(K, "t")
    g = t^2 - a*t + 1
    E, b = number_field(g, "b", cached = false);
    S = unique([restrict(r, K) for r in filter(!is_real, infinite_places(E)) if is_real(restrict(r, K))]);
    sort!(S, lt=(p,q) -> isless(real(embedding(p).r), real(embedding(q).r)));
    vals = Int[1, 1];
    sig = Dict(S[i] => vals[i] for i in 1:2);
    OK = maximal_order(K);
    ps = AbsSimpleNumFieldOrderIdeal[ideal(OK, v) for v in Vector{AbsSimpleNumFieldOrderElem}[map(OK, [2, a^2 + a + 1]), map(OK, [2, a + 3]), map(OK, [11, a + 6]), map(OK, [239, a + 174]), map(OK, [1487, a + 881])]];
    datas = [[(0, 1, 1)], [(0, 1, 1)], [(-1, 1, -1)], [(3, 1, -1)], [(-1, 1, 1)]];
    lgs = HermLocalGenus{typeof(E), AbsSimpleNumFieldOrderIdeal}[genus(HermLat, E, ps[i], datas[i]) for i in 1:5];
    G = HermGenus(E, 1, lgs, sig)
    GG = representative(G)
    @test GG in G
  end

  let # 1851
    Qx, x = polynomial_ring(QQ, :x)
    f = x^3 + x^2 - 2*x - 1
    K, a = number_field(f, :a, cached = false)
    Kt, t = polynomial_ring(K, :t)
    g = t^2 - a*t + 1
    E, b = number_field(g, :b, cached = false)
    D = matrix(E, 3, 3, [-1//49, 0, 0, 0, -1//49, 0, 0, 0, -1//49])
    gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[
             map(E, [7, 0, 0]),
             map(E, [7*a, 0, 0]),
             map(E, [a^2 + 3*a + 4, 0, 0]),
             map(E, [7*b, 0, 0]),
             map(E, [7*a*b, 0, 0]),
             map(E, [(a^2 + 3*a + 4)*b, 0, 0]),
             map(E, [0, 7, 0]),
             map(E, [0, 7*a, 0]),
             map(E, [0, a^2 + 3*a + 4, 0]),
             map(E, [0, 7*b, 0]),
             map(E, [0, 7*a*b, 0]),
             map(E, [0, (a^2 + 3*a + 4)*b, 0]),
             map(E, [0, 0, 7]),
             map(E, [0, 0, 7*a]),
             map(E, [0, 0, a^2 + 3*a + 4]),
             map(E, [0, 0, 7*b]),
             map(E, [0, 0, 7*a*b]),
             map(E, [0, 0, (a^2 + 3*a + 4)*b])]
    L = hermitian_lattice(E, gens, gram = D)
    @test length(genus_representatives(L)) == 2
    @test length(genus_representatives(L; use_mass = true)) == 2
  end
end
