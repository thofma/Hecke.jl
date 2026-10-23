# Quotients and normal-form remainders preserve the ambient module embedding.
@testset "quotients" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  N = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6])

  Q, MtoQ = quo(M, N)
  @test MtoQ isa Hecke.EmbeddedModuleMap
  x = Hecke._element_from_coordinates(M, ZZRingElem[1, 0])
  y = Hecke._element_from_coordinates(M, ZZRingElem[2, 0])
  @test !iszero(MtoQ(x))
  @test iszero(MtoQ(y))
  @test coordinates(preimage(MtoQ, MtoQ(x))) == coordinates(x)

  V, MtoV = Hecke.quotient_vector_space(M, N, ZZ(2))
  RtoF = Hecke.ring_map(MtoV)
  @test MtoV isa Hecke.EmbeddedModuleMap
  @test domain(MtoV) === M
  @test codomain(MtoV) === V
  @test domain(RtoF) === ZZ
  @test codomain(RtoF) === base_ring(V)
  @test dim(V) == 2
  @test !iszero(MtoV(x))
  @test iszero(MtoV(y))
  @test coordinates(preimage(MtoV, MtoV(x))) == coordinates(x)

  Mline = Hecke.embedded_module(ZZ, QQ, QQ[1 0])
  Nline = Hecke.embedded_module(ZZ, QQ, QQ[0 1])
  @test_throws ArgumentError quo(Mline, Nline)
end

@testset "Normal-form remainders" begin
  function test_remainder(M, N, x, z)
    c = coordinates(x)
    a = Hecke.ambient_coordinates(x)
    @test Hecke.ambient_coordinates(z) in N
    y = mod(x, N)
    @test parent(y) === M
    @test Hecke.ambient_coordinates(x - y) in N
    @test Hecke.ambient_coordinates(y) in M
    @test mod(y, N) == y
    @test mod(x + z, N) == mod(x - z, N) == y
    @test coordinates(x) == c
    @test Hecke.ambient_coordinates(x) == a
  end

  @testset "PID matrices" begin
    F, t = rational_function_field(GF(7), "t")
    Rinf = localization(F, degree)
    for (R, K, p) in ((ZZ, QQ, ZZ(3)),
                      (parent(numerator(t)), F, numerator(t)),
                      (Rinf, F, Rinf(inv(t))))
      s = K(p)
      B = K[inv(s) 0 0 0; 1 s 0 0; 0 1 inv(s) 0]
      M = Hecke.embedded_module(R, K, B; is_basis_matrix = true)
      x = Hecke._element_from_coordinates(M,
            elem_type(R)[R(a) for a in (-1, p + 1, -1)])
      for T in (R[p 0 0; 1 0 p^2], R[0 p p],
                identity_matrix(R, 3), zero_matrix(R, 0, 3))
        N = Hecke.embedded_module(R, K, change_base_ring(K, T)*B)
        c = [zero(R) for _ in 1:3]
        for i in 1:nrows(T), j in 1:3
          c[j] += (p + R(i))*T[i, j]
        end
        z = Hecke._element_from_coordinates(M, c)
        test_remainder(M, N, x, z)
        if R === ZZ && nrows(T) == 2
          @test coordinates(mod(x, N)) == ZZRingElem[0, 4, 8]
        end
      end
      Z = Hecke.zero_embedded_module(R, K, 4)
      @test mod(x, Z) == x
      @test iszero(mod(x, M))
      @test iszero(mod(zero(Z), Z))
      larger = Hecke.embedded_module(R, K, inv(s)*B)
      outside = Hecke.embedded_module(R, K, K[0 0 0 1])
      incompatible = Hecke.zero_embedded_module(R, K, 5)
      other_ambient = Hecke.embedded_module(R, K, B;
                                            overstructure = Ref(:other))
      for N in (larger, outside, incompatible, other_ambient)
        @test_throws ArgumentError mod(x, N)
      end
    end

    M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
    N = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
    x = Hecke._element_from_coordinates(M, ZZRingElem[-1, -1])
    @test coordinates(mod(x, N)) == ZZRingElem[1, 2]
    MM = Hecke.embedded_module(ZZ, QQ, QQ[1 1; 0 1];
                               is_basis_matrix = true)
    @test MM == M
    y = Hecke._element_from_coordinates(MM, ZZRingElem[3, 0])
    @test coordinates(mod(y, N)) == ZZRingElem[3, 0]
    @test Hecke.ambient_coordinates(y - mod(y, N)) in N
  end

  @testset "Pseudo-matrices" begin
    function test_pseudo_remainder(R, K, I, p)
      J = inv(I)
      B = K[1 0 0; 0 1 1]
      M = Hecke.embedded_module(R, K, Hecke.pseudo_matrix(R, B, [I, J]);
                                 is_basis_matrix = true)
      a = -(1 + p)*K(first(basis(I)))
      b = (1 + p^2)*K(last(basis(J)))
      x = Hecke._element_from_coordinates(M, elem_type(K)[a, b])
      for (T, C) in ((K[p 0; 0 p^2], [I, J]),
                      (K[p 0; p p^2], [I, I]), (K[1 1], [I]))
        N = Hecke.embedded_module(R, K, Hecke.pseudo_matrix(R, T*B, C))
        c = [zero(K), zero(K)]
        for i in 1:nrows(T)
          d = (1 + p)*K(first(basis(C[i])))
          for j in 1:2
            c[j] += d*T[i, j]
          end
        end
        z = Hecke._element_from_coordinates(M, c)
        test_remainder(M, N, x, z)
      end
      N = Hecke.embedded_module(R, K,
            Hecke.pseudo_matrix(R, K[p 0; 0 p^2]*B, [I, J]))
      @test coordinates(mod(x, N)) ==
            elem_type(K)[mod(a, p*I), mod(b, p^2*J)]
      @test !([one(K) for _ in 1:3] in M)
      Z = Hecke.zero_embedded_module(R, K, 3)
      @test mod(x, Z) == x
      @test iszero(mod(x, M))
      @test iszero(mod(zero(Z), Z))
      larger = Hecke.embedded_module(R, K,
                 Hecke.pseudo_matrix(R, B, [inv(p)*I, J]))
      @test_throws ArgumentError mod(x, larger)
      @test_throws ArgumentError mod(x,
        Hecke.zero_embedded_module(R, K, 4))
    end

    K, a = quadratic_field(-5)
    R = maximal_order(K)
    I = fractional_ideal(R, ideal(R, 2, R(1 + a)))
    test_pseudo_remainder(R, K, I, K(2))

    kt, t = rational_function_field(GF(5), "t")
    K, a = function_field(polynomial(kt, [-t^3 - t - 1, 0, 1]))
    R = finite_maximal_order(K)
    I = fractional_ideal(ideal(R, t, R(a - 1)))
    test_pseudo_remainder(R, K, I, K(t))
    Rinf = infinite_maximal_order(K)
    test_pseudo_remainder(Rinf, K, K(inv(t))*Rinf, K(inv(t)))
  end
end

@testset "embedded quotient validation" begin
  M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
  for N in (Hecke.embedded_module(ZZ, QQ, QQ[2 0]),
            Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3]))
    @test_throws ArgumentError Hecke.quotient_embedded_module(M, N)
  end
  larger = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0])
  incompatible = Hecke.embedded_module(ZZ, QQ, QQ[1 0 0])
  @test_throws ArgumentError Hecke.quotient_embedded_module(M, larger)
  @test_throws ArgumentError Hecke.quotient_embedded_module(M, incompatible)
end

@testset "residue quotient validation" begin
  M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
  p = ZZ(3)
  free_part = Hecke.embedded_module(ZZ, QQ, QQ[1 0])
  higher_torsion = Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 9])
  larger = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0; 0 1])
  incompatible = Hecke.embedded_module(ZZ, QQ, QQ[3 0 0; 0 3 0])
  for N in (free_part, higher_torsion)
    @test_throws ArgumentError Hecke.quotient_vector_space(M, N, p)
  end
  @test_throws ArgumentError Hecke.quotient_vector_space(M, larger, p)
  @test_throws ArgumentError Hecke.quotient_vector_space(M, incompatible, p)
  for q in (ZZ(0), ZZ(1), ZZ(9))
    @test_throws ArgumentError Hecke.quotient_vector_space(M, M, q)
  end
  _, t = polynomial_ring(QQ, "t")
  @test_throws ArgumentError Hecke.quotient_vector_space(M, M, t)
end
