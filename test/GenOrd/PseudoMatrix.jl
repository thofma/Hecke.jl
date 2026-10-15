@testset "Pseudo-matrices over generic orders" begin
  function test_genord_pseudo_matrix(O, a, c, I, J)
    K = Hecke.field(O)
    R = Hecke.coefficient_ring(O)
    c0 = R(coeff(c, 0))
    U = fractional_ideal(ideal(O, one(O)))
    A = fractional_ideal(I)
    B = fractional_ideal(J)

    @testset "Fractional ideal remainders" begin
      F = fractional_ideal(I, c0)
      F2 = fractional_ideal(c0*I, c0^2)
      @test F == F2
      for L in (A, F, inv(A), U), x in (zero(K), one(K), a, (a + 1)//c^2)
        r = mod(x, L)
        @test parent(r) === K
        @test x - r in L
        @test mod(r, L) == r
        for b in basis(L)
          @test mod(x + b, L) == r
          @test mod(x - c*b, L) == r
        end
      end
      for x in (a, (a + 1)//c^2)
        @test mod(x, F) == mod(x, F2)
      end
      @test_throws ArgumentError mod(zero(K), fractional_ideal(ideal(O, zero(O))))
      @test_throws ArgumentError mod(one(base_field(K)), F)
      @test_throws ArgumentError mod(zero(O), ideal(O, zero(O)))
    end

    @testset "Idempotents" begin
      for (L, N) in ((I, J), (J, I), (ideal(O, zero(O)), ideal(O, one(O))),
                     (ideal(O, one(O)), ideal(O, zero(O))))
        e, f = idempotents(L, N)
        @test parent(e) === O
        @test parent(f) === O
        @test iszero(L) ? iszero(e) : e in L
        @test iszero(N) ? iszero(f) : f in N
        @test e + f == one(O)
      end
      @test_throws ArgumentError idempotents(I, I)

      # The coordinates of 1 need not be the first standard basis vector.
      T = identity_matrix(base_field(K), degree(O))
      T[1, 2] = one(base_field(K))
      O2 = order(O, T, one(base_field(K)))
      @test !isone(first(basis(O2)))
      L, N = ideal(O2, O2(c)), ideal(O2, O2(c + 1))
      e, f = idempotents(L, N)
      @test e in L && f in N && e + f == one(O2)
      @test_throws ArgumentError idempotents(I, L)
    end

    # Expand the pseudo-generators over the coefficient PID to verify module
    # preservation independently of the pseudo-HNF algorithm.
    function expand_pseudo_matrix(P)
      d = degree(O)
      E = zero_matrix(base_field(K), d*nrows(P), d*ncols(P))
      for i in 1:nrows(P), (j, b) in enumerate(basis(coefficient_ideals(P)[i]))
        for k in 1:ncols(P)
          v = coordinates(K(b)*Hecke.matrix(P)[i, k], O)
          for l in 1:d
            E[(i - 1)*d + j, (k - 1)*d + l] = v[l]
          end
        end
      end
      return Hecke.integral_split(E, R)
    end

    @testset "Pseudo-HNF and transformations" begin
      inputs = (
        (K[1 1; 1 -1], [A, U]),
        (K[0 0 0; c a 1; 1 1 c; c + 1 a + 1 c], [U, A, U, B]),
        (K[0 c c 0; 0 1 1 0; 0 0 0 1], [A, U, B]),
        (K[0 a c], [inv(c)*A]),
        (zero_matrix(K, 2, 3), [A, B]),
        (zero_matrix(K, 0, 2), typeof(A)[]),
        (zero_matrix(K, 2, 0), [A, B]),
        (zero_matrix(K, 0, 0), typeof(A)[]),
      )
      for (M, C) in inputs
        P = pseudo_matrix(O, M, C)
        original = deepcopy(P)
        @test base_ring(P) === O
        @test P.base_ring === O
        @test base_ring(original) === O
        @test base_ring_type(typeof(P)) === typeof(O)
        @test base_ring(sub(P, 1:0, 1:ncols(P))) === O
        @test base_ring(vcat(P, P)) === O
        @test base_ring(hcat(P, P)) === O
        E, d = expand_pseudo_matrix(P)
        for shape in (:upperright, :lowerleft)
          H, V = pseudo_hnf_with_transform(P, shape)
          @test P == original
          @test base_ring(H) === O
          @test Hecke.matrix(H) == V*Hecke.matrix(P)
          @test !iszero(det(V))
          @test H == pseudo_hnf(P, shape)
          @test Hecke._spans_subset_of_pseudohnf(P, H; shape)
          F, e = expand_pseudo_matrix(H)
          @test Hecke._hnf(e*E, shape) == Hecke._hnf(d*F, shape)
          pivots = Int[]
          for i in 1:nrows(H)
            v = Hecke.matrix(H)[i, :]
            p = shape === :upperright ? findfirst(!iszero, v) : findlast(!iszero, v)
            if p === nothing
              push!(pivots, shape === :upperright ? ncols(H) + 1 : 0)
            else
              @test isone(v[p])
              push!(pivots, p)
            end
          end
          @test issorted(pivots)
        end
      end
      @test pseudo_matrix(K[1;;], [I]) == pseudo_matrix(O, K[1;;], [A])
      @test base_ring(pseudo_matrix(K[1;;], [I])) === O
      @test_throws ArgumentError pseudo_matrix(zero_matrix(K, 0, 1), typeof(A)[])
      @test_throws ArgumentError pseudo_matrix(O, K[1;;], typeof(A)[])
    end
  end

  @testset "Number-field order over ZZ" begin
    K, a = quadratic_field(-5)
    O = Hecke.maximal_order(Hecke.GenOrd(ZZ, K))
    test_genord_pseudo_matrix(O, a, K(2), ideal(O, 2, O(1 + a)), ideal(O, 3))
  end

  for k in (GF(5), QQ)
    kt, t = rational_function_field(k, :t; cached = false)
    K, a = function_field(polynomial(kt, [-t^3 - t - 1, 0, 1]); cached = false)
    @testset "Finite function-field order over $k" begin
      O = finite_maximal_order(K)
      test_genord_pseudo_matrix(O, a, K(t), ideal(O, t, O(a - 1)), ideal(O, t + 1))
    end
    @testset "Infinite function-field order over $k" begin
      O = infinite_maximal_order(K)
      test_genord_pseudo_matrix(O, K(last(basis(O))), K(1//t),
                               ideal(O, O(1//t)), ideal(O, O(1 + 1//t)))
    end
  end
end
