@testset "SpaceCurves" begin
  @testset "Curves in projective space" begin
    P3, (X, Y, Z, W) = polynomial_ring(QQ, [:X, :Y, :Z, :W])
    # canonical genus 4 curve: quadric ∩ cubic in P^3. (Not the Fermat cubic:
    # on the quadric XW = YZ = P^1 x P^1 it becomes (s0^3 + s1^3)(t0^3 + t1^3),
    # nine lines. The extra term keeps the rational point (1, -1, 1, -1) and
    # makes the curve irreducible.)
    Q = X*W - Y*Z
    C = X^3 + Y^3 + Z^3 + W^3 + (X - Z)*Y*W
    RS = _rs([Q, C], 100)
    @test RSM.genus(RS) == 4
    test_sanity(_computed(RS))
    sc = RSM.space_curve(RS)
    @test sc.equations == [Q, C]
    # a rational point of the space curve lies on the plane model
    p0 = matrix(QQ, 4, 1, [1, -1, 1, -1])
    @test iszero(Q(p0...)) && iszero(C(p0...))
    q = sc.projection * p0
    if !iszero(q[3, 1])
      @test iszero(RS.input_polynomial(q[1, 1] // q[3, 1], q[2, 1] // q[3, 1]))
    end
    # a given projection is used as is (and checked)
    A = matrix(QQ, [1 0 0 1; 0 1 0 0; 0 0 1 0])
    fA, AA = RSM.plane_model([Q, C]; projection = A)
    @test total_degree(fA) == 6

    # a plane curve given projectively: same Jacobian as the affine equation
    P2, (u, v, w) = polynomial_ring(QQ, [:u, :v, :w])
    RSp = _rs([u^4 + v^4 - w^4], 200; model = :original)
    RSa = _rs(FAST_CURVES[9][2], 200; model = :original)        # g6: y^4 + x^4 - 1
    @test RSM.genus(RSp) == 3
    @test _period_matrices_isomorphic(RSM.small_period_matrix(RSa), RSM.small_period_matrix(RSp))

    # Not a complete intersection of two surfaces: needs an elimination
    # ideal, which only Oscar provides (refused here, with a hint to Oscar).
    if !RSM._elimination_available()
      for F in ([Q, C, X*Q + C], [Q, C, X^2 + Y^2 + Z^2 + 2*W^2])
        err = try _rs(F, 100); nothing catch e; e end
        @test err isa ArgumentError && occursin("Oscar", err.msg)
      end
    end

    # refused inputs
    @test_throws ArgumentError _rs([Q, X + 1], 100)            # not homogeneous
    @test_throws ArgumentError _rs([Q], 100)                   # a surface
    @test_throws ArgumentError _rs([X*Y, Z*W], 100)            # four lines
    @test_throws ArgumentError RSM.plane_model([Q, C]; projection = matrix(QQ, [1 0 0 0; 0 1 0 0; 1 1 0 0]))
  end
end
