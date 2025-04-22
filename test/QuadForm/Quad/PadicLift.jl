@testset "PadicLift" begin
  G = matrix(residue_ring(ZZ, 8)[1], 3, 3, [4,0,0, 0,2,1, 0,1,2])
  @test (2, 0, 2) == Hecke._last_block_index(G, 2)

  # We want to test for small and big residue rings
  for RR in [Int, ZZ]
    R = residue_ring(ZZ, RR(3)^6)[1]
    F1 = matrix(R, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 1])
    F2 = matrix(R, 3, 3, [0, 1, 0, 1, 2, 2, 0, 2, 1])
    Flist = [F1,F2]
    G = matrix(R, 3, 3, [0, 1, 0, 1, 0, 0, 0, 0, 2])
    for F in Flist
      Flift = Hecke._hensel_qf_modular_odd(G, G, F, 1, 4)
      error = Flift*G*transpose(Flift) - G
      @test 4<=Hecke._min_val(error, 3)
    end

    k = Hecke.Native.finite_field(2)[1]
    Y = matrix(k, 3, 3, [0,0,1, 0,0,1, 1,1,0])
    b = [k(i) for i in [1, 0, 0]]
    g = [k(i) for i in [0, 1, 0]]
    X = Hecke._solve_X(Y, b, g)
    @test Y == X + transpose(X)
    for i in 1:3
      @test b[i] == X[i,i] + sum([X[i,j]*g[j] for j in 1:3])
    end
    for X in Hecke._solve_X_ker(Y, b, g)
      @test all(0 == X[i,i] + sum([X[i,j]*g[j] for j in 1:3]) for i in 1:3)
    end

    Y = matrix(R, 3, 3, [0,0,1, 0,0,1, 1,1,0])
    b = [R(i) for i in [1, 0, 0]]
    g = [R(i) for i in [0, 1, 0]]
    gk = [k(i) for i in [0, 1, 0]]
    for X in Hecke._solve_X_ker(Y, b, g)
      @test all(0 == X[i,i] + sum([X[i,j]*gk[j] for j in 1:3]) for i in 1:3)
    end

    R = residue_ring(ZZ, ZZ(3)^5)[1]
    G = diagonal_matrix([R(i) for i in [3^2,1,1]])
    Z = G + matrix(R, 3, 3, [0,3^2,0, 3^2,0,0, 0,0,3])
    F = matrix(R, 3, 3, [1,0,0, 0,0,1, 0,1,0])
    Fn = @inferred Hecke._hensel_qf(Z, G, F, 1, 4, 3)
    @test(4<=Hecke._min_val(Z - F*G*transpose(F),3))

    p = ZZ(3)
    R = residue_ring(ZZ,p^7)[1]
    G = matrix(R, 6, 6, [0, 243, 0, 0, 0, 0, 243, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0])
    F = matrix(R, 6, 6, [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 1, 2, 1, 0, 0, 0, 2, -1, 6, 3, 0, 1, 1, 9, 3, 6, 1, 0])
    Flift = Hecke.hensel_qf(G, F, 1, 6, p)
    @test Hecke._min_val(Flift*G*transpose(Flift)-G, p ) >= 6

    p = ZZ(2)
    R = residue_ring(ZZ,p^10)[1]
    U = matrix(R, 2, 2,[0, 1, 1 ,0])
    V = matrix(R, 2, 2,[2, 1, 1 ,2])
    G = diagonal_matrix([2*U, 2*U, V])
    F = matrix(R, 6, 6,[1, 0, 0, 0, 0, 0,
                        1, 1, 1, 1, 0, 0,
                        1, 0, 1, 0, 0, 0,
                        1, 0, 0, 1, 0, 0,
                        1, 0, 0, 0, 1, 1,
                        0, 0, 0, 1, 0, 1])
    Fl = @inferred Hecke.hensel_qf(G, F, 1, 6, p )
    @test 10<=Hecke._min_val(Fl*G*transpose(Fl)-G, p)


    p = ZZ(2)
    R = residue_ring(ZZ,p^10)[1]
    G = matrix(R, 4, 4,[0,1,0,0,
                        1,0,0,0,
                        0,0,1,0,
                        0,0,0,5])
    F = matrix(R, 4, 4, [1, 0, 0, 0,
                        1, 1, 1, 1,
                        1, 0, 0, 1,
                        1, 0, 1, 0])
    Fl = @inferred Hecke. _hensel_qf_modular_even(G, G, F, 1, 4)
    Er = Fl*G*transpose(Fl) - G
    @test 4<=Hecke._min_val(Er,2)
    @test 5<=Hecke._min_val(diagonal(Er),p)
    F = matrix(R, 4, 4, [0, 1, 0, 0,
                         1, 1, 1, 1,
                         0, 1, 1, 0,
                         0, 1, 0, 1])
    Fl = @inferred Hecke. _hensel_qf_modular_even(G, G, F, 1, 4)
    Er = Fl*G*transpose(Fl) - G
    @test 4<=Hecke._min_val(Er,2)
    @test 5<=Hecke._min_val(diagonal(Er),p)

    G = matrix(R, 4, 4, [2, 1, 0, 0,
                         1, 2, 0, 0,
                         0, 0, 3, 0,
                         0, 0, 0, 7])
    F = matrix(R, 4, 4, [1, 0, 0, 0,
                         1, 1, 0, 0,
                         0, 0, 0, 1,
                         0, 0, 1, 0])
    Fl = @inferred Hecke._hensel_qf_modular_even(G, G, F, 1, 5)
    Er = Fl*G*transpose(Fl) - G
    @test 5<=Hecke._min_val(Er, 2)
    @test 6<=Hecke._min_val(diagonal(Er), p)

    Z = G + identity_matrix(R, 4)*2^2
    Fl = @inferred Hecke. _hensel_qf_modular_even(Z, G, F, 1, 5)
    Er = Fl*G*transpose(Fl) - Z
    @test 5<=Hecke._min_val(Er,2)
    @test 6<=Hecke._min_val(diagonal(Er),p)

    R = residue_ring(ZZ, ZZ(2)^5)[1]
    G = matrix(R, 3, 3, [2, 1, 0,
                         1, 2, 0,
                         0, 0, 7])
    F = matrix(R, 3, 3, [0, 1, 0,
                         1, 1, 0,
                         0, 0, 1])
    Fl = @inferred Hecke. _hensel_qf_modular_even(G, G, F, 1, 8)
    Er = Fl*G*transpose(Fl) - G
    @test 8<=Hecke._min_val(Er, p)
    @test 9<=Hecke._min_val(diagonal(Er), p)

    G = matrix(R, 3, 3, [4,0,0,
                         0,2,1,
                         0,1,2])
    @test ([1, 2], [2, 0]) == @inferred Hecke._block_indices_vals(G, 2)
  end
end
