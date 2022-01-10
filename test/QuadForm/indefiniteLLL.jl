@testset "indefiniteLLL" begin
    
    ######################################################
    #                   complete_to_basis
    ######################################################
    n = 5 
    m = 4

    L = MatrixSpace(ZZ,n,m)
    S = MatrixSpace(ZZ,3,4)
    w = L([ 0 2  3  0 ; -5 3 -5 -5; 4 3 -5  4; 1 2 3 4; 0 1 0 0])
    v = S([ 0 2  3  0; -5 3 -5 -5; 4 3 -5  4])
    
    x = Hecke.complete_to_basis(w)
    y = Hecke.complete_to_basis(v)

    @test x[:,ncols(x)] == w[:,ncols(w)]
    @test det(x) == 1 || det(x) == -1

    @test y[:,ncols(y)] == v[:,ncols(v)]
    @test det(y) == 1 || det(y) == -1

    ######################################################
    #                   ker_mod_p
    ######################################################

    p1 = 3
    p2 = 4

    rank1, U1 = Hecke.ker_mod_p(v,p1)
    rank2, U2 = Hecke.ker_mod_p(w,p2)

    v_mod_p = change_base_ring(ResidueRing(ZZ,p1),v)
    w_mod_p = change_base_ring(ResidueRing(ZZ,p2),w)

    if (rank1 != 0)
        u1 = change_base_ring(ResidueRing(ZZ,p1),U1[:,1:rank1])
        for i = 1:rank1
            @test v_mod_p*u1[:,i] == 0
        end
    end

    if (rank2 != 0)
        u2 = change_base_ring(ResidueRing(ZZ,p2),U2[:,1:rank2])
        for i = 1:rank2
            @test w_mod_p*u2[:,i] == 0
        end
    end

    
    ######################################################
    #              quadratic_form_solve_triv
    ######################################################

    M = MatrixSpace(ZZ,2,2)
    G = M([1 2; 2 3])
    v = Hecke.quadratic_form_solve_triv(G)

    if (length(v) == 2)
        @test v == (G,one(parent(G)))
    elseif (length(v) == 3)
        @test v[2][:,1] == v[3]
        @test v[3]' * G * v[3] == 0
    else
        @test v'*G*v == 0
    end
    
end