
@testset "Generic Group" begin
    @testset "Subgroups from generators" begin
        G, = generic_group([1, -1, im, -im], *)
        for (S, expected) in [([G[2]], [one(G), G[2]]),
                              ([G[3]], collect(G)),
                              ([G[3], G[3]], collect(G)),
                              (elem_type(G)[], [one(G)]),
                              ([one(G)], [one(G)]),
                              (reverse(collect(G)), collect(G))]
            H, mH = sub(G, S)
            @test order(H) == length(expected)
            @test domain(mH) === H
            @test codomain(mH) === G
            @test Set(mH(h) for h in H) == Set(expected)
            @test mH(one(H)) == one(G)
            @test all(mH(g*h) == mH(g)*mH(h) for g in H, h in H)
            @test all(preimage(mH, mH(h)) == h for h in H)
        end

        G = small_group(6, 1)
        H, mH = sub(G, gens(G))
        @test order(H) == order(G)
        @test Set(mH(h) for h in H) == Set(G)
        @test all(mH(g*h) == mH(g)*mH(h) for g in H, h in H)

        K, = generic_group([1, -1], *)
        @test_throws ArgumentError sub(G, [one(K)])
    end

    @testset "Subgroups from all elements" begin
        G, = generic_group([1, -1, im, -im], *)
        for S in [[one(G)], [G[2], one(G)], reverse(collect(G))]
            H, mH = @inferred sub(G, S; complete = true)
            @test order(H) == length(S)
            @test [mH(h) for h in H] == S
            @test mH(one(H)) == one(G)
            @test all(mH(g*h) == mH(g)*mH(h) for g in H, h in H)
        end
    end

    @testset "QuotientGroup" begin
        @test Hecke.quotient_indx(1,1) == [(1,1)]
        @test Hecke.quotient_indx(2,1) == [(1,1), (2,1)]
        @test Hecke.quotient_indx(3,1) == [(1,1), (3,1)]
        @test Hecke.quotient_indx(4,1) == [(1,1), (2,1), (4,1)]
        @test Hecke.quotient_indx(4,2) == [(1,1), (2,1), (2,1), (2,1), (4,2)]
        @test Hecke.quotient_indx(5,1) == [(1,1), (5,1)]
        @test Hecke.quotient_indx(6,1) == [(1,1), (2,1), (6,1)]
        @test Hecke.quotient_indx(6,2) == [(1,1), (2,1), (3,1), (6,2)]
        @test Hecke.quotient_indx(7,1) == [(1,1), (7,1)]
        @test Hecke.quotient_indx(8,1) == [(1,1), (2,1), (4,1), (8,1)]
        @test Hecke.quotient_indx(8,2) == [(1,1), (2,1), (2,1), (2,1), (4,1), (4,1), (4,2), (8,2)]
        @test Hecke.quotient_indx(8,3) == [(1,1), (2,1), (2,1), (2,1), (4,2), (8,3)]
        @test Hecke.quotient_indx(8,4) == [(1,1), (2,1), (2,1), (2,1), (4,2), (8,4)]
        @test Hecke.quotient_indx(8,5) == [(1,1), (2,1), (2,1), (2,1), (2,1), (2,1), (2,1), (2,1), (4,2), (4,2), (4,2), (4,2), (4,2), (4,2), (4,2), (8,5)]
        @test Hecke.quotient_indx(9,1) == [(1,1), (3,1), (9,1)]
        @test Hecke.quotient_indx(9,2) == [(1,1), (3,1), (3,1), (3,1), (3,1), (9,2)]
        @test Hecke.quotient_indx(10,1) == [(1,1), (2,1), (10,1)]
        @test Hecke.quotient_indx(10,2) == [(1,1), (2,1), (5,1), (10,2)]
        @test Hecke.quotient_indx(11,1) == [(1,1), (11,1)]
        @test Hecke.quotient_indx(12,1) == [(1,1), (2,1), (4,1), (6,1), (12,1)]
        @test Hecke.quotient_indx(22,1) == [(1,1), (2,1), (22,1)]
        @test Hecke.quotient_indx(32,15) == [(1,1), (2,1), (2,1), (2,1), (4,1), (4,1), (4,2), (8,2), (8,3), (8,4), (16,4), (32,15)]
        @test Hecke.quotient_indx(42,1) == [(1,1), (2,1), (3,1), (6,2), (42,1)]
        @test Hecke.quotient_indx(52,3) == [(1,1), (2,1), (4,1), (52,3)]
        @test Hecke.quotient_indx(60,5) == [(1,1), (60,5)]
    end

    @testset "derived series" begin
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(1,1))] == [(1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(8,3))] == [(8,3), (2,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(18,1))] == [(18,1), (9,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(24,5))] == [(24,5), (3,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(24,6))] == [(24,6), (6,2), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(24,10))] == [(24,10), (2,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(27,4))] == [(27,4), (3,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(36,10))] == [(36,10), (9,2), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(38,2))] == [(38,2), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(40,13))] == [(40,13), (5,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(43,1))] == [(43,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(46,1))] == [(46,1), (23,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(48,37))] == [(48,37), (6,2), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(51,1))] == [(51,1), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(54,14))] == [(54,14), (27,5), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(56,13))] == [(56,13), (1,1)]
        @test [tuple(Hecke.find_small_group(i[1])[1]...) for i in Hecke.derived_series(Hecke.small_group(59,1))] == [(59,1), (1,1)]
    end

    @testset "psylow" begin
        G,AtoG,GtoA = Hecke.generic_group([1, -1, im, -im], *)
        @test order(sylow_subgroup(G,2)[1]) == 4
        @test order(sylow_subgroup(G,3)[1]) == 1
        @test_throws ErrorException sylow_subgroup(G,10)
    end

    @testset "exponent" begin
        for (id, e) in [((1, 1), 1), ((4, 1), 4), ((4, 2), 2), ((8, 5), 2)]
            G = small_group(id...)
            @test e == @inferred exponent(G)
            @test all(isone(g^e) for g in G)
        end

        # The exponent need not be the order of an element.
        G = small_group(6, 1)
        @test maximum(order(g) for g in G) == 3
        @test 6 == @inferred exponent(G)
        @test all(isone(g^6) for g in G)

        G, = direct_product(small_group(4, 1), small_group(6, 1))
        @test 12 == @inferred exponent(G)
        @test all(isone(g^12) for g in G)
    end

    @testset "GrpGenToGrpAb" begin
        G,AtoG,GtoA = Hecke.generic_group([1, -1, im, -im], *)
        GrpAb, GtoGrpAb, GrpAbtoG = Hecke.gen_2_ab(G)
        @test GrpAb.snf == ZZ.([4])
        @test order(GtoGrpAb(G[1])) == 1
        @test order(GtoGrpAb(G[2])) == 2
        @test order(GtoGrpAb(G[3])) == 4
        @test order(GtoGrpAb(G[4])) == 4

        @test Hecke.gen_2_ab(small_group(4,2))[1].snf == ZZ.([2, 2])
        @test Hecke.gen_2_ab(small_group(8,2))[1].snf == ZZ.([2, 4])
        @test Hecke.gen_2_ab(small_group(58,2))[1].snf == ZZ.([58])
        @test Hecke.gen_2_ab(small_group(56,13))[1].snf == ZZ.([2, 2, 14])
        @test Hecke.gen_2_ab(small_group(60,13))[1].snf == ZZ.([2, 30])
        @test Hecke.gen_2_ab(small_group(54,15))[1].snf == ZZ.([3, 3, 6])

    end
    @testset "Trivia" begin
        G,AtoG,GtoA = Hecke.generic_group([1, -1, im, -im], *)
        @test one(G) == id(G)
    end
end
