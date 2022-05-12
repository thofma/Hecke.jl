
@testset "Morphisms" begin
    @testset "Find Automorphisms" begin
        G, = generic_group([1, -1, im, -im], *)
        @test find_small_group(generic_group(automorphisms(G), *)[1])[1] == (2,1)
        @test find_small_group(generic_group(automorphisms(small_group(8,2)), *)[1])[1] == (8,3)
        @test find_small_group(generic_group(automorphisms(small_group(13,1)), *)[1])[1] == (12,2)
        @test find_small_group(generic_group(automorphisms(small_group(18,5)), *)[1])[1] == (48,29)
        @test find_small_group(generic_group(automorphisms(small_group(24,12)), *)[1])[1] == (24,12)
        @test find_small_group(generic_group(automorphisms(small_group(33,1)), *)[1])[1] == (20,5)
        @test find_small_group(generic_group(automorphisms(small_group(36,2)), *)[1])[1] == (12,5)
        @test find_small_group(generic_group(automorphisms(small_group(42,3)), *)[1])[1] == (36,12)

        @test length(automorphisms(small_group(27,3))) == 432

        for aut in automorphisms(small_group(25,2))
            @test is_bijective(aut)
        end

        for aut in automorphisms(small_group(34,2))
            @test is_bijective(aut)
        end

        G = small_group(16,4)
        auts = automorphisms(G)
        for aut in auts
            @test all([aut(g * h) == aut(g) * aut(h) for g in G for h in G]) == true
        end

        G = small_group(20,2)
        auts = automorphisms(G)
        for aut in auts
            @test all([aut(g * h) == aut(g) * aut(h) for g in G for h in G]) == true
        end

        G = small_group(39,1)
        auts = automorphisms(G)
        for aut in auts
            @test all([aut(g * h) == aut(g) * aut(h) for g in G for h in G]) == true
        end

        G = small_group(44,2)
        auts = automorphisms(G)
        for aut in auts
            @test all([aut(g * h) == aut(g) * aut(h) for g in G for h in G]) == true
        end
    end

    @testset "Find Morphisms" begin
        G, = generic_group([1, -1, im, -im], *)
        H = small_group(6,2)
        @test length(morphisms(G,H)) == 2

        @test length(morphisms(small_group(23,1), small_group(42,5))) == 1
        @test length(morphisms(small_group(24,4), small_group(24,4))) == 124
        @test length(morphisms(small_group(24,4), small_group(45,2))) == 1
        @test length(morphisms(small_group(12,2), small_group(6,1))) == 6
        @test length(morphisms(small_group(56,4), small_group(24,2))) == 8
        @test length(morphisms(small_group(24,2), small_group(56,4))) == 32
        @test length(morphisms(small_group(24,2), small_group(58,2))) == 2
        @test length(morphisms(small_group(32,2), small_group(60,2))) == 64
        @test length(morphisms(small_group(56,4), small_group(62,2))) == 4
        @test length(morphisms(small_group(36,2), small_group(63,2))) == 9

        G = small_group(16,3)
        morphs = morphisms(G, G)
        for mor in morphs
            @test all([mor(g * h) == mor(g) * mor(h) for g in G for h in G]) == true
        end

        G = small_group(48,3)
        H = small_group(58,2)
        morphs = morphisms(G, H)
        for mor in morphs
            @test all([mor(g * h) == mor(g) * mor(h) for g in G for h in G]) == true
        end

        G = small_group(50,2)
        H = small_group(61,1)
        morphs = morphisms(G, H)
        for mor in morphs
            @test all([mor(g * h) == mor(g) * mor(h) for g in G for h in G]) == true
        end
    end

    @testset "morphisms" begin
        G,AtoG,GtoA = generic_group([1, -1, im, -im], *)
        Hom = GrpGenToGrpGenMor(G,G,[G[1],G[1],G[1],G[1]])
        @test order(image(Hom)[1]) == 1
        @test order(kernel(Hom)[1]) == 4
        @test is_surjective(Hom) == false
        @test is_injective(Hom) == false
        @test is_bijective(Hom) == false

        Hom = GrpGenToGrpGenMor(G,G,[G[1],G[2],G[3],G[4]])
        @test order(image(Hom)[1]) == 4
        @test order(kernel(Hom)[1]) == 1
        @test is_surjective(Hom) == true
        @test is_injective(Hom) == true
        @test is_bijective(Hom) == true
    end
end
