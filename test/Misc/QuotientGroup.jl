using Test

@testset "quotients" begin
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
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(1,1))] == [(1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(8,3))] == [(8,3), (2,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(18,1))] == [(18,1), (9,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(24,5))] == [(24,5), (3,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(24,6))] == [(24,6), (6,2), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(24,10))] == [(24,10), (2,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(27,4))] == [(27,4), (3,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(36,10))] == [(36,10), (9,2), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(38,2))] == [(38,2), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(40,13))] == [(40,13), (5,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(43,1))] == [(43,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(46,1))] == [(46,1), (23,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(48,37))] == [(48,37), (6,2), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(51,1))] == [(51,1), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(54,14))] == [(54,14), (27,5), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(56,13))] == [(56,13), (1,1)]
        @test [Hecke.find_small_group(i[1]) for i in Hecke.derived_series(Hecke.small_group(59,1))] == [(59,1), (1,1)]
    end

    @testset "psylow" begin
        G,AtoG,GtoA = Hecke.generic_group([1, -1, im, -im], *)
        @test order(psylow_subgroup(G,2)[1]) == 4
        @test order(psylow_subgroup(G,3)[1]) == 1
        @test_throws ErrorException psylow_subgroup(G,10)
    end

    @testset "morphisms" begin
        G,AtoG,GtoA = generic_group([1, -1, im, -im], *)
        Hom = GrpGenToGrpGenMor(G,G,[G[1],G[1],G[1],G[1]])
        @test order(image(Hom)[1]) == 1
        @test order(kernel(Hom)[1]) == 4
        @test issurjective(Hom) == false
        @test isinjective(Hom) == false
        @test isbijective(Hom) == false

        Hom = GrpGenToGrpGenMor(G,G,[G[1],G[2],G[3],G[4]])
        @test order(image(Hom)[1]) == 4
        @test order(kernel(Hom)[1]) == 1
        @test issurjective(Hom) == true
        @test isinjective(Hom) == true
        @test isbijective(Hom) == true
    end



end
