@testset "Lattice" begin
  @testset "Graph" begin
    # first test the graph stuff
    G = Hecke.Graph{Int, Int}()
    append!(G, 1)
    @test haskey(G.degrees, 1)
    @test haskey(G.new_low_degrees, 1)
    @test G.degrees[1] == 0
    @test 1 in keys(G.edges)

    append!(G, 2)
    @test 2 in keys(G.edges)
    append!(G, (2, 3), 5)
    @test haskey(G.degrees, 2)
    @test haskey(G.new_low_degrees, 2)
    @test haskey(G.new_low_degrees, 3)
    @test G.degrees[2] == 1
    @test G.degrees[3] == 1
    @test 3 in keys(G.edges)
    @test 3 in keys(G.edges[2])
    @test 5 == G.edges[2][3]

    append!(G, (3, 4), 5)
    @test !(3 in keys(G.new_low_degrees))
    @test G.degrees[3] == 2

    append!(G, (5, 4), 5)

    # Now G looks like this:
    #
    #       4
    #      / \
    #     /   \
    # 1   3    5
    #     |
    #     2

    @test_throws ErrorException append!(G, 1)

    # Now delete 3
    delete!(G, 3)
    @test !(3 in keys(G.edges))
    @test !(3 in keys(G.edges[2]))
    @test G.degrees[2] == 0
    @test G.degrees[4] == 1
    @test 4 in keys(G.new_low_degrees)

    # Now add it again and restore G
    append!(G, (2, 3), 5)
    append!(G, (3, 4), 5)

    append!(G, (2, 4), 5)
    append!(G, (6, 5), 5)
    append!(G, (5, 7), 5)

    # Now G looks like this:
    #
    #       4      7
    #      / |\   /
    #     /  | \ /
    # 1   3  |  5
    #     |  /   \
    #     2       6

    # Find shortest path
    b, P = @inferred Hecke.find_shortest(G, 2, 4)
    @test b
    @test P == [4, 2]
    b, P = @inferred Hecke.find_shortest(G, 6, 4)
    @test b
    @test P == [4, 5, 6]
    b, P = @inferred Hecke.find_shortest(G, 1, 1)
    @test b
    @test P == [1]

    b, P = @inferred Hecke.find_shortest(G, 1, 2)
    @test !b

    b, P = @inferred Hecke.find_shortest(G, 3, 5)
    @test !b

    # Find something in the intersect
    b, P1, P2 = @inferred Hecke.find_common(G, 3, 5)
    @test b
    @test P1 == [4, 3]
    @test P2 == [4, 5]

    b, P1, P2 = @inferred Hecke.find_common(G, 2, 3)
    @test b
    @test P1 == [3, 2]
    @test P2 == [3]

    b, P1, P2 = @inferred Hecke.find_common(G, 1, 2)
    @test !b

    b, P1, P2 = @inferred Hecke.find_common(G, 2, 7)
    @test !b
  end

  @testset "Lattice of groups" begin
    # For testing don't use the global lattice
    L = Hecke.GrpAbLatticeCreate()
    G = abelian_group([3,3,4,5])
    H, mH = sub(G, [G[1]], true, L)
    Q, mQ = quo(G, [G[2]], true, L)

    b, M = @inferred Hecke.can_map_into(L, H, G)
    @test b
    @test M == mH.map
    @test_throws ErrorException H[1] + G[1] == 2*G[1]
    @test +(H[1], G[1], L) == 2*G[1]

    b, M = @inferred Hecke.can_map_into(L, H, Q)
    @test b
    @test M == mH.map * mQ.map
    @test_throws ErrorException H[1] + Q[1]
    @test +(H[1], Q[1], L) == 2*Q[1]

    b, M = @inferred Hecke.can_map_into(L, Q, H)
    @test !b

    HH, mHH = sub(G, [G[2]], true, L)
    b, GG, MH, MHH = @inferred Hecke.can_map_into_overstructure(L, H, HH)
    @test b
    @test GG == G
    @test MH == mH.map
    @test MHH == mHH.map
    @test_throws ErrorException H[1] + HH[1]
    @test +(H[1], HH[1], L) == G[1] + G[2]

    HHH, mHHH = sub(H, [H[1]], true, L)
    b, GG, MHHH, MHH = @inferred Hecke.can_map_into_overstructure(L, HHH, HH)
    @test b
    @test GG == G
    @test_throws ErrorException HHH[1] + HH[1]
    @test +(HHH[1], HH[1], L) == G[1] + G[2]

    Q2, mQ2 = quo(G, [G[1]], true, L)
    b, GG, MHHH, MHH = @inferred Hecke.can_map_into_overstructure(L, Q, Q2)
    @test !b

    b, GG, _, _ = @inferred Hecke.can_map_into_overstructure(L, Q, Q)
    @test b
    @test GG === Q
  end
end
