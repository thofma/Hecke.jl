@testset "Integer" begin
  @testset "range" begin

    r04 = ZZRingElem(0):ZZRingElem(4)
    r026 = ZZRingElem(0):ZZRingElem(2):ZZRingElem(6)
    zlarge = ZZRingElem(13)^100
    zjump = ZZRingElem(11)^100
    rlarge = -zlarge:zlarge
    rlargejumps = -zlarge:zjump:zlarge

    @test ZZRingElem(0):4 == 0:ZZRingElem(4) == r04
    @test ZZRingElem(0):2:6 == 0:2:ZZRingElem(6) == 0:ZZRingElem(2):6 == r026
    @test typeof(ZZRingElem(0):4) == typeof(0:ZZRingElem(4)) == typeof(r04)
    @test typeof(ZZRingElem(0):ZZRingElem(2):6) == typeof(0:ZZRingElem(2):ZZRingElem(6)) == typeof(0:ZZRingElem(2):6) == typeof(r026)

    @test collect(r04) == ZZRingElem[0, 1, 2, 3, 4]
    @test collect(r026) == ZZRingElem[0, 2, 4, 6]
    @test collect(ZZRingElem(-2):ZZRingElem(5):ZZRingElem(21)) == ZZRingElem[-2, 3, 8, 13, 18]
    @test collect(ZZRingElem(3):ZZRingElem(-2):ZZRingElem(-4)) == ZZRingElem[3, 1, -1, -3]

    @test length(r04) == 5
    @test length(r026) == 4
    @test length(ZZRingElem(-2):ZZRingElem(5):ZZRingElem(21)) == 5
    @test length(ZZRingElem(3):ZZRingElem(-2):ZZRingElem(-4)) == 4

    # Julia assumes `length` to return an Integer, so if we want several base
    # functions to work, that should better be the case.
    @test length(r04) isa Integer
    @test length(r026) isa Integer
    @test length(rlarge) isa Integer
    @test length(rlargejumps) isa Integer

    @test r04[4] == r04[end-1] == 3
    @test r026[3] == r026[end-1] == 4
    @test rlarge[2zlarge] == rlarge[end-1] == rlarge[end-ZZRingElem(1)] == zlarge - 1
    @test rlargejumps[2] == -zlarge + zjump
    @test rlargejumps[end] == zlarge - 2zlarge % zjump

    @test range(ZZRingElem(0); step=2, stop=6) == ZZRingElem(0):ZZRingElem(2):ZZRingElem(6)
    @test range(0; step=ZZRingElem(2), stop=6) == ZZRingElem(0):ZZRingElem(2):ZZRingElem(6)
    @test range(ZZRingElem(0); step=2, length=4) == ZZRingElem(0):ZZRingElem(2):ZZRingElem(6)
    VERSION >= v"1.7" && @test range(; stop=ZZRingElem(0), length=3) == ZZRingElem(-2):ZZRingElem(0)

    @test 1 .+ r04 == ZZRingElem(1):ZZRingElem(5)
    @test ZZRingElem(1) .+ r04 == ZZRingElem(1):ZZRingElem(5)
    @test ZZRingElem(1) .+ (0:4) == ZZRingElem(1):ZZRingElem(5)
    @test 2 .* r04 == ZZRingElem(0):ZZRingElem(2):ZZRingElem(8)
    @test ZZRingElem(2) .* r04 == ZZRingElem(0):ZZRingElem(2):ZZRingElem(8)
    @test 2 .* (0:4) == ZZRingElem(0):ZZRingElem(2):ZZRingElem(8)

    @test mod(ZZRingElem(7), r04) == ZZRingElem(2)
    @test mod(7, r04) == 2
    @test mod(7, ZZRingElem(10):ZZRingElem(14)) == 12

    @test all(x -> x in r04, rand(r04, 5))
    @test all(x -> x in ZZRingElem(0):ZZRingElem(10):ZZRingElem(100), rand(ZZRingElem(0):ZZRingElem(10):ZZRingElem(100), 5))
    @test all(x -> x in rlarge, rand(rlarge, 20))
    @test all(x -> x in rlargejumps, rand(rlargejumps, 20))
  end
end
