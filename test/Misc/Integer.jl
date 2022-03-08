@testset "Integer" begin
  @testset "range" begin

    r04 = fmpz(0):fmpz(4)
    r026 = fmpz(0):fmpz(2):fmpz(6)
    zlarge = fmpz(13)^100
    zjump = fmpz(11)^100
    rlarge = -zlarge:zlarge
    rlargejumps = -zlarge:zjump:zlarge

    @test fmpz(0):4 == 0:fmpz(4) == r04
    @test fmpz(0):2:6 == 0:2:fmpz(6) == 0:fmpz(2):6 == r026
    @test typeof(fmpz(0):4) == typeof(0:fmpz(4)) == typeof(r04)
    @test typeof(fmpz(0):fmpz(2):6) == typeof(0:fmpz(2):fmpz(6)) == typeof(0:fmpz(2):6) == typeof(r026)

    @test collect(r04) == fmpz[0, 1, 2, 3, 4]
    @test collect(r026) == fmpz[0, 2, 4, 6]
    @test collect(fmpz(-2):fmpz(5):fmpz(21)) == fmpz[-2, 3, 8, 13, 18]
    @test collect(fmpz(3):fmpz(-2):fmpz(-4)) == fmpz[3, 1, -1, -3]

    @test length(r04) == 5
    @test length(r026) == 4
    @test length(fmpz(-2):fmpz(5):fmpz(21)) == 5
    @test length(fmpz(3):fmpz(-2):fmpz(-4)) == 4

    # Julia assumes `length` to return an Integer, so if we want several base
    # functions to work, that should better be the case.
    @test length(r04) isa Integer
    @test length(r026) isa Integer
    @test length(rlarge) isa Integer
    @test length(rlargejumps) isa Integer

    @test r04[4] == r04[end-1] == 3
    @test r026[3] == r026[end-1] == 4
    @test rlarge[2zlarge] == rlarge[end-1] == rlarge[end-fmpz(1)] == zlarge - 1
    @test rlargejumps[2] == -zlarge + zjump
    @test rlargejumps[end] == zlarge - 2zlarge % zjump

    @test range(fmpz(0); step=2, stop=6) == fmpz(0):fmpz(2):fmpz(6)
    @test range(0; step=fmpz(2), stop=6) == fmpz(0):fmpz(2):fmpz(6)
    @test range(fmpz(0); step=2, length=4) == fmpz(0):fmpz(2):fmpz(6)
    @test VERSION >= v"1.7.0" && range(; stop=fmpz(0), length=3) == fmpz(-2):fmpz(0)

    @test 1 .+ r04 == fmpz(1):fmpz(5)
    @test fmpz(1) .+ r04 == fmpz(1):fmpz(5)
    @test fmpz(1) .+ (0:4) == fmpz(1):fmpz(5)
    @test 2 .* r04 == fmpz(0):fmpz(2):fmpz(8)
    @test fmpz(2) .* r04 == fmpz(0):fmpz(2):fmpz(8)
    @test 2 .* (0:4) == fmpz(0):fmpz(2):fmpz(8)

    @test mod(fmpz(7), r04) == fmpz(2)
    @test mod(7, r04) == 2
    @test mod(7, fmpz(10):fmpz(14)) == 12

    @test all(x -> x in r04, rand(r04, 5))
    @test all(x -> x in fmpz(0):fmpz(10):fmpz(100), rand(fmpz(0):fmpz(10):fmpz(100), 5))
    @test all(x -> x in rlarge, rand(rlarge, 20))
    @test all(x -> x in rlargejumps, rand(rlargejumps, 20))
  end
end
