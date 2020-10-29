@testset "IntegralForms" begin

  @testset "Discriminant" begin
    A = [i for i in -12:13]
    C = [1,1,0,0,1,1,0,0,1,1,0,0,0,1,0,0,1,1,0,0,1,1,0,0,1,1]
    @test isdiscriminant.(A) == C
  end
  
  @testset "Conductor" begin
    A = [5, 8, 12, 13, 17, 20, 21, 24, 28, 29, 32, 33, 37, 40, 41, 44, 45, 48,
         52, 53, 56, 57, 60, 61, 65, 68, 69, 72, 73, 76, 77, 80, 84, 85, 88,
         89, 92, 93, 96, 97, 101, 104, 105, 108, 109, 112, 113, 116, 117, 120,
         124, 125, 128, 129, 132, 133, 136, 137, 140, 141, 145, 148, 149, 152,
         153, 156, 157, 160, 161, 164, 165, 168, 172, 173, 176, 177, 180, 181,
         184, 185, 188, 189, 192, 193, 197, 200, 201, 204, 205, 208, 209, 212,
         213, 216, 217, 220, 221, 224, 228, 229, 232, 233, 236, 237, 240, 241,
         244, 245, 248, 249, 252, 253, 257, 260, 261, 264, 265, 268, 269, 272,
         273, 276, 277, 280, 281, 284, 285, 288, 292, 293, 296, 297, 300, 301,
         304, 305, 308, 309, 312, 313, 316, 317, 320, 321, 325, 328, 329, 332,
         333, 336, 337, 340, 341, 344, 345, 348, 349, 352, 353, 356, 357, 360,
         364, 365, 368, 369, 372, 373, 376, 377, 380, 381, 384, 385, 388, 389,
         392, 393, 396, 397, 401, 404, 405, 408, 409, 412, 413, 416, 417, 420,
         421, 424, 425, 428, 429, 432, 433, 436, 437, 440, 444, 445, 448, 449,
         452, 453, 456, 457, 460, 461, 464, 465, 468, 469, 472, 473, 476, 477,
         480, 481, 485, 488, 489, 492, 493, 496, 497, 500, 501, 504, 505, 508,
         509, 512, 513, 516, 517, 520, 521, 524, 525, 528, 532, 533, 536, 537,
         540, 541, 544, 545, 548, 549, 552, 553, 556, 557, 560, 561, 564, 565,
         568, 569, 572, 573, 577, 580, 581, 584, 585, 588, 589, 592, 593, 596,
         597, 600, 601, 604, 605, 608, 609, 612, 613, 616, 617, 620, 621, 624,
         628, 629, 632, 633, 636, 637, 640, 641, 644, 645, 648, 649, 652, 653,
         656, 657, 660, 661, 664, 665, 668, 669, 672, 673, 677, 680, 681, 684,
         685, 688, 689, 692, 693, 696, 697, 700, 701, 704, 705, 708, 709, 712,
         713, 716, 717, 720, 721, 724, 725, 728, 732, 733, 736, 737, 740, 741,
         744, 745, 748, 749, 752, 753, 756, 757, 760, 761, 764, 765, 768, 769,
         772, 773, 776, 777, 780, 781, 785, 788, 789, 792, 793, 796, 797, 800,
         801, 804, 805, 808, 809, 812, 813, 816, 817, 820, 821, 824, 825, 828,
         829, 832, 833, 836, 837, 840, 844, 845, 848, 849, 852, 853, 856, 857,
         860, 861, 864, 865, 868, 869, 872, 873, 876, 877, 880, 881, 884, 885,
         888, 889, 892, 893, 896, 897, 901, 904, 905, 908, 909, 912, 913, 916,
         917, 920, 921, 924, 925, 928, 929, 932, 933, 936, 937, 940, 941, 944,
         945, 948, 949, 952, 953, 956, 957, 960, 964, 965, 968, 969, 972, 973,
         976, 977, 980, 981, 984, 985, 988, 989, 992, 993, 996, 997, 1000]
    Acond = [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1,
             1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3,
             1, 2, 1, 2, 3, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1,
             1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1,
             1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1,
             3, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3,
             5, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 1, 5, 1, 1, 1, 3, 4, 1, 2, 1, 1,
             1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1,
             7, 1, 3, 1, 1, 2, 9, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 6, 1, 2,
             1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 3, 2, 1,
             1, 1, 1, 1, 1, 2, 1, 10, 1, 3, 1, 1, 1, 8, 3, 2, 1, 1, 1, 1, 5, 4,
             2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1,
             1, 2, 1, 1, 3, 7, 1, 4, 1, 2, 1, 5, 1, 1, 11, 2, 1, 6, 1, 1, 1, 1,
             3, 2, 2, 1, 1, 1, 1, 7, 4, 1, 2, 1, 9, 1, 1, 1, 4, 3, 2, 1, 1, 1,
             1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 1, 4, 1, 2, 1, 1,
             1, 1, 1, 12, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1,
             1, 1, 1, 3, 8, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10, 3, 2,
             1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 8, 7, 2, 3, 1, 1, 13, 4, 1,
             2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1,
             4, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1,
             1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 2, 1, 11, 1, 9, 1, 4, 1, 14, 3, 1,
             1, 1, 1, 2, 1, 2, 1, 5]
    @test conductor.(A) == Acond
  end

  @testset "FundamentalDiscriminant" begin
    @test isfundamental_discriminant(12) == true
    @test isfundamental_discriminant(-12) == false
    D =	[1, 5, 8, 12, 13, 17, 21, 24, 28, 29, 33, 37, 40, 41, 44, 53, 56, 57,
         60, 61, 65, 69, 73, 76, 77, 85, 88, 89, 92, 93, 97, 101, 104, 105,
         109, 113, 120, 124, 129, 133, 136, 137]
    @test all(isfundamental_discriminant, D)
    D =	map(x -> -x, [3, 4, 7, 8, 11, 15, 19, 20, 23, 24, 31, 35, 39, 40, 43,
                      47, 51, 52, 55, 56, 59, 67, 68, 71, 79, 83, 84, 87, 88,
                      91, 95, 103])
    @test all(isfundamental_discriminant, D)

    @test fundamental_discriminant(20) == 5
    @test fundamental_discriminant(-20) == -20
  end

  @testset "DefiniteForms" begin
    @test isnegative_definite(binary_quadratic_form(-2, 3, -2)) == true
    @test ispositive_definite(binary_quadratic_form(2, -3, 2)) == true
    @test isindefinite(binary_quadratic_form(1, 3, 1)) == true
    @test ispositive_definite(binary_quadratic_form(1, 3, 1)) == false
    @test isnegative_definite(binary_quadratic_form(1, 3, 1)) == false
  end

  @testset "Reduction" begin
  @test isreduced(binary_quadratic_form(1, 2, 3)) == false
  @test isreduced(binary_quadratic_form(2, 1, 3)) == true
  @test isreduced(binary_quadratic_form(1, -1, 1)) == false
  @test isreduced(binary_quadratic_form(1, 1, 1)) == true
  @test isreduced(binary_quadratic_form(-1, 2, 2)) == true
  # indefinite
  @test isreduced(binary_quadratic_form(1, 9, 4)) == false
  @test isreduced(binary_quadratic_form(1, 5, -1)) == true
  #@test reduce(binary_quadratic_form(195751, 37615, 1807)) == binary_quadratic_form(1, 1, 1)
  #@test reduce(binary_quadratic_form(33, 11, 5)) == binary_quadratic_form(5, -1, 27)
  #@test reduce(binary_quadratic_form(15, 0, 15)) == binary_quadratic_form(15, 0, 15)
  end

  #@testset "Composition" begin
  #@test reduce(compose(binary_quadratic_form(2 ,2, 1), binary_quadratic_form(5, 4, 1))) == binary_quadratic_form(1, 0, 1)
  #@test reduce(compose(binary_quadratic_form(1, 1, 6), binary_quadratic_form(1, 1, 6))) == binary_quadratic_form(1, 1, 6)
  #@test reduce(compose(binary_quadratic_form(2, -1, 3), binary_quadratic_form(2, -1, 3))) == binary_quadratic_form(2, 1, 3)
  #end

  @testset "Cycle" begin

    A1 = [binary_quadratic_form(1, 7, -6), binary_quadratic_form(6, 5, -2), binary_quadratic_form(2, 7, -3), binary_quadratic_form(3, 5, -4),
    binary_quadratic_form(4, 3, -4), binary_quadratic_form(4, 5, -3), binary_quadratic_form(3, 7, -2), binary_quadratic_form(2, 5, -6), binary_quadratic_form(6, 7, -1)]

    @test cycle(binary_quadratic_form(1,7,-6)) == A1

    A2 = [binary_quadratic_form(1, 8, -3), binary_quadratic_form(3, 4, -5), binary_quadratic_form(5, 6, -2), binary_quadratic_form(2, 6, -5),
    binary_quadratic_form(5, 4, -3), binary_quadratic_form(3, 8, -1)]

    @test cycle(binary_quadratic_form(1,8,-3)) == A2

    A3 = [binary_quadratic_form(14, 17, -2), binary_quadratic_form(2, 19, -5), binary_quadratic_form(5, 11, -14)]
    @test cycle(binary_quadratic_form(14, 17, -2)) == A3
  end

  @testset "CanSolve" begin
    @test can_solve(binary_quadratic_form(3,2,2), 28) == (true, (2, 2))
    @test can_solve(binary_quadratic_form(2,1,3), 3) == (true, (0, 1))
    @test can_solve(binary_quadratic_form(2,1,3), 5) == (false, (0, 0))
    @test can_solve(binary_quadratic_form(2,1,3), 6) == (true, (1, 1))
    @test can_solve(binary_quadratic_form(2,-1,3), 3) == (true, (0, 1))
    @test can_solve(binary_quadratic_form(2,-1,3), 5) == (false, (0, 0))
    @test can_solve(binary_quadratic_form(2,-1,3), 6) == (true, (-1, 1))
    @test can_solve(binary_quadratic_form(1,1,6), 3) == (false, (0, 0))
    @test can_solve(binary_quadratic_form(1,1,6), 5) == (false, (0, 0))
    @test can_solve(binary_quadratic_form(1,1,6), 6) == (true, (0, 1))
  end

  @testset "PrimeForm" begin
    f = prime_form(ZZ(17), ZZ(1237))
    @test discriminant(f) == 17 && f[1] == 1237
    f = prime_form(ZZ(12), ZZ(743))
    @test discriminant(f) == 12 && f[1] == 743
    f = prime_power_form(ZZ(117), ZZ(3), 2)
    @test discriminant(f) == 117 && f[1] == 9
  end

  @testset "Equivalent" begin
    f = binary_quadratic_form(fmpz(-1), fmpz(0), fmpz(3))
    g = Hecke.reduction(f)
    @test g[1] == -1 && g[2] == 2 && g[3] == 2
    g, T = Hecke.reduction_with_transformation(f)
    @test g[1] == -1 && g[2] == 2 && g[3] == 2
    @test T == matrix(FlintZZ, 2, 2, [-1, 1, 0, -1])
    @test Hecke._buchmann_vollmer_action(f, T) == g

    f = binary_quadratic_form(4, 4, 15)
    g = binary_quadratic_form(4, -4, 15)
    @test_broken isequivalent(f, g)

    f = binary_quadratic_form(33, 11, 5)
    #g = reduction(f)
    #@test g == binary_quadratic_form(5, -1, 27)
    #@test isequivalent(f, g)
    #@test !isequivalent(f, binary_quadratic_form(3, 4, 5))

    f = binary_quadratic_form(9, 8, -7)
    g = binary_quadratic_form(9, -8, -7)
    @test isequivalent(f, g, proper = false)
    @test !isequivalent(f, g, proper = true)

    f = binary_quadratic_form(0, 4, 2)
    g = binary_quadratic_form(2, 4, 0)
    @test isequivalent(f, g, proper = false)

    f = binary_quadratic_form(fmpz(3), fmpz(4), fmpz(-2))
    g = binary_quadratic_form(fmpz(-2), fmpz(4), fmpz(3))
    @test isequivalent(f, g)
    @test isequivalent(f, g, proper = false)

    f = binary_quadratic_form(2, -120, 1785)
    g = binary_quadratic_form(10, -120, 357)
    @test !isequivalent(f, g)
    @test !isequivalent(f, g, proper = false)
  end

  @testset "Automormorphism group" begin
    g = binary_quadratic_form(3, 1, -3)
    gens = automorphism_group_generators(g)
    @test all(T -> Hecke._action(g, T) == g, gens)
    @assert all(T -> abs(det(T)) == 1, gens)
    @assert any(T -> det(T) == -1, gens) # g is ambiguous
  end

  @testset "Misc" begin
    f = binary_quadratic_form(1, 8, -3)
    g, T = Hecke._tau(f)
    @test g == binary_quadratic_form(-1, 8, 3)
    @test g == Hecke._buchmann_vollmer_action(f, T)

    f = binary_quadratic_form(1, 8, -3)
    g, T = Hecke._rhotau(f)
    @test g == binary_quadratic_form(3, 4, -5)
    @test g == Hecke._buchmann_vollmer_action(f, T)

    f = binary_quadratic_form(1, 8, -3)
    g, T = Hecke._rho(f)
    @test g == binary_quadratic_form(-3, 4, 5)
    @test g == Hecke._buchmann_vollmer_action(f, T)
  end
end
