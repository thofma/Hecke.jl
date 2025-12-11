@testset "Auxiliary" begin

  @testset "Weighted projective space" begin
    
    K = QQ

    wghts = [3,5,8,12,13]
    lambda = 12
    values = map(K, [0,34//4589,6//23,1,-7//2])
    image = [values[i]*lambda^wghts[i] for i in (1:length(wghts))]
    @test weighted_equality(values, image, wghts)

    @test @inferred weighted_reduction(image, wghts) ==  [0, 3105562731008915782481344, 
      1028562127914445898022660216566371312445952,
      7829078948476295033372631581424820715020840434928081930961883136,
     -5784350570423792583211668018672518864058132517697479844970637155487744]

    wghts = [4,20,8,12,10]
    lambda = -3
    values = map(K, [200,-5,0,0,-7])
    image = [values[i]*lambda^wghts[i] for i in (1:length(wghts))]
    @test @inferred weighted_equality(values, image, wghts)

    @test @inferred weighted_reduction(image, wghts) == values
    
    K, a = cyclotomic_field(8)

    wghts = [2,4,8,12]
    lambda = -3
    values = map(K, [a-12,31*a+3,a^2-5,-7])
    image = [values[i]*lambda^wghts[i] for i in (1:length(wghts))]
    @test @inferred weighted_equality(values, image, wghts)

    image = [image[i]+1 for i in (1:length(wghts))]
    @test !weighted_equality(values, image, wghts)

    K = GF(37, 2)
    a = gen(K)

    wghts = [2,4,8,12]
    lambda = -3
    values = map(K, [a-12,31*a+3,a^2-5,-7])
    image = [values[i]*lambda^wghts[i] for i in (1:length(wghts))]
    @test @inferred weighted_equality(values, image, wghts)
    @test !weighted_equality(values, map(K, [0,31*a+3,a^2-5,-7]), wghts)

  end

end
