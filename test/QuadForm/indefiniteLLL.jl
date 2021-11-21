@testset "indefiniteLLL" begin
    n = 5 
    m = 4

    L = MatrixSpace(ZZ,n,m)
    S = MatrixSpace(ZZ,3,4)
    w = L([ 0 2  3  0 ; -5 3 -5 -5; 4 3 -5  4; 1 2 3 4; 0 1 0 0])
    v = S([ 0 2  3  0; -5 3 -5 -5; 4 3 -5  4])
    
    x = completebasis(w)
    y = completebasis(v)

    @test x[:,m] == w[:,m]
    @test det(x) == 1 || det(x) == -1

    @test y[:,4] == v[:,4]
    @test det(y) == 1 || det(y) == -1
end