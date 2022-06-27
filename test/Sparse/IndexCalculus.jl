@testset "disclog" begin
    function cryptoprime(N)
        #return a Prime p with N digits. s.t (p-1)/2 is prime
        p = rand(fmpz(10)^(N-1):fmpz(10)^N)
        while true
            p = next_prime(p+1)
            !isprime(div(p-1,2)) || return p
        end 
    end 
    
    for i = 10:20
        pr = cryptoprime(15)
        F = GF(pr)
        a = primitive_elem(F, false)
        b = rand(F)
        c = rand(F)
        g1, _ = Hecke.IdxCalc(a, b)
        g2, _ = Hecke.IdxCalc(a, c)
        @test a^g1==b
        @test a^g2==c
    end
end