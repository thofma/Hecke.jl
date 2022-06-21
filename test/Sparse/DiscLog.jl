@testset "disclog" begin
    function rand_dec_prime(N) #returns prime numer of decimal length N
        lower = fmpz(10)^(N-1)
        upper = fmpz(10)^N
        p = rand(lower:upper)
        p = next_prime(p)
        if p >= upper
            return next_prime(lower)
        end
        return p
    end

    p = rand_dec_prime(20)
    F = GF(p)
    a = rand(F)
    while a == zero(F)
        a = rand(F)
    end
    g = rand(1:p-1)
    b = a^g
    log_, K = disc_log(a, b)
    @test log_ == Nothing || a^log_ == b 
end