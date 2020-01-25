using Test
using Hecke

# Some nearby primes 131, 137, 139.

my_prime = 131
K, a = wildanger_field(3, my_prime)
lp = prime_decomposition(maximal_order(K), my_prime)
P  = lp[1][1]

Kp, inj = Hecke.completion(K,P)
lif = Hecke.preimage_function(inj)


@testset "Completions: Wildanger_field(3,131), basic" begin

    my_prime = 131
    K, a = wildanger_field(3, my_prime)
    lp = prime_decomposition(maximal_order(K), my_prime)
    P  = lp[1][1]

    Kp, inj = Hecke.completion(K,P)
    lif = Hecke.preimage_function(inj)

    # Test 
    
    # This doesn't actually need to happen, but it should in this example.
    @test lif(inj(gen(K) + 1)) == gen(K) + 1

    @test precision(Kp) == 10

    @test inj(lif(gen(Kp))) == gen(Kp)

    @test inj(lif(zero(Kp))) == zero(Kp)

    @test lif(inj(zero(K))) == zero(K)

    @test all(let a=rand(Kp); inj(lif(a)) == a end for i=1:100)
    
    # Also test how the generic unramified completions work. The output of the
    # specialized algorithm most agree with the general_technique.
    
    lq = prime_decomposition(maximal_order(K), 37)
    Q  = lq[1][1]
    Kq, inj = Hecke.generic_completion(K,Q) # Generically returns an Eisenstein Extension
    Kqbase = base_ring(Kq)
    
    lif = Hecke.preimage_function(inj)
    
    Kq2, inj2 = Hecke.unramified_completion(K,Q)
    lif2 = Hecke.preimage_function(inj2)
    
    @test degree(Kqbase) == degree(Kq2) && prime(Kqbase) == prime(Kq2)
    @test precision(Kqbase) == precision(Kq2)

    # There is a bug in Nemo's a^0 for qadics. Hence, there will be a mild precision
    # error until this is fixed.
    tval = inj(gen(K))
    setprecision!(tval,9)
    @warn "Precision for 0-th powering erronious in Nemo. Test will quietly let this fail."
    @test string(inj(gen(K))) == "$tval"

    @test lif(inj(zero(K))) == zero(K)
    
    @test lif2(inj2(zero(K))) == zero(K)    

    @test all(let a=rand(Kq2); inj2(lif2(a)) == a end for i=1:100)
end
    

@testset "Completions: Wildanger_field(3,131), more precision" begin

    my_prime = 131
    K, a = wildanger_field(3, my_prime)
    lp = prime_decomposition(maximal_order(K), my_prime)
    P  = lp[1][1]

    Kp, inj = Hecke.completion(K,P,20)
    lif = Hecke.preimage_function(inj)

    # Test 
    @test iszero(change_base_ring(Kp, K.pol)(inj(gen(K))))
    
    # This doesn't actually need to happen, but it should in this example.
    @test lif(inj(gen(K) + 1)) == gen(K) + 1

    @test precision(Kp) == 20

    @test inj(lif(gen(Kp))) == gen(Kp)

    @test inj(lif(zero(Kp))) == zero(Kp)

    @test lif(inj(zero(K))) == zero(K)

    @test all(let a=rand(Kp); inj(lif(a)) == a end for i=1:100)
    
    # Also test how the generic unramified completions work. The output of the
    # specialized algorithm most agree with the general_technique.
    
    lq = prime_decomposition(maximal_order(K), 37)
    Q  = lq[1][1]
    Kq, inj = Hecke.generic_completion(K,Q,20) # Generically returns an Eisenstein Extension
    Kqbase = base_ring(Kq)
    
    lif = Hecke.preimage_function(inj)
    
    Kq2, inj2 = Hecke.unramified_completion(K,Q,20)
    lif2 = Hecke.preimage_function(inj2)

    @test iszero(change_base_ring(Kq, K.pol)(inj(gen(K))))
    @test degree(Kqbase) == degree(Kq2) && prime(Kqbase) == prime(Kq2)
    @test precision(Kqbase) == precision(Kq2)

    # There is a bug in Nemo's a^0 for qadics. Hence, there will be a mild precision
    # error until this is fixed.
    tval = inj(gen(K))
    setprecision!(tval,19)
    @warn "Precision for 0-th powering erronious in Nemo. Test will quietly let this fail."
    @test string(inj(gen(K))) == "$tval"

    @test lif(inj(zero(K))) == zero(K)
    
    @test lif2(inj2(zero(K))) == zero(K)    

    @test all(let a=rand(Kq2); inj2(lif2(a)) == a end for i=1:100)
end
    
@testset "Completions: Wildanger_field(3,137), basic" begin

    my_prime = 137
    K, a = wildanger_field(3, my_prime)
    lp = prime_decomposition(maximal_order(K), my_prime)
    P  = lp[1][1]

    Kp, inj = Hecke.completion(K,P)
    lif = Hecke.preimage_function(inj)

    @test iszero(change_base_ring(Kp, K.pol)(inj(gen(K))))
    
    # This doesn't actually need to happen, but it should in this example.
    @test lif(inj(gen(K) + 1)) == gen(K) + 1

    @test precision(Kp) == 10

    @test inj(lif(gen(Kp))) == gen(Kp)

    @test inj(lif(zero(Kp))) == zero(Kp)

    @test lif(inj(zero(K))) == zero(K)

    @test all(let a=rand(Kp); inj(lif(a)) == a end for i=1:100)
    
    # Also test how the generic unramified completions work. The output of the
    # specialized algorithm most agree with the general_technique.
    
    lq = prime_decomposition(maximal_order(K), 37)
    Q  = lq[1][1]
    Kq, inj = Hecke.generic_completion(K,Q) # Generically returns an Eisenstein Extension
    Kqbase = base_ring(Kq)
    
    lif = Hecke.preimage_function(inj)
    
    Kq2, inj2 = Hecke.unramified_completion(K,Q)
    lif2 = Hecke.preimage_function(inj2)
    
    @test degree(Kqbase) == degree(Kq2) && prime(Kqbase) == prime(Kq2)
    @test precision(Kqbase) == precision(Kq2)

    # There is a bug in Nemo's a^0 for qadics. Hence, there will be a mild precision
    # error until this is fixed.
    tval = inj(gen(K))
    setprecision!(tval,9)
    @warn "Precision for 0-th powering erronious in Nemo. Test will quietly let this fail."
    @test string(inj(gen(K))) == "$tval"

    @test lif(inj(zero(K))) == zero(K)
    
    @test lif2(inj2(zero(K))) == zero(K)    

    @test all(let a=rand(Kq2); inj2(lif2(a)) == a end for i=1:100)
end


@testset "Sharpening" begin
    
    my_prime = 131
    K, a = wildanger_field(3, my_prime)
    lp = prime_decomposition(maximal_order(K), my_prime)
    P  = lp[1][1]

    Kp, inj = Hecke.completion(K,P)
    sharpen!(inj, 20)

    @test precision(Kp) == 20
    
    Kp2, inj2 = Hecke.completion(K,P,20)

    # Technically, the polynomials only have to define the same extension. In this
    # case they should turn out identical as presently, sharpen re-solves the linear
    # equations defining the polynomial.
    Rx, x = PolynomialRing(base_ring(Kp), "x")
    @test Kp.pol(x) == Kp2.pol(x) && base_ring(Kp) == base_ring(Kp2)

    Kp3, inj3 = Hecke.completion(K,P,10)

    @test precision(Kp3) == 10 && precision(Kp) == 20
    
    @test preimage(inj, inj(zero(K))) == zero(K)

    @test inj(lif(gen(Kp))) == gen(Kp)

    @test iszero(change_base_ring(Kp, K.pol)(inj(gen(K))))
end

nothing
