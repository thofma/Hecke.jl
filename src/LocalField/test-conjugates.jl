using Test
using Hecke

@testset "Flint Hensel contexts are broken" begin
    # Specifically, for polynomials defining extensions with non-trivial ramification, it
    # goes very wrong.
    
    Rx,x = PolynomialRing(FlintZZ,"x")
    f = (x^3 + x + 1)*(x^2-2)*(x^5+x^4+ x^3 + x+1)

    H  = Hecke.factor_mod_pk_init(f,2)
    lf = Hecke.factor_mod_pk(H,2)

    @test degree(sum( k^v for (k,v) in collect(lf))) < degree(f)
end


@testset "Completions" begin
    k, a = wildanger_field(3, 131)
    # (Number field over Rational Field with defining polynomial x^3-131*x^2+131*x-131, _$)

    C = qAdicConj(k, 31)

    conjugate_fields = C.C.Q
    conjugate_fields = [conjugate_fields[1], conjugate_fields[1], conjugate_fields[2]]

    b = gen(conjugate_fields[1])

    raw_values = [
        (4 + 29*31^1 + 30*31^3 + 27*31^4 + 26*31^5 + 25*31^6 + 26*31^7 + 13*31^8 + 8*31^9)*b + (19 + 29*31^1 + 19*31^2 + 2*31^3 + 20*31^4 + 16*31^5 + 9*31^6 + 30*31^7 + 13*31^8 + 2*31^9)
        (27 + 1*31^1 + 30*31^2 + 3*31^4 + 4*31^5 + 5*31^6 + 4*31^7 + 17*31^8 + 22*31^9)*b + (27 + 21*31^1 + 23*31^2 + 30*31^3 + 14*31^4 + 11*31^5 + 3*31^6 + 27*31^7 + 14*31^8 + 5*31^9) 
        (23 + 14*31^1 + 18*31^2 + 28*31^3 + 26*31^4 + 2*31^5 + 18*31^6 + 4*31^7 + 2*31^8 + 23*31^9)      ]

    conj_test_values = [F(b) for (F,b) in zip(conjugate_fields, raw_values)]

    @test vcat(conjugates(a, fmpz(31))...) == conj_test_values

    lp = prime_decomposition(maximal_order(k), 37)
    # 2-element Array{Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},Int64},1}:
    #  (<37, _$+2>
    # Norm: 37
    # Minimum: 37
    # two normal wrt: 37, 1)               
    #  (<37, _$^2 + 15*_$ - 10>
    # Norm: 1369
    # Minimum: 37
    # two normal wrt: 37, 1)

    C1, mC1 = completion(k, lp[1][1])
    # (Unramified extension of 37-adic numbers of degree 1, Map from
    # Number field over Rational Field with defining polynomial x^3-131*x^2+131*x-131 to Unramified extension of 37-adic numbers of degree 1 defined by a julia-function with inverse
    # )

    C2, mC2 = completion(k, lp[2][1])
    # (Unramified extension of 37-adic numbers of degree 2, Map from
    # Number field over Rational Field with defining polynomial x^3-131*x^2+131*x-131 to Unramified extension of 37-adic numbers of degree 2 defined by a julia-function with inverse
    # )

    mC2a =  mC2(a)
    #(11 + 15*37^1 + 36*37^2 + 1*37^3 + 31*37^4 + 16*37^5 + 9*37^6 + 33*37^7 + 9*37^8 + 7*37^9 + O(37^10))*a + (26 + 19*37^1 + 26*37^2 + 3*37^3 + 33*37^4 + 16*37^5 + 33*37^6 + 35*37^7 + 12*37^8 + 33*37^9 + O(37^10))

    @test preimage(mC2, mC2a) == -2511552483050448743793433955969332899552*a^2 + 5365463224081720212664744523051098506912*a + 3530047674421867860891817239846622123868

end
nothing
