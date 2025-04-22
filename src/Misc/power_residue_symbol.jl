#Computes the d-th power residue symbol (a/b)_d in F_q
#with d|q-1

@doc raw"""
    power_residue(a::PolyRingElem{T}, b::PolyRingElem{T}, d::ZZRingElem, q::ZZRingElem) where T<: RingElem

Computes the $d$-th power residue symbol $\left(\frac{a}{b}\right)_d$ in $\mathbb{F}_q$.
$d$ has to divide $q-1$.
"""

function power_residue(a::PolyRingElem{T}, b::PolyRingElem{T}, d::ZZRingElem, q::ZZRingElem) where T<: RingElem
    if mod(q-1,d)!=0
        return error("Must have d|q-1")
    end
    e = div(q-1, d)

    if b==0 || a==0
        return error("Must have a,b!=0")
    end

    if gcd(a,b)!=1
        return 0
    end

    a = mod(a,b)

    #top part constant -> formula
    if degree(a)==0
        return powermod( powermod(ZZRingElem(coeff(a,0)), e, q),  degree(b), q)
    end

    #switch top and bottom part -> recursion (general reciprocity law)
    symbol = mod(  mod( powermod(powermod(ZZRingElem(leading_coefficient(a)), e, q), degree(b), q) *
    powermod(powermod(ZZRingElem(leading_coefficient(b)), e, q), -degree(a), q),  q) *
    power_residue(b,a,d,q),   q)

    if isodd(e) && isodd(degree(a)) && isodd(degree(b))
        symbol = mod( (-1) * symbol, q)
    end

    return symbol
end
