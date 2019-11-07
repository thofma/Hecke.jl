
# By definition, a non-archimedean local field always has a uniformizer.

function unit_part(a::NALocalFieldElem)
    K  = parent(a)
    pi = uniformizer(K)
    m  = Integer(valuation(a)//valuation(pi))
    return pi^(-m) * a
end

function ^(a::padic, n::fmpz)
    iszero(n) && return one(a)
    n < 0     && return inv(a)^(-n)

    if !(typemin(Int) <= n <= typemax(Int))
        error("Exponent too large to perform operation.")
    end
    
    return a^Int(n)
end

function abs(a::NALocalFieldElem)
    return residue_characteristic(parent(a))^(-valuation(a))
end


function (Q::FlintPadicField)(a::Rational{Int})
    return Q(numerator(a))//Q(denominator(a))
end

# TODO: Move to NEMO
import Base.ceil
function ceil(a::fmpq)
    q,r = divrem(numerator(a), denominator(a))
    return iszero(r) ? q : q+1
end

#****************************************************************************************

@doc Markdown.doc"""
    residue_characteristic(K::NALocalField)
Return the characteristic of the residue field.
"""
residue_characteristic(K::NALocalField) = residue_characteristic(base_field(K))

residue_characteristic(Q::FlintLocalField) = prime(Q)

@doc Markdown.doc"""
    log(a::NALocalFieldElem)
Return the Iwasawa logarithm of `a`. See `https://en.wikipedia.org/wiki/P-adic_exponential_function`.
"""
function log(a::NALocalFieldElem)
    @assert !iszero(a)
    
    N = precision(a)
    K = parent(a)
    k,res = ResidueField(K)
    card_kx = order(k)-1
    
    # Remove the root of unity factor, write the new element as 1 + b.
    b = unit_part(a)^card_kx - one(K)
    bsqrd = b*b
    
    # Evaluate the power series for log.
    # Split into two iterations to avoid if statements
    num_terms = Int(ceil(N//valuation(b)))
    result = zero(K)
    powb = b
    for j=1:2:num_terms
        result += powb // j
        powb   *= bsqrd
    end

    powb = b^2
    for j=2:2:num_terms
        result -= powb // j
        powb   *= bsqrd
    end
    
    return result // K(card_kx)
end

@doc Markdown.doc"""
    exp(a::NALocalFieldElem)
Return the p-adic exponential of `a`. See `https://en.wikipedia.org/wiki/P-adic_exponential_function`.
"""
function exp(a::NALocalFieldElem)
    iszero(a) && return one(a)
    
    N = precision(a)
    K = parent(a)
    p = residue_characteristic(K)

    if valuation(a) <= 1//(p-1)
        error("$a is not in the radius of convergence of `exp`.")
    end
    
    function _number_terms_for_exp(N,p,vz)
        # Note that the valuation of $n!$ is bounded by n//(p-1). The expression below
        # bounds the $n$ such that z^n/n! is O(p^N).
        return Int(ceil(N * (p-1)//(vz*(p-1)-1)))
    end

    # Evaluate the power series for exp.
    num_terms = _number_terms_for_exp(N, p, valuation(a))
    result = one(K) # The 0-th term is included here.
    powa   = one(K)
    factj  = one(K)
    for j=1:num_terms
        factj  *= j
        powa   *= a
        result += powa // factj
    end
    
    return result
end

function valuation_of_factorial(n::Integer, p::Integer)
    n==0 && return 0
    
    result = 0
    powp   = p
    while true
        m = Int(floor(n//powp))
        m == 0 && break
        result += m
        powp *= p
    end
    return result
end
