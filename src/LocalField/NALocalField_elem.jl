
# By definition, a non-archimedean local field always has a uniformizer.

@doc Markdown.doc"""
    unit_part(a::NALocalFieldElem)
Returns an element `b` such that `b*pi^v = a` and `valuation(b)==0`, where `pi` is the uniformizer of the parent of `a`.
"""
function unit_part(a::NALocalFieldElem)
    K  = parent(a)
    pi = uniformizer(K)
    m  = Integer(valuation(a)//valuation(pi))
    return pi^(-m) * a
end

@doc Markdown.doc"""
    remove_pth_powers(a::eisf_elem)
Returns an element `b` such that `b*p^v = a` and `valuation(b)==0`. Note that `b` may live in a field extension of `parent(a)`.
"""
function remove_pth_powers(a::eisf_elem)
    K = parent(a)
    e = ramification_degree(K)
    Rx,x = PolynomialRing(K, "x")
    rts = roots(x^e - prime(K))

    if isempty(rts)
        error("Not implemented in the case where the field lacks p-th roots.")
    end

    # Choose your favorite e-th root of p
    rt = rts[1][1]
    result = a//rt^valuation(a)

    # Sanity check
    @assert valuation(result) == 0
    return result
end

@doc Markdown.doc"""
    remove_pth_powers(a::FlintLocalFieldElem)
Returns an element `b` such that `b*p^v = a` and `valuation(b)==0`.
"""
function remove_pth_powers(a::FlintLocalFieldElem)
    return unit_part(a)
end


function ^(a::padic, n::fmpz)
    iszero(n) && return one(a)
    n < 0     && return inv(a)^(-n)

    if !(typemin(Int) <= n <= typemax(Int))
        error("Exponent too large to perform operation.")
    end
    
    return a^Int(n)
end

# TODO: Make the output of abs lie in a well-defined real field?
# function abs(a::NALocalFieldElem)
#     return residue_characteristic(parent(a))^(-valuation(a))
# end


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

#elem_type(::Type{NALocalField}) = NALocalFieldElem

@doc Markdown.doc"""
    log(a::NALocalFieldElem)
Return the Iwasawa logarithm of `a`. See `https://en.wikipedia.org/wiki/P-adic_exponential_function`. If `a` is defined over a ramified extension, the result may be defined over an extension of the parent of `a` (of the same type).
"""
function log(a::NALocalFieldElem)
    @assert !iszero(a)
    
    N = precision(a)
    K = parent(a)
    k,res = ResidueField(K)
    card_kx = order(k)-1
    
    # Remove the root of unity factor, write the new element as 1 + b.
    b = remove_pth_powers(a)^card_kx - one(K)
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
    iwasawa_log(a::NALocalFieldElem)
Return the Iwasawa logarithm of `a`. See `https://en.wikipedia.org/wiki/P-adic_exponential_function`.
"""
iwasawa_log(a::NALocalFieldElem) = log(a)

function iwasawa_log(a::qadic)
    q = prime(parent(a))^degree(parent(a))
    if iseven(q) # an error in flint
        return log((a^(q-1))^2)//2//(q-1)
    end
    return log(a^(q-1))//(q-1) # faster than `log(a*inv(teichmuller(a)))`
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
    
    # Note that the valuation of $n!$ is bounded by n//(p-1). The expression below
    # bounds the $n$ such that z^n/n! is O(p^N).
    vz = valuation(a)
    num_terms = Int(ceil(N * (p-1)//(vz*(p-1)-1)))
    
    # Evaluate the power series for exp.
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
