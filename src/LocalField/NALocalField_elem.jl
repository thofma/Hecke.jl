
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
Return the Iwasawa logarithm of `a`. See `https://en.wikipedia.org/wiki/P-adic_exponential_function`. The result is defined in the parent of `a`.
"""
function log(a::NALocalFieldElem)

    # This is an implementation of Algorithm 2.8 of:
    # "An application of the p-adic analytic class number formula"
    # Claus Fieker and Yinan Zhang
    @assert !iszero(a)
    
    K   = parent(a)
    k,_ = ResidueField(K)
    card_kx = order(k)-1

    pi = uniformizer(K)
    u  = unit_part(a) # a = pi^valuation(a) * u

    # Since `log` is normalized so that `log(p)=0`, and `pi^e` is not necessarily
    # a power of `p`, we need to compute a correction factor. More generally, `p` is the
    # uniformizer of the unramified subfield.
    correction_factor = let
        p_K = K(prime(K))
        p_unit    = unit_part(p_K) # p = pi^e * p_unit
        p_unit_kx = p_unit^card_kx
        va  = fmpq(valuation(a))
        vpi = fmpq(valuation(pi))
        
        -K(va*vpi//card_kx)*log_power_series(p_unit_kx, _num_terms_for_log(p_unit_kx))
    end
    
    logu = let
        b = u^card_kx        
        log_power_series(b, _num_terms_for_log(b)) // K(card_kx)
    end
    
    return logu + correction_factor
end

_num_terms_for_log(a::NALocalFieldElem) = Int(ceil(precision(a)//valuation(a - one(parent(a)))))


@doc Markdown.doc"""
    log_power_series(a)
Generic implenentation to evaluate the power series expression for `log(a)`, to number of terms 'num_terms'. There is no convergence check in this method.
"""
function log_power_series(a, num_terms::Integer)
    # Write `a = 1 - b`, and use the simpler power series expression.
    K = parent(a)
    b = one(K) - a
    
    # Evaluate the power series for log.
    minus_result = zero(K)
    powb = b
    for j=1:num_terms
        minus_result += powb // j
        powb *= b
    end
    return -minus_result
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
    p = Int(residue_characteristic(K))

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


#########################################################################################
#
#   Tropicalization
#
#########################################################################################

function tropicalization(g::Hecke.Generic.Poly{<:NALocalFieldElem})
    return valuation.(coefficients(g))
end

