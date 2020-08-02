module MFactor
#by Daniel

using Nemo
using Hecke

mutable struct disolveinfo{E}
    zero                ::E                         # the zero polynomial
    xalphas             ::Vector{E}                 # [x_i - alpha_i for i = 1..r]
    betas               ::Vector{Vector{E}}         # matrix of beta evaluations
    inv_prod_betas1     ::Vector{E}                 # info for inivariate solver
    prod_betas_coeffs   ::Vector{Vector{Vector{E}}} # matrix of taylor coeffs
    deltas              ::Vector{Vector{E}}         # answers
    delta_coeffs        ::Vector{Vector{Vector{E}}} # taylor coeffs of answer
end

############### subsets of 1, ..., n of size m ################################

mutable struct msubsets
    n::Int
    m::Int
end

function Base.iterate(a::msubsets)
    state = [i <= a.m ? true : false for i in 1:a.n]
    return (copy(state), state)
end

function Base.iterate(a::msubsets, state)
    i = 0
    while i < a.n && !state[1+i]
        i += 1
    end
    t1 = i
    while i < a.n && state[1+i]
        i += 1
    end
    t2 = i
    if t2 >= a.n
        return nothing
    end
    newstate = [t2 <= i < a.n ? state[1+i] : false for i in 0:a.n-1]
    newstate[1+t2] = true
    for i in 0:t2-t1-2
        newstate[1+i] = true
    end
    (copy(newstate), newstate)
end

# interface for enumerating evaluation points
# probably over-engineered and a simple random will do

function tuple_init(n::Int)
    return zeros(fmpz, n)
end

function tuple_saturate!(alpha::Vector{fmpz}, m::Int)
    n = length(alpha)
    @assert n > 0
    for i in m+1:n-1
        alpha[1 + m] += alpha[1 + i]
        alpha[1 + i] = 0
    end
    if m < n && alpha[1 + m] == 0
        for i in 1:m
            if alpha[i] != 0
                return
            end
        end
        alpha[1 + m] = 1
    end
end

function tuple_next!(alpha::Vector{fmpz})
    n = length(alpha)
    @assert n > 0
    sum = fmpz(0)
    for i in 1:n
        sum += alpha[i]
    end
    i = n - 1
    while i >= 0 && alpha[1 + i] == 0
        i -= 1
    end
    t1 = i
    while i >= 0 && alpha[1 + i] != sum
        i -= 1
    end
    t2 = i
    while i >= 0 && alpha[1 + i] == sum
        i -= 1
    end
    t3 = i
    if t1 > 0 && t1 != t2
        (alpha[1 + t1], alpha[1 + n - 1]) = (alpha[1 + n - 1], alpha[1 + t1])        
        alpha[1 + n - 1] -= 1
        alpha[1 + t1 - 1] += 1
    elseif t1 > 0 && t1 == t2 && t3 >= 0
        alpha[1 + t3] += 1
        alpha[1 + t3 + 1] = 0
        alpha[1 + n - 1] = sum - 1
    else
        alpha[1 + n - 1] = alpha[1] + 1
        if n > 1
            alpha[1] = 0
        end
    end
end


########### various helpers for expansions in terms of (x - alpha) ############

# the evaluation of p at x = alpha. Don't use evaluate for this!!!
function taylor_rem(p::E, xalpha::E) where E
    q, r = divrem(p, xalpha)
    return r
end

function taylor_divrem(p::E, xalpha::E) where E
    return divrem(p, xalpha)
end

# set t to the coefficients of q when expanded in powers of (x - alpha)
function taylor_get_coeffs!(t::Vector{E}, q::E, xalpha::E) where E
    R = parent(q)
    empty!(t)
    while !iszero(q)
        q, r = divrem(q, xalpha)
        push!(t, r)
    end
end

function taylor_get_coeffs(q::E, xalpha::E) where E
    t = E[]
    taylor_get_coeffs(t, q, xalpha)
    return t
end

# opposite of taylor_get_coeffs
function taylor_from_coeffs(B::Vector{E}, xalpha::E, zero::E) where E
    a = zero
    for i in length(B):-1:1
        a = a*xalpha + B[i]
    end
    return a
end

function taylor_set_coeff!(t::Vector{E}, i::Int, c::E, zero::E) where E
    while 1 + i > length(t)
        push!(t, zero)
    end
    t[1 + i] = c
    while length(t) > 0 && iszero(t[end])
        popback!(t)
    end
end

#################### basic manipulation of Fac ################################

# a *= b^e
function mulpow!(a::Fac{T}, b::T, e::Int) where T
    @assert e >= 0
    if e < 1
        return
    end
    if isconstant(b)
        a.unit *= b^e
    elseif haskey(a.fac, b)
        a.fac[b] += e
    else
        a.fac[b] = e
    end
end

function mulpow!(a::Fac{T}, b::Fac{T}, e::Int) where T
    @assert !(a === b)
    @assert e >= 0
    if e < 1
        return
    end
    a.unit *= b.unit^e
    if isempty(a.fac)
        a.fac = b.fac
    elseif !isempty(b.fac)
        a.fac = merge((A, B) -> A + B*e, a.fac, b.fac)
    end
end

################ basic manipulation of polys #################################

function gcdcofactors(a, b)
    g = gcd(a, b)
    if iszero(g)
        @assert iszero(a)
        @assert iszero(b)
        return (g, a, b)
    else
        return (g, divexact(a, g), divexact(b, g))
    end
end

# remove the content with repect to variable v
function primitive_part(a::E, v::Int)::E where E
    R = parent(a)
    d = degree(a, v)
    g = R(0)
    for i in 0:d
        ci = coeff(a, Int[v], Int[i])
        if !iszero(ci)
            g = gcd(g, ci)::E
        end
    end
    if iszero(g)
        return a
    elseif isone(g)
        return a
    else
        return divexact(a, g)
    end
end

function get_lc(a::E, v::Int)::E where E
    d = degree(a, v)
    @assert d >= 0
    return coeff(a, Int[v], Int[d])
end

function set_lc(a::E, v::Int, b::E) where E
    R = parent(a)
    d = degree(a, v)
    @assert d >= 0
    diff = (b - coeff(a, Int[v], Int[d]))
    if iszero(diff)
        return a
    else
        return a + diff*gen(R, v)^d
    end
end

function make_monic(a::E)::E where E
    if length(a) < 1
        return a
    end
    lc = coeff(a, 1)
    if isone(a)
        return a
    else
        return inv(lc) * a
    end
end

function eval_one(a::E, v, alpha)::E where E
    R = parent(a)
    return divrem(a, gen(R, v) - alpha)[2]
end


################ generic diophantine solver ###################################

#=
    R is a multivariate ring K[X, x_1, ..., x_n]
    We will be dealing with polynomials in the first l + 1 variables, i.e.
    only the variables X, x_1, ..., x_l appear.
    l is length of alpha.

    For fixed B[1], ..., B[r], precompute info for solving

        t/(B[1]*...*B[r]) = delta[1]/B[1] + ... + delta[r]/B[r]

    for delta[1], ..., delta[r] given t in X, x_1, ..., x_l.

    alpha is an array of evaluation points
        x_1 = alpha[1]
        ...
        x_l = alpha[l]

    If, after evaluation at all x_j = alpha[j], the B[i] did not drop degree
    in X and are pairwise relatively prime in K[X], then the function returns
    true and a suitable disolveinfo. Otherwise, it returns false and junk

    Upon success, we are ready to solve for the delta[i] using disolve.
    The only divisions that disolve does in K are by the leading coefficients
    of the inv_prod_betas1 member of disolveinfo
=#

function disolveinit(B::Vector{E}, alpha::Vector, R) where E
    K = base_ring(R)
    n = nvars(R) - 1
    l = length(alpha)   # number of evaluated variables
    r = length(B)       # number of factors

    @assert n > 0
    @assert r > 1

    # betas is a 1+l by r matrix with the original B[i] in the last row
    # and successive evaluations in the previous rows
    betas = [E[R(0) for i in 1:r] for j in 0:l]

    # prod_betas is like betas, but has B[1]*...*B[r]/B[i] in the i^th column
    # we don't need prod_betas, but rather
    #   prod_betas_coeffs = taylor of prod_betas in x_(1+j) - alpha[j]
    prod_betas_coeffs = [[E[] for i in 1:r] for j in 0:l]

    # inv_prod_betas1[i] will hold invmod(B[1]*...*B[r]/B[i], B[i]) in R[X]
    # after all x_j = alpha[j] have been evaluated away
    inv_prod_betas1 = E[R(0) for i in 1:r]

    # working space that need not be reallocated on each recursive call
    deltas = [E[R(0) for i in 1:r] for j in 0:l]
    delta_coeffs = [[E[] for i in 1:r] for j in 0:l]

    xalphas = E[gen(R, 1 + j) - R(alpha[j]) for j in 1:l]

    I = disolveinfo{E}(R(0), xalphas,
                       betas, inv_prod_betas1, prod_betas_coeffs,
                       deltas, delta_coeffs)

    for i in 1:r
        I.betas[1+l][i] = deepcopy(B[i])
    end
    for j in l:-1:1
        for i in 1:r
            I.betas[j][i] = taylor_rem(I.betas[j + 1][i], xalphas[j])
        end
    end

    for i in 1:r
        if degree(I.betas[1][i], 1) != degree(I.betas[l + 1][i], 1)
            # degree drop in invariates in X
            return false, I
        end
    end

    # univariate ring for gcdx
    S, x = PolynomialRing(K, "x")
    sub = [k == 1 ? x : S(1) for k in 1:n+1]

    for j in 0:l
        for i in 1:r
            p = R(1)
            for k in 1:r
                if k != i
                    p *= I.betas[1 + j][k]
                end
            end
            if j > 0
                taylor_get_coeffs!(I.prod_betas_coeffs[1 + j][i], p, I.xalphas[j])
            else
                s = evaluate(betas[1][i], sub)
                t = evaluate(p, sub)
                g, s1, t1 = gcdx(s, t)
                if !isconstant(g)
                    # univariates are not pairwise prime
                    return false, I
                end
                I.inv_prod_betas1[i] = evaluate(divexact(t1, g), gen(R,1))
                # leave prod_betas_coeffs[1][i] as zero, it doesn't matter
            end
        end
    end

    return true, I
end

# The second return of disolve (the answer) is owned by I.
# So, at least its length should not be mutated.
function disolve(I::disolveinfo{E}, t::E, degs::Vector{Int}) where E
    return disolve_recursive(I, t, degs, length(I.xalphas))
end

function disolve_recursive(I::disolveinfo{E}, t::E, degs::Vector{Int},
                                                              lev::Int) where E
    @assert 0 <= lev <= length(I.xalphas)
    @assert lev <= length(degs)

    r = length(I.inv_prod_betas1)

    deltas = I.deltas[1 + lev]

    if lev == 0
        for i in 1:r
            Q, deltas[i] = divrem(t*I.inv_prod_betas1[i], I.betas[1][i])
            # TODO check the denominator of deltas[i] and possibly return false
        end
        return true, deltas
    end

    newdeltas = I.deltas[lev]
    delta_coeffs = I.delta_coeffs[1 + lev]

    for i in 1:r
        empty!(delta_coeffs[i])
    end

    for l in 0:degs[lev]
        t, newt = divrem(t, I.xalphas[lev])
        for s in 0:l-1
            for i in 1:r
                if s < length(delta_coeffs[i]) &&
                   l - s < length(I.prod_betas_coeffs[1 + lev][i])
                    newt -= delta_coeffs[i][1 + s] *
                            I.prod_betas_coeffs[1 + lev][i][1 + l - s]
                end
            end
        end

        if iszero(newt)
            continue
        end

        ok, newdeltas = disolve_recursive(I, newt, degs, lev - 1)
        if !ok
            return false, deltas
        end

        for i in 1:r
            if iszero(newdeltas[i])
                continue
            end
            if l + length(I.prod_betas_coeffs[1 + lev][i]) - 1 > degs[lev]
                return false, deltas
            end
            taylor_set_coeff!(delta_coeffs[i], l, newdeltas[i], I.zero)
        end
    end

    for i in 1:r
        deltas[i] = taylor_from_coeffs(delta_coeffs[i], I.xalphas[lev], I.zero)
    end

    return true, deltas
end

########### extremely thorough tests #####################

function map_down(Rp, a, mKp :: Map, pr::Int)
    M = MPolyBuildCtx(Rp)
    pk = prime(base_ring(a))^pr
    for (c, v) in zip(coeffs(a), exponent_vectors(a))
        @assert valuation(c) >= pr
        q = divexact(c, pk)  #should be a shift
        push_term!(M, mKp(q), v)
    end
    return finish(M)
end

function map_up(R, a, mKp :: Map, pr::Int)
    Rp = parent(a)
    Kp = base_ring(Rp)
    M = MPolyBuildCtx(R)
    pk = prime(base_ring(R))^pr

    for (c, v) in zip(coeffs(a), exponent_vectors(a))
        d = preimage(mKp, c)
        push_term!(M, d*pk, v)
    end
    return finish(M)
end

function lift_prime_power(a::fmpq_mpoly, fac::Vector{Generic.MPoly{qadic}},
                           alphas::Vector, degs::Vector{Int}, k::Int)

    r = length(fac)
    R = parent(fac[1])
    n = nvars(R)
    ZZ = base_ring(R)
    Kp, mKp = ResidueField(ZZ)
    Rp, x = PolynomialRing(Kp, n)

    pr = 0

    ok, I = disolveinit([map_down(Rp, f, mKp, pr) for f in fac], alphas, Rp)
    @assert ok

    a = map_coeffs(ZZ, a, parent = parent(fac[1]))

    for l in 1:k
        pr += 1
        pro = prod(fac)
        error = a - pro  
#println("error: ", error)
        if iszero(error)
          @show "exact"
            break
        end
        t = map_down(Rp, error, mKp, pr)
        ok, deltas = disolve(I, t, degs)
        @assert ok
        for i in 1:r
            fac[i] += map_up(R, deltas[i], mKp, pr)
        end
#println("newfac: ", fac)
    end
    return fac
end

end

#=
println("------------- lifing to 5^10  --------------------")
Kxyz, (x, y, z) = PolynomialRing(ZZ, ["x", "y", "z"])
lift_prime_power(
    (111111*x+y+z+555555)*(x-222222*y+z)*(x+y+333333*z),
    [(111111*x+y+z), (x-2*y+z), (x+y+3*z)], # all the lc_x must be correct :-(
    [1, 2], # evaluation points for y, z
    [3, 3], # degree bounds for y, z
    5, 10)


println("----------- bad leading coefficient --------------")
Kxyz, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
@time F = mfactor_char_zero(x^24-y^24*z^12)
println("yay! ", F)


println("-------------- extraneous factors ----------------")
Kxyz, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
@time F = mfactor_char_zero(((x^2+y^2+z^2+2)*(x+1)*(y+2)*(z+3) + x*y*z)*(x^2+y^2+z^2+3))
println("yay! ", F)


println("--------------- number field ---------------------")
QA, A = PolynomialRing(QQ, "A")
K, a = number_field(A^3 - 2, "a")
Kxyz, (x, y, z) = PolynomialRing(K, ["x", "y", "z"])
println("yay! ", mfactor_char_zero(Kxyz(0)))
println("yay! ", mfactor_char_zero(Kxyz(1)))
println("yay! ", mfactor_char_zero(Kxyz(2)))
println("yay! ", mfactor_char_zero(2*x^2*y*(1+y)*(x^3-2)))
println("yay! ", mfactor_char_zero(2*x^2*y*(1+y)*(2*x^3-1)*(a*x+a^2*y+1)*(a^2*x+a*y+1)^2))
println("yay! ", mfactor_char_zero(x^6-2*y^3))
println("yay! ", mfactor_char_zero((x^2+z-1)*(x+a*z^3)))
println("yay! ", mfactor_char_zero((x+y+a)*(x+a*y+1)*(x+y+2*a)))
println("yay! ", mfactor_char_zero((x^2+y^2+a)*(x^3+a*y^3+1)*(x^2+y+2*a)))
println("yay! ", mfactor_char_zero((1+x+a*y)^3*(1+x+a^2*y)^5))
println("yay! ", mfactor_char_zero((x+y+z)*(a*x+y+z)*(x+a*y+z)*(x+y+a*z)))


println("------------ rational benchmarketing -------------")
function number_of_odd_divisors(n::Int)
    count = 0
    for i in 1:2:n
        if n%i == 0
            count += 1
        end
    end
    return count
end
Kxyzt, (x, y, z, t) = PolynomialRing(QQ, ["x", "y", "z", "t"])
for i in 1:15
    @time P = ((1+x+y+z+t)^i+1)*((1+x+y+z+t)^i+2)
    @time F = mfactor_char_zero(P)
    println("power: ", i, ", number of factors: ", length(F.fac), ", expected: ", 1 + number_of_odd_divisors(i))
end


=#
