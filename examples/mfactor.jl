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
            if false && l + length(I.prod_betas_coeffs[1 + lev][i]) - 1 > degs[lev]
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

#=
    supposed to have a = prod(fac) mod p^kstart
    furthermore, the fac's are supposed to be pairwise coprime univariate in
        Fq[gen(1)] when evaluated at gen(2) = alphas[1], ... gen(n) = alphas[n-1]

    try to lift to a factorization mod p^kstop  (or maybe its mod p^(kstop+1))
=#
function lift_prime_power(
    a::fmpq_mpoly,
    fac::Vector{Generic.MPoly{qadic}},
    alphas::Vector,
    kstart::Int,
    kstop::Int)

    if kstop <= kstart
        return
    end


    r = length(fac)
    R = parent(fac[1])
    n = nvars(R)
    ZZ = base_ring(R)
    Kp, mKp = ResidueField(ZZ)
    Rp, x = PolynomialRing(Kp, n, cached = false)

    minorvars = [i for i in 2:n]
    degs = [degree(a, i) for i in 2:n]

    md = [map_down(Rp, f, mKp, 0) for f in fac]
    ok, I = Hecke.AbstractAlgebra.MPolyFactor.pfracinit(md, 1, minorvars, alphas)
    @assert ok  # evaluation of fac's should be pairwise coprime

    a = map_coeffs(ZZ, a, parent = parent(fac[1]))

    for l in kstart:kstop
        error = a - prod(fac)
        if iszero(error)
            break
        end
        t = map_down(Rp, error, mKp, l)
        ok, deltas = Hecke.AbstractAlgebra.MPolyFactor.pfrac(I, t, degs, true)
        if !ok
            return false, fac
        end
        for i in 1:r
            fac[i] += map_up(R, deltas[i], mKp, l)
        end
    end
    return true, fac
end

end

