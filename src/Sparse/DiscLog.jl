include("IndexCalculus.jl")

function sieve2(F::T,SP = sieve_params(characteristic(F),0.02,1.1)) where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField} #works without primitive element
    p = characteristic(F) #(p = Int(length(A.K)))
    set_attribute!(F, :p=>p)
    #a = get_attribute(F, :a)
    H = floor(root(p,2))+1
    J = H^2 - p
    qlimit, climit, ratio, inc = SP
    #(lift(a) <= qlimit&&isprime(a)) || (a = primitive_elem(F, true)) 
    set_attribute!(F, :primitive_elem=>a)

    # factorbase up to qlimit
    FB = [fmpz(i) for i in PrimesSet(1,qlimit)]

    # use shift! / unshift! here...
    log2 = log(2.0);
    logqs = [log(Int(q))/log2 for q in FB] #real logarithms for sieve 
    FBs = deepcopy(FactorBase(FB)) #Factorbase
    l2 = length(FB)
    l = deepcopy(l2)
    Indx = Dict(zip(FB,[i for i=1:l])) #Index in a dictionary
    A = sparse_matrix(ZZ)
    #IDEA: dont add logs. add INT counter, then add cnt * log in the end. ??
    ##########################################################################################################################################
    # Sieve for ci
    for c1 = 1:climit
        nrows(A)/length(FB) < ratio || break
        Sieve = zeros(climit)
        den = H + c1;                # denominator of relation
        num = -(J + c1*H)            # numerator
        for i=1:length(FB)
            q = FB[i]
            qpow = q
            nextqpow = qpow   #WARNING inserted, because of some error with nextqpow
            logq = logqs[i]
            while qpow < qlimit      # qlimit-smooth
                den % qpow != 0 || break
                c2 = num * invmod(den, fmpz(qpow))  % qpow
                (c2 != 0) || (c2 = qpow)
                nextqpow = qpow*q    #increase q_power
                while c2 < c1   #c2>=c1 to remove redundant relations of (c1,c2) tuples, just increase c2
                    c2+=qpow
                end
                while c2 <= length(Sieve)
                    Sieve[Int(c2)] += logq
                    if nextqpow > qlimit
                        prod = (J + (c1 + c2)*H + c1*c2) % p
                        nextp = nextqpow
                        while rem(prod,nextp) == 0
                            Sieve[Int(c2)] += logq
                            nextp = nextp*q
                        end
                    end
                    c2 += qpow
                end
                qpow = nextqpow
            end
        end

        #include relations / check sieve for full factorizations.
        rel = den * (H + 1)
        relinc = H + c1       # add to relation to get next relation
        idx = 0
        for c2 in 1:length(Sieve)
            n = rel % p
            if abs(Sieve[c2] - (nbits(n)-1)) < 1 
                #FBs = FactorBase(FB) #generate Factorbas from updated FBs with new c_i´s
                if issmooth(FBs,fmpz(n))
                    dict_factors = Hecke.factor(FBs,fmpz(n))
                    #Include each H + c_i in extended factor basis.
                    r = length(Indx)+1
                    if !((H + c1) in keys(Indx))
                        push!(FB,H + c1)
                        push!(Indx,(H+c1) => r)
                    end#(FB = vcat(FB,[H + c1])) #push!(FB,wert)
                    r = length(Indx)+1
                    if !((H + c2) in keys(Indx))
                        push!(FB,H + c2)
                        push!(Indx,(H+c2) => r)
                    end#(FB = vcat(FB,[H + c2]))
                    #Include relation (H + c1)*(H + c2) = fact.
                    #row = nrows(A) + 1 # insert new relation (new row)to sparse_matrix
                    J1 = Vector{Int64}([])
                    V = Vector{Int64}([])
                    for (prime,power) in dict_factors
                        if !(power == 0)
                            push!(J1,Indx[prime])
                            push!(V,Int(power))
                        end
                    end
                    if c1 == c2
                         push!(J1,Indx[H+c1])
                         push!(V,-2)
                    else
                         push!(J1,Indx[H+c1])
                         push!(J1,Indx[H+c2])
                         push!(V,-1)
                         push!(V,-1)
                    end
                    push!(A,sparse_row(ZZ, J1, V))
                end
            end
            rel += relinc
        end
    end
    #increase Sieve 
    if nrows(A)/length(FB) < ratio
		qlimit += inc[1]
		climit += inc[2]
		return sieve2(F,(qlimit, climit, ratio, inc))
	end
    return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :factorbase=>FBs, :fb_length=>l)
end

function log_dict2(F::T, A, TA )where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField}
    p = get_attribute(F, :p)
    cnt = 0
    if !wiedemann(A, TA)[1]
        @warn "wiedemann failed"
            return F
    end
    z = true 
    while z
        kern = wiedemann(A, TA)[2]
        cnt+=1
        cnt < 5 || return Dict{fmpz, fmpz}([]),Vector{fmpz_mod}([]),FactorBase(fmpz[])
        if !iszero(kern)
            z = false
        end
    end
    a = get_attribute(F,:a)
    idx = get_attribute(F, :idx)
    FB_array = get_attribute(F, :FB_array)
    if typeof(idx) == Nothing
        (lift(a) <= qlimit&&isprime(a)) || (a = primitive_elem(F, true)) 
        set_attribute!(F, :primitive_elem=>a)
        idx = searchsortedfirst(FB_array, lift(a))
    end
    set_attribute!(F, :p_elem2=>FB_array(idx))
    kern = inv(kern[idx]).*kern #norm kernelvec
    # recon FB_logs mod p  mod p (note this works here if (p-1)/2 prime) Only 2 checks necessary.
    Q,L = Array{fmpz}([]),Array{fmpz}([])
    two = fmpz(2)
    _modulus = get_attribute(F, :_modulus)
    u,v = get_attribute(F, :u), get_attribute(F, :v)
    FB = get_attribute(F, :FB_array)
    #a = get_attribute(F, :primitive_elem)
    l = get_attribute(F, :fb_length)
    for i in 1:l
        temp = lift(kern[i])*two*u
        test1 = temp%(p-1)
        test2 = (temp + v*_modulus)%(p-1)
        q_temp = FB[i]
        if a^test1 == q_temp   
            push!(Q,q_temp)
            push!(L,fmpz(test1))
        elseif a^test2 == FB[i]
            push!(Q,q_temp)
            push!(L,fmpz(test2))
        end 
    end 
    
    Logdict = Dict(zip(Q,L))

    length(Logdict) == l ? (@info "FB_LOGS: all FB logs found") : (@warn "FB_LOGS: at least $(length(Logdict)-l) logarithms not found") 
    set_attribute!(F, :Logdict=>Logdict, :kern=>kern, :Q=>FactorBase(Q))
    return F
end

function IdxCalc2(a::T, b::T, F=parent(a)) where T<:Union{gfp_elem, gfp_fmpz_elem} #RingElem better?
    @assert parent(a) === parent(b)
    b==1 && return fmpz(0)
    b==a && return fmpz(1)
    set_attribute!(F, :a=>a)
    #typeof(get_attribute(F, :Logdict))==Nothing || @goto Logdict
    #typeof(get_attribute(F, :RelMat))==Nothing || @goto RelMat
    if typeof(get_attribute(F, :RelMat))==Nothing
        sieve2(F)
    end
    if typeof(get_attribute(F, :Logdict))==Nothing
        p = get_attribute(F, :p)
        _modulus = div((p-1),2)
        two = fmpz(2)
        #F2 = GF(_modulus)
        F2 = ResidueRing(ZZ, _modulus) #change it when prepro fixed
        set_attribute!(F, :F2=>F2)
        c, u, v = gcdx(two, _modulus)
        c == 1 || (@error "FB_LOGS: 2 ,(p-1)/2 not coprime")
        set_attribute!(F, :u=>u, :v=>v)
        set_attribute!(F, :_modulus=>_modulus)
        #Preprocessing
        A = change_base_ring(F2, get_attribute(F,:RelMat))
        TA = transpose(A)
        A, TA = sp_prepro(A, TA, get_attribute(F, :fb_length))
        #Wiedemann + dict with logs of FB
        log_dict2(F, A, TA)
    end
    logb = log(F, b)
    if logb == 0
        return logb, F
    end
    if a != get_attribute(F, :primitive_elem)
        p = get_attribute(F, :p)
        loga = log(F, a)
        logb = solvemod(loga, logb, p-1)
    end
    return logb, F 
end


#compare time of IdxCalc and IdxCalc2
F = GF(cryptoprime(13))
a = primitive_elem(F, false)
b = F(101)
@time 2*3
@time g1 = IdxCalc(a,b)
@time g2 = IdxCalc2(a,b)

function disc_log_rest(a2, b2, F)
    @assert parent(a2) === parent(b2)
    b==1 && return fmpz(0)
    b==a && return fmpz(1)
    p = characteristic(F)
    set_attribute(F, :a=>F(2))
    sieve(F)                     #later sieve2
    small_prod = get_attribute(F, :small_prod)
    rest = get_attribute(F, :rest)
    #=
    SP = sieve_params(p, 0.02, 1.1) #prob. p instead of rest 
    qlimit = SP[1]
    i = 0
    prim_elem = a2
    while lift(prim_elem)>qlimit && i<1000
        i+=1
        prim_elem = Hecke.primitive_element(F)^small_prod
    end
    if lift(prim_elem)>qlimit
        @info "prim_elem to big"
        return false
    end
    set_attribute!(F ,:primitive_elem=>prim_elem)
    sieve(F)
    =#
    #Preprocessing
    RR = ResidueRing(ZZ, rest)#falsches p ?
    A = change_base_ring(RR,get_attribute(F,:RelMat))
    TA = transpose(A)
    A, TA = sp_prepro(A, TA, get_attribute(F, :fb_length))
    #Wiedemann + dict with logs of FB
    cnt = 0
    if !wiedemann(A, TA)[1]
        @warn "wiedemann failed"
            return F
    end
    z = true 
    while z
        kern = wiedemann(A, TA)[2]
        cnt+=1
        cnt < 10 || return Dict{fmpz, fmpz}([]),Vector{fmpz_mod}([]),FactorBase(fmpz[])
        if !iszero(kern)
            z = false
        end
    end
    idx = get_attribute(F, :idx)
    FB_array = get_attribute(F, :FB_array)
    if typeof(idx) == Nothing
        (lift(a) <= qlimit&&isprime(a)) || (a = primitive_elem(F, true)) 
        set_attribute!(F, :primitive_elem=>a)
        idx = searchsortedfirst(FB_array, lift(a))
    end
    set_attribute!(F, :primitive_elem=>FB_array[idx])
    kern = inv(kern[idx]).*kern #norm kernelvec
    Logdict_p = Dict(zip(FB_array, kern))
    set_attribute!(F, :Logdict=>Logdict_p)
    g2 = log(F, b2)
    if lift(a2) != FB_array[idx]
        g2 = solvemod(log(F, a2), g2)
    end
    return g2
end



function disc_log(a, b, F=parent(a)) #p prime
    @assert parent(a) === parent(b)
    b==1 && return fmpz(0)
    b==a && return fmpz(1)
    p = characteristic(F)
    if log(p)/log(10)<13
        @info "only bsgs used"
        return disc_log_bs_gs(a,b,p-1), F #or ph -> compare time
    end
    d,t = Hecke.factor_trial_range(p-1)
    d = sort(d)
    small_prod = t
    rest = p-1
    for (k,v) in d
        pow_ = k^v
        divexact!(rest, pow_)
        mul!(small_prod, small_prod, pow_)
    end
    h = maximum(keys(d))
    if rest == 1
        rest = h^d[h]
        divexact!(small_prod, rest)
    end
    set_attribute!(F, :small_prod=>small_prod)
    set_attribute!(F, :rest=>rest)
    if small_prod == 2
        return IdxCalc(a, b)
    end
    @assert log(small_prod)/log(10) < 13
    a1 = a^rest #primitive element for small_prod
    a2 = a^small_prod #primitive element for rest
    b1 = b^rest
    b2 = b^small_prod
    set_attribute!(F, :a1=>a1, :a2=>a2, :b1=>b1, :b2=>b2)
    g1 = disc_log_bs_gs(a1,b1,small_prod)
    if log(rest)/log(10)<13
        g2 = disc_log_bs_gs(a2,b2,rest)
        @info "bsgs for rest"
        return crt(g1, small_prod, g2, rest), F
    else
        @info "IdxCalc for rest"
        return Nothing, F
        @assert log(rest)/log(10)< 21
        #=
        g2 = disc_log_rest(a2, b2, F)
        if g2 == false
            return false, F
        end
        =#
    end
    return crt(g1, small_prod, g2, rest), F
end