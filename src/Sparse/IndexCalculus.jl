include("Preprocessing.jl")
include("Wiedemann.jl")
#include("Matrix.jl")
import Base.log #delete later, added to Sparse.jl
###############################################################################
#
#   SIEVE
#
###############################################################################

function primitive_elem(F::FinField,first::Bool) 
    p = length(F)
    Fact = prime_divisors(fmpz(p-1))
    while true # alpha exists
        for y in F
            bool = true
            if !first y = rand(F) end
            if isprime(lift(y))
                if !(one(F) in [y^(div(fmpz(p-1),i)) for i in Fact])
                    return y
                end
            end
        end
    end
end

@doc Markdown.doc"""
    sieve_params(p,eps::Float64,ratio::Float64) -> Tuple{Int64, Int64, Float64, Tuple{Int64, Int64}}

Returns parameters for sieve.
"""
function sieve_params(p,eps::Float64,ratio::Float64)
	# assymptotic bounds by Coppersmith, Odlyzko, and Schroeppel L[p,1/2,1/2]# L[n,\alpha ,c]=e^{(c+o(1))(\ln n)^{\alpha }(\ln \ln n)^{1-\alpha }}}   for c=1
	qlimit = exp((0.5* sqrt(log(p)*log(log(p)))))
	qlimit *= log(qlimit) # since aproximately    #primes
	climit = exp((0.5+eps)*sqrt(log(p)*log(log(p))))

	qlimit = Int64(ceil(0.5*max(qlimit,30)))
	climit = Int64(ceil(max(climit,35)))
	inc = (Int64(100),Int64(100))
	return qlimit,climit,ratio,inc
end

@doc Markdown.doc"""
    sieve(F::Nemo.Galois(Fmpz)Field,SP = sieve_params(characteristic(F),0.02,1.1)) -> Nemo.Galois(Fmpz)Field

Computes coefficient matrix of factorbase logarithms and returns F with corresponding attributes.
"""
function sieve(F::T,SP = sieve_params(characteristic(F),0.02,1.1)) where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField} #F with primitive element as attribute
    p = characteristic(F) #(p = Int(length(A.K)))
    set_attribute!(F, :p=>p)
    a = get_attribute(F, :a)
    H = floor(root(p,2))+1
    J = H^2 - p
    qlimit, climit, ratio, inc = SP
    lift(a) <= qlimit || (a = primitive_elem(F, true)) 
    set_attribute!(F, :primitive_elem=>a)

    # factorbase up to qlimit
    fb_primes = [i for i in PrimesSet(1,qlimit)]


    #FB[findfirst(isequal(lift(alpha))] FB[1] = lift(alpha), FB[]
    indx = findfirst(isequal(lift(a)),fb_primes)
    FB = vcat([lift(a)],deleteat!(fb_primes,indx)) # swap a[1] = a[2] , a[2] = [1] array
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
        sieve = zeros(climit)
        den = H + c1;                # denominator of relation
        num = -(J + c1*H)            # numerator
        for i=1:length(fb_primes)
            q = fb_primes[i]
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
                while c2 <= length(sieve)
                    sieve[Int(c2)] += logq
                    if nextqpow > qlimit
                        prod = (J + (c1 + c2)*H + c1*c2) % p
                        nextp = nextqpow
                        while rem(prod,nextp) == 0
                            sieve[Int(c2)] += logq
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
        for c2 in 1:length(sieve)
            n = rel % p
            if abs(sieve[c2] - (nbits(n)-1)) < 1 
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
		return sieve(F,(qlimit, climit, ratio, inc))
	end
    return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :factorbase=>FBs, :fb_length=>l)
end

###############################################################################
#
#   Auxiliary Logs
#
###############################################################################

@doc Markdown.doc"""
    log_dict(F::Nemo.Galois(Fmpz)Field, A::SMat, TA::SMat) -> Nemo.Galois(Fmpz)Field

Given a field $F$ with attributes from sieve, logs of factorbase are computed and added to $F$.
"""
function log_dict(F::T, A, TA )where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField}
    p = get_attribute(F, :p)
    cnt = 0
    @label retour
    kern = wiedemann(A, TA)
    cnt+=1
    cnt < 5 || return Dict{fmpz, fmpz}([]),Vector{fmpz_mod}([]),FactorBase(fmpz[])
    !iszero(kern) || @goto retour
    kern = inv(kern[1]).*kern #norm kernelvec
    # recon FB_logs mod p  mod p (note this works here if (p-1)/2 prime) Only 2 checks necessary.
    Q,L = Array{fmpz}([]),Array{fmpz}([])
    two = fmpz(2)
    _modulus = get_attribute(F, :_modulus)
    u,v = get_attribute(F, :u), get_attribute(F, :v)
    FB = get_attribute(F, :FB_array)
    a = get_attribute(F, :primitive_elem)
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

@doc Markdown.doc"""
    log(F::Nemo.Galois(Fmpz)Field, b) -> fmpz

Returns $g$ s.th. $a^g == b$ given the factorbase logs in $F$.
"""
function log(F::T, b) where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField}
    #return log_a(b) i.e x s.t a^x = b
    p = get_attribute(F, :p)
    a = get_attribute(F, :a)
    p_elem = get_attribute(F, :primitive_elem)
    FB = get_attribute(F, :Q)
    FB_logs = get_attribute(F, :Logdict)
    randomexp = fmpz(rand(1:p-1))
    while !issmooth(FB,fmpz(lift(b*p_elem^randomexp)))
        randomexp = fmpz(rand(1:p-1))
    end  
    factorization = Hecke.factor(FB,lift(b*p_elem^randomexp))

    logb = -randomexp + sum([exp*FB_logs[prime] for (prime,exp) in factorization])
    return logb
end

###############################################################################
#
#   DISCRETE LOGARITHM IN SAFE PRIME FIELDS
#
###############################################################################

@doc Markdown.doc"""
    IdxCalc(a::gfp_(fmpz_)elem, b::gfp_(fmpz_)elem, F=parent(a)) -> Tupel{fmpz, Nemo.Galois(Fmpz)Field} 

Tries to find $g$ s.th. $a^g == b$ where $a$ is primitive element of $F$.
"""
function IdxCalc(a::T, b::T, F=parent(a)) where T<:Union{gfp_elem, gfp_fmpz_elem} #RingElem better?
    @assert parent(a) === parent(b)
    b==1 && return fmpz(0)
    b==a && return fmpz(1)
    set_attribute!(F, :a=>a)
    typeof(get_attribute(F, :Logdict))==Nothing || @goto Logdict
    typeof(get_attribute(F, :RelMat))==Nothing || @goto RelMat
    #test if 'a' a generator?
    #Sieve
    sieve(F)
    @label RelMat
    p = get_attribute(F, :p)
    _modulus = div((p-1),2)
    two = fmpz(2)
    F2 = GF(_modulus)
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
    log_dict(F, A, TA)
    @label Logdict
    logb = log(F, b)
    #wrong log with solvemod(loga, logb, p)
    if a != get_attribute(F, :p_elem)
        p = get_attribute(F, :p)
        loga = log(F, a)
        logb = solvemod(loga, logb, p-1)
    end
    return logb, F 
end