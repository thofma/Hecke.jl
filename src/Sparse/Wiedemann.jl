some_nullspace(A::SMat) = wiedemann(A::SMat, transpose(A)::SMat)

#(p-1)/2 prime 
@doc Markdown.doc"""
    wiedemann(A::SMat{gfp_elem}, TA::SMat{gfp_elem}) ->Vector{gfp_elem}
Computes ker($A$).
"""
function wiedemann(A::SMat{gfp_elem}, TA::SMat{gfp_elem}) #N::Int64
	@info "wiedemann 1 used"
	RR = base_ring(A)
	N = modulus(RR)
	T = elem_type(RR)
	(n,m) = nrows(A),ncols(A)
	# Prealloc +Randomchoice
    r = rand(RR, m)
	c = rand(RR, m)
    randlin = rand_srow(min(m,10),m,min(10,N),RR)
	seq = Vector{T}(undef, 2*n)
	storing_n = Vector{T}(undef,n)
    storing_m =  Vector{T}(undef,m)
	z = zero(RR)
    #Wiedemann sequence
    # solve A^tAx = A^tAr = y => x -r in kernel(A^tA) to avoid finding zero vec
	y = Hecke.mul!(storing_m,TA, Hecke.mul!(storing_n,A,r))
	seq[1] = dot(randlin,c,z) #randlin*c 		
	for i = 2:2*n  #Wiedemann sequence 2m?
        c =  Hecke.mul!(c,TA, Hecke.mul!(storing_n,A,c))
		seq[i] = dot(randlin,c) 
	end

	done,f = Hecke.berlekamp_massey(seq)
	delta =0
	while iszero(coeff(f,0)) #TODO collect coeffs:
		delta+=1
		f = divexact(f,gen(parent(f)))
	end
	constpartoff = coeff(f,0)
	a = -inv(constpartoff)
	reducedf = divexact(f-constpartoff,gen(parent(f)))
	#f(TA*A)'c
    v = Hecke.evaluate(reducedf,TA,A,y).*a
    return true, (v-r)
end

@doc Markdown.doc"""
    wiedemann(A::SMat{gfp_fmpz_elem}, TA::SMat{gfp_fmpz_elem}) ->Vector{gfp_fmpz_elem}
Computes ker($A$).
"""
function wiedemann(A::SMat{gfp_fmpz_elem}, TA::SMat{gfp_fmpz_elem}) #N::fmpz
	@info "wiedemann 2 used"
    RR = base_ring(A)
	N = modulus(RR)
	T= elem_type(RR)
	#A = change_base_ring(RR, A)::SMat{T}
	(n,m) = nrows(A),ncols(A);
	# Prealloc +Randomchoice
    r = rand(RR, m)
	c = rand(RR, m)
    randlin = rand_srow(min(m,10),m,min(10,N),RR)
	seq = Vector{T}(undef, 2*n)
	storing_n = zeros(RR,n)#Vector{T}(undef,n)
    storing_m = zeros(RR,m)#Vector{T}(undef,m)
	z = zero(RR)
    #Wiedemann sequence
    # solve A^tAx = y2 => x -y in kernel(A^tA) to avoid finding zero vec
	y = multi!(storing_m,TA, multi!(storing_n,A,r))
	seq[1] = dot(randlin,c,z) #randlin*c 		
	for i = 2:2*n  #Wiedemann sequence
        c =  multi!(c,TA, multi!(storing_n,A,c))
		seq[i] = dot(randlin,c) 
	end
    ##########################################################################################################################################
	done,f = Hecke.berlekamp_massey(seq)
	delta =0
	while iszero(coeff(f,0))
		delta+=1
		f = divexact(f,gen(parent(f)))
	end
	constpartoff = coeff(f,0)
	a = -inv(constpartoff)
	reducedf = divexact(f-constpartoff,gen(parent(f)))
    #f(TA*A)'c
    v = Hecke.evaluate(reducedf,TA,A,y).*a
    return true, (v-r)
end

function wiedemann(A::SMat{T}, TA::SMat{T}) where T<:Union{nmod, fmpz_mod}
	@info "wiedemann 3 used"
    RR = base_ring(A)
	N = modulus(RR)
	#T= elem_type(RR)
	#A = change_base_ring(RR, A)::SMat{T}
	(n,m) = nrows(A),ncols(A);
	# Prealloc +Randomchoice
    r = rand(RR, m)
	c = rand(RR, m)
    randlin = rand_srow(min(m,10),m,min(10,N),RR)
	seq = Vector{T}(undef, 2*m)
	storing_n = zeros(RR,n)#Vector{T}(undef,n)
    storing_m = zeros(RR,m)#Vector{T}(undef,m)
	z = zero(RR)
    #Wiedemann sequence
    # solve A^tAx = y2 => x -y in kernel(A^tA) to avoid finding zero vec
	y = multi!(storing_m,TA, multi!(storing_n,A,r))
	seq[1] = dot(randlin,c,z) #randlin*c 		
	for i = 2:2*m  #Wiedemann sequence
        c =  multi!(c,TA, multi!(storing_n,A,c))
		seq[i] = dot(randlin,c) 
	end
    ##########################################################################################################################################
	done,f = Hecke.berlekamp_massey(seq)
	delta =0
	while iszero(coeff(f,0))
		delta+=1
		f = divexact(f,gen(parent(f)))
	end
	constpartoff = coeff(f,0)
	a = -inv(constpartoff)
	reducedf = divexact(f-constpartoff,gen(parent(f)))
    #f(TA*A)'c
    v = Hecke.evaluate(reducedf,TA,A,y).*a
    return true, (v-r)
end
#(p-1)/2 probably not prime
#=
function wiedemann(A::SMat{T}, TA::SMat{T}) where T<:Union{nmod, fmpz_mod}
	@info "wiedemann catch used"
	RR = base_ring(A)
	N = modulus(RR)
	(n,m) = nrows(A),ncols(A);
	# Prealloc +Randomchoice
    r = rand(RR, m)
	c = rand(RR, m)
    randlin = rand_srow(min(m,10),m,min(10,N),RR)
	seq = Vector{T}(undef, 2*n)
	storing_n = zeros(RR,n)#Vector{T}(undef,n)
    storing_m = zeros(RR,m)#Vector{T}(undef,m)
    #Wiedemann sequence
    # solve A^tAx = y2 => x -y in kernel(A^tA) to avoid finding zero vec
	y = mul!(storing_m,TA, mul!(storing_n,A,r))
	seq[1] = dot(randlin,c,RR(0)) #randlin*c 		
	for i = 2:2*n  #Wiedemann sequence
        c =  mul!(c,TA, mul!(storing_n,A,c))
		seq[i] = dot(randlin,c) 
	end
	#=
    coeff_ = try                     
		Hecke.berlekamp_massey(seq)
	catch
		e = false	               #TODO: assign gcd here
	end
    if !coeff_
		return false, 0
	end
	=#
	delta =0
	while iszero(coeff(f,0))
		delta+=1
		f = divexact(f,gen(parent(f)))
	end
	constpartoff = coeff(f,0)
	a = -inv(constpartoff)
	reducedf = divexact(f-constpartoff,gen(parent(f)))
    #f(TA*A)'c
    v = Hecke.evaluate(reducedf,TA,A,y).*a
    return true, (v-r)
end
=# 
function Hecke.evaluate(f,TA,A::SMat{T},c) where T <:Union{gfp_elem, nmod}
    #return f(A^t *A)*c
	#T = elem_type(base_ring(A))
	(n,m) = size(A)
	storing_n = Vector{T}(undef,n)
    s =  Vector{T}(undef,m)
	C = collect(coefficients(f))
	n = length(C)
	s =  Hecke.mul!(s,TA, Hecke.mul!(storing_n,A,c)).*C[end]+c.*C[end-1]
	for i = n-2:-1:1
		s =  Hecke.mul!(s,TA, Hecke.mul!(storing_n,A,s)) + c.*C[i]
	end
	return s
end

function Hecke.evaluate(f,TA,A::SMat{T},c) where T <:Union{gfp_fmpz_elem, fmpz_mod}
    #return f(A^t *A)*c
	R = base_ring(A)
	(n,m) = size(A)
	storing_n = zeros(R,n)#Vector{T}(undef,n)
    s =  zeros(R,m)#Vector{T}(undef,m)
	C = collect(coefficients(f))
	n = length(C)
	s =  multi!(s,TA, multi!(storing_n,A,c)).*C[end]+c.*C[end-1]
	for i = n-2:-1:1
		s =  multi!(s,TA, multi!(storing_n,A,s)) + c.*C[i]
	end
	return s
end

function rand_srow(l,n,b,R)
    #generate fmpz sparse_row, indx not greater than n limited by n
    #l values not greater than b
    val =  rand(1:b,l)
    pos = randperm!(Vector{Int}(undef, n))[1:l]
    return sparse_row(R,pos,val)
end

function multi!(c::Vector{T}, A::SMat{T}, b::Vector{T}) where T <:Union{gfp_fmpz_elem, fmpz_mod}
    t = fmpz()
    for (i, r) in enumerate(A)
      c[i] = dot_experimental!(c[i],r,b,t)
    end
    return c
end

function dot_experimental!(s::T, sr::SRow{T}, a::Vector{T},t::fmpz) where T <:Union{gfp_fmpz_elem, fmpz_mod}
    m = modulus(parent(s))
    zero!(s.data)
    zero!(t)
    for (i,v) = sr
      Hecke.mul!(t, v.data, a[i].data)
      Hecke.add!(s.data, s.data, t)
    end
    mod!(s.data, s.data, m)
    return s
end

#=
F = GF(fmpz(34589))
F2 = ResidueRing(ZZ, fmpz(17294))
a = F(2)
set_attribute!(F, :a, a)
sieve(F)
A = change_base_ring(F2, get_attribute(F,:RelMat))
TA = transpose(A)
=#