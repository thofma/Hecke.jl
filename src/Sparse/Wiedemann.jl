using AbstractAlgebra
import AbstractAlgebra.evaluate #cannot import AbstractAlgebra stuff in Sparse.jl

function wiedemann(A::SMat{gfp_elem}, TA::SMat{gfp_elem}) #N::fmpz || N::Int64
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
	seq[1] = dot(randlin,c,zero!(z)) #randlin*c 		
	for i = 2:2*n  #Wiedemann sequence 2m?
        c =  Hecke.mul!(c,TA, Hecke.mul!(storing_n,A,c))
		seq[i] = dot(randlin,c) 
	end

	done,f = Hecke_berlekamp_massey(seq)
	delta =0
	while iszero(coeff(f,0)) #TODO collect coeffs:
		delta+=1
		f = divexact(f,gen(parent(f)))
	end
	constpartoff = coeff(f,0)
	a = -inv(constpartoff)
	reducedf = divexact(f-constpartoff,gen(parent(f)))
	#f(TA*A)'c
    v = evaluate(reducedf,TA,A,y).*a
    return (v-r)
end

function wiedemann(A::SMat{gfp_fmpz_elem}, TA::SMat{gfp_fmpz_elem}) #N::fmpz || N::Int64
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
	seq[1] = dot(randlin,c,zero!(z)) #randlin*c 		
	for i = 2:2*n  #Wiedemann sequence
        c =  multi!(c,TA, multi!(storing_n,A,c))
		seq[i] = dot(randlin,c) 
	end
    ##########################################################################################################################################
	done,f = Hecke_berlekamp_massey(seq)
	delta =0
	while iszero(coeff(f,0))
		delta+=1
		f = divexact(f,gen(parent(f)))
	end
	constpartoff = coeff(f,0)
	a = -inv(constpartoff)
	reducedf = divexact(f-constpartoff,gen(parent(f)))
    #f(TA*A)'c
    v = evaluate(reducedf,TA,A,y).*a
    return (v-r)
end

function evaluate(f,TA,A::SMat{gfp_elem},c)
    #return f(A^t *A)*c
	T = elem_type(base_ring(A))
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

function evaluate(f,TA,A::SMat{gfp_fmpz_elem},c)
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

function Hecke_berlekamp_massey(L)#::Vector{fmpz})
	# from Hecke\U6dsX\src\Sparse\Matrix.jl
	 RR = parent(L[1])
	 Ry,x = PolynomialRing(RR, "x", cached = false) ## Ring over TZZ
     lg = length(L)
     L = [lift(L[lg-i]) for i in 0:lg-1]
     g = Ry(L)
     if iszero(g)
       return true, g
     end
     f = x^lg
     N = lift((inv(leading_coefficient(g)))); g1 = g*N
     v0 = Ry(); v1 = Ry(1)
     while lg <= 2*degree(g1)
       q,r = divrem(f,g1)
       if r==0
         N = lift(1)
       else
         N = lift(inv(leading_coefficient(r)))
       end
       v = (v0-q*v1)*N
       v0 = v1; v1 = v; f = g1; g1= r*N
     end
     return true, divexact(v1, leading_coefficient(v1))
end

function multi!(c::Vector{gfp_fmpz_elem}, A::SMat{gfp_fmpz_elem}, b::Vector{gfp_fmpz_elem})
    t = fmpz()
    for (i, r) in enumerate(A)
      c[i] = dot_experimental!(c[i],r,b,t)
    end
    return c
end

function dot_experimental!(s::gfp_fmpz_elem, sr::SRow{gfp_fmpz_elem}, a::Vector{gfp_fmpz_elem},t::fmpz)
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