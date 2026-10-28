some_nullspace(A::SMat) = wiedemann(A::SMat, transpose(A)::SMat)

#(p-1)/2 prime 
@doc raw"""
    wiedemann(A::SMat{fpFieldElem}, TA::SMat{fpFieldElem}) ->Vector{fpFieldElem}

Computes ker($A$).
"""
function wiedemann(A::SMat{T}, TA::SMat{T}) where T <:Union{fpFieldElem, FpFieldElem, zzModRingElem, ZZModRingElem} #N::Int64
		RR = base_ring(A)
		N = modulus(RR)
		(n,m) = nrows(A),ncols(A)
		# Prealloc +Randomchoice
		r = rand(RR, m)
		c = rand(RR, m)
		randlin = rand_srow(min(m,10),m,min(10,N),RR)
		seq = zeros(RR, 2*m)
		storing_n = zeros(RR, n)
		storing_m =  zeros(RR, m)
		z = zero(RR)
		#Wiedemann sequence
		# solve A^tAx = A^tAr = y => x -r in kernel(A^tA) to avoid finding zero vec
		y = my_mul!(storing_m,TA, my_mul!(storing_n,A,r))
		seq[1] = dot(randlin,c,z) #randlin*c
		for i = 2:2*m  #Wiedemann sequence 2m?
				c = my_mul!(c,TA, my_mul!(storing_n,A,c))
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

function wiedemann(A::SMat{T}) where T <:Union{fpFieldElem, FpFieldElem, zzModRingElem, ZZModRingElem} #A square matrix
 RR = base_ring(A)
 N = modulus(RR)
 n = nrows(A)
 # Prealloc +Randomchoice
 r = rand(RR, n)
 c = rand(RR, n)
 randlin = rand_srow(min(n,10),n,min(10,N),RR)
 seq = zeros(RR, 2*n)
 storing_n = zeros(RR, n)
 z = zero(RR)
 #Wiedemann sequence
 # solve A^tAx = A^tAr = y => x -r in kernel(A^tA) to avoid finding zero vec
 y = my_mul!(storing_n,A,r)
 seq[1] = dot(randlin,c,z) #randlin*c 		
 for i = 2:2*n  #Wiedemann sequence 2m?
   c = my_mul!(c,A, my_mul!(storing_n,A,c))
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
 v = Hecke.evaluate(reducedf,A,y).*a
 return true, (v-r)
end

function Hecke.evaluate(f,TA::SMat{T},A::SMat{T},c) where T <:Union{fpFieldElem, FpFieldElem, zzModRingElem, ZZModRingElem}
  #return f(A^t *A)*c
		(n,m) = size(A)
  RR = base_ring(A)
		storing_n = zeros(RR, n)
  s =  zeros(RR, m)
		C = collect(coefficients(f))
		n = length(C)
		s =  my_mul!(s,TA, my_mul!(storing_n,A,c)).*C[end]+c.*C[end-1]
		for i = n-2:-1:1
				s =  my_mul!(s,TA, my_mul!(storing_n,A,s)) + c.*C[i]
		end
		return s
end

function Hecke.evaluate(f,A::SMat{T},c) where T <:Union{fpFieldElem, FpFieldElem, zzModRingElem, ZZModRingElem}
 #return f(A^t *A)*c
 n = nrows(A)
 RR = base_ring(A)
 storing_n = zeros(RR, n)
 s =  zeros(RR, n)
 C = collect(coefficients(f))
 n = length(C)
 s =  my_mul!(s,A,c).*C[end]+c.*C[end-1]
 for i = n-2:-1:1
   s =  my_mul!(s,A,s) + c.*C[i]
 end
 return s
end

function rand_srow(l,n,b,R)
		#generate ZZRingElem sparse_row, indx not greater than n limited by n
		#l values not greater than b
		val =  rand(1:b,l)
		pos = Hecke.randperm!(Vector{Int}(undef, n))[1:l]
		return sparse_row(R,pos,val)
end

function rand_vec(l,n,RR)
 v = zeros(RR, n)
 pos = rand(1:n, l)
 for i in pos
  v[i] = rand(RR)
 end
 return v
end

function multi!(c::Vector{T}, A::SMat{T}, b::Vector{T}) where T <:Union{FpFieldElem, ZZModRingElem}
		t = ZZRingElem()
		for (i, r) in enumerate(A)
				c[i] = dot_experimental!(c[i],r,b,t)
		end
		return c
end

function dot_experimental!(s::T, sr::SRow{T}, a::Vector{T},t::ZZRingElem) where T <:Union{FpFieldElem, ZZModRingElem}
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

function multi2!(c::SRow{T}, A::SMat{T}, b::SRow{T}) where T <:Union{FpFieldElem, ZZModRingElem}
 #t = ZZRingElem()
 for (i, r) in enumerate(A)
   c[i] = dot_experimental2!(c[i],r,b)
 end
 return c
end

function dot_experimental2!(v::T, A::SRow{T}, B::SRow{T},t=ZZRingElem()) where T <:Union{FpFieldElem, ZZModRingElem}
  @assert length(A) != 0
  m = modulus(parent(v))
  zero!(v.data)
  b = 1
  for a=1:length(A.pos)
    while b<=length(B.values) && B.pos[b] < A.pos[a]
      b += 1
    end
    if b>length(B.values)
      return v
    end
    if B.pos[b] == A.pos[a]
      Hecke.mul!(t, B.values[b].data ,A.values[a].data)
      Hecke.add!(v.data, v.data, t)
    end
  end
  mod!(v.data, v.data, m)
  return v
end

my_mul!(c::Vector{T}, A::SMat{T}, b::Vector{T}) where T <:Union{FpFieldElem, ZZModRingElem} = multi!(c, A, b)
my_mul!(c::Vector{T}, A::SMat{T}, b::Vector{T}) where T <:Union{fpFieldElem, zzModRingElem} = mul!(c, A, b)

