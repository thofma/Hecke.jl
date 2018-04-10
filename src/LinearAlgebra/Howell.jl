export howell_form2

# we assume that B has at least as many rows as columns
function howell_form2(A::nmod_mat)
  #A = deepcopy(B)
  n = A.r
  m = A.c
  if n < m
    A = vcat(A, zero_matrix(base_ring(A), m-n, m))
  end
  for j in 1:m
    for i in j+1:n
      #print("Computing xgcd of $(_raw_getindex(A,j,j)), $(_raw_getindex(A,i,j))\n")
      g,s,t,u,v = _xxgcd(_raw_getindex(A,j,j),_raw_getindex(A,i,j),A._n)
      #println("$g $s $t $u $v ")
      for k in 1:m
        t1 = s*_raw_getindex(A,j,k) + t*_raw_getindex(A, i, k)
        t2 = u*_raw_getindex(A,j,k) + v*_raw_getindex(A, i, k)
        t1 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), t1, A._n, A._ninv)
        t2 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), t2, A._n, A._ninv)
        ccall((:nmod_mat_set_entry, :libflint), Void, (Ptr{nmod_mat}, Int, Int, UInt), &A, j - 1, k - 1, t1)
        ccall((:nmod_mat_set_entry, :libflint), Void, (Ptr{nmod_mat}, Int, Int, UInt), &A, i - 1, k - 1, t2)
      end
    end
    #println(A)
  end
  #println("I have a triangular matrix:")
  #println(A)
  T = zero_matrix(base_ring(A), 1, A.c)
  for j in 1:m
    if _raw_getindex(A,j,j) != 0
      #println("nonzero case")
      u = _unit(_raw_getindex(A,j,j), A._n)
      for k in 1:m
        t1 = mod(u*_raw_getindex(A,j,k), A._n)
        ccall((:nmod_mat_set_entry, :libflint), Void, (Ptr{nmod_mat}, Int, Int, UInt), &A, j - 1, k - 1, t1)
      end
      #println("Multiplied row $j with $u and obtained \n$A\n")
      for i in 1:j-1
        #println("ich nehme zeile $j und reduziere damit zeile $i")
        #println("zeile $i: $(window(A, i:i, 1:m))")
        #println("zeile $j: $(window(A, j:j, 1:m))")
        #println("A[$i,$j]: $(_raw_getindex(A,i,j)) A[$j,$j]: $(_raw_getindex(A,j,j))")
        #println("A[$i,$j]: $(A[i,j]) A[$j,$j]: $(A[j,j])")
        q = UInt(prem(- Int(div(_raw_getindex(A, i, j), _raw_getindex(A, j, j))), Int(A._n)))
        #println("quotient ist $q")
        for k in j:m
          #println("adjusting row $i, divinding by $(_raw_getindex(A, j, j))")
          #println("I am replacing A[$i,$k] with")
          #println("A[$i,$j]: $(_raw_getindex(A,i,j)) A[$j,$j]: $(_raw_getindex(A,j,j))")
          #println("quotient is $(UInt(prem(- Int(div(_raw_getindex(A, i, j), _raw_getindex(A, j, j))), Int(A._n))))")
          #print(_raw_getindex(A, i, k) + UInt(prem(- Int(div(_raw_getindex(A, i, j), _raw_getindex(A, j, j))), Int(A._n))) *_raw_getindex(A, j, k))
          #println()
          _raw_setindex(A, i, k, mod(_raw_getindex(A, i, k) + q *_raw_getindex(A, j, k), A._n))
        end
      end
      #print("computing the annihilator for $j ... ")
      l = mod(div(A._n,gcd(_raw_getindex(A,j,j),A._n)),A._n)
      #println("annihilator is $l")
      if l == 0
        continue
      end
      for k in 1:m
        _raw_setindex(T, 1, k, mod(l*_raw_getindex(A,j,k), A._n))
      end
    else
      for k in 1:m
        _raw_setindex(T, 1, k, _raw_getindex(A,j,k))
      end
    end
    #println("T looks like: $T")
    #println("Augmented matrix looks like \n$A\n$T\n")
    for i in j+1:m 
      g,s,t,u,v = _xxgcd(_raw_getindex(A,i,i),_raw_getindex(T,1,i),A._n)
      for k in 1:m
        t1 = s*_raw_getindex(A,i,k) + t*_raw_getindex(T, 1, k)
        t2 = u*_raw_getindex(A,i,k) + v*_raw_getindex(T, 1, k)
        t1 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), t1, A._n, A._ninv)
        t2 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), t2, A._n, A._ninv)
        ccall((:nmod_mat_set_entry, :libflint), Void, (Ptr{nmod_mat}, Int, Int, UInt), &A, i - 1, k - 1, t1)
        ccall((:nmod_mat_set_entry, :libflint), Void, (Ptr{nmod_mat}, Int, Int, UInt), &T, 0, k - 1, t2)
      end
    end
    #println("After reducing with T the augmented matrix looks like \n$A\n$T\n")
 
  end
  #return A
end

function _raw_setindex(A::nmod_mat, i::Int, j::Int, x::UInt)
  ccall((:nmod_mat_set_entry, :libflint), Void, (Ptr{nmod_mat}, Int, Int, UInt), &A, i - 1, j - 1, x)
end

function _stab(a::UInt, b::UInt, N::UInt)
  g = gcd(a,b,N)
  _, c = ppio(div(N,g),div(a,g))
  #c = prem(c,N)
  return c
end

function _unit(a::UInt, N::UInt)
  g,s,_ = gcdx(a,N)
  if g == 1
    return rem(s,N)
  else
    l = div(N,g)
    d = _stab(s,l,N)
    return rem(s + d*l,N)
  end
end

function _xxgcd(a::UInt, b::UInt, N::UInt)
  g,s,t = gcdx(Int(a),Int(b))
  if g == 0
    return (UInt(0), UInt(1), UInt(0), UInt(0), UInt(1))
  end
  u = UInt(prem(-div(Int(b),g),Int(N)))
  g = UInt(g)
  v = div(a,g)
  return (g,UInt(prem(s,Int(N))),UInt(prem(t,Int(N))),u,v)
end

################################################################################
#
#  positive remainder
#
################################################################################

function prem(a::Integer, m::T) where T<:Integer
  b = a % m
  if b < 0
    return m+b
  else
    return b
  end
end

function prem(a::fmpz, m::T) where T
  return prem(BigInt(a), m)
end



###############################################################################
#
#  Howell form for Generic.Mat{fmpz}
#
###############################################################################
     
     
function _xxgcd(a::fmpz, b::fmpz, N::fmpz)
  g,s,t = gcdx(a,b)
  if g == 0
    return (fmpz(0), fmpz(1), fmpz(0), fmpz(0), fmpz(1))
  end
  u = mod(-div(b,g),N)
  v = div(a,g)
  return (g,mod(s,N),mod(t,N),u,v)
end

function _unit(a::fmpz, N::fmpz)
  g,s,_ = gcdx(a,N)
  if g == 1
    return mod(s,N)
  else
    l = div(N,g)
    d = _stab(s,l,N)
    return mod(s + d*l,N)
  end
end

function _stab(a::fmpz, b::fmpz, N::fmpz)
  g = gcd(gcd(a,b),N)
  _, c = ppio(div(N,g),div(a,g))
  return c
end

function howell_form(A::Generic.Mat{Nemo.Generic.Res{Nemo.fmpz}})
  B=deepcopy(A)
  if rows(B)<cols(B)
    B=vcat(B, zero_matrix(base_ring(B), cols(B)-rows(B), cols(B)))
  end
  howell_form!(B)
  return B
end


#
#  for the in-place function, the number of rows must be at least equal to the number of columns
#


function howell_form!(A::Generic.Mat{Nemo.Generic.Res{Nemo.fmpz}})
  
  R=base_ring(A)
  n=R.modulus

  #
  #  Get an upper triangular matrix 
  #
  
  for j=1:cols(A)
    for i=j+1:cols(A)
      g,s,t,u,v = _xxgcd(A[j,j].data,A[i,j].data,n)
      for k in 1:cols(A)
        t1 = s* A[j,k] + t* A[i,k]
        t2 = u* A[j,k] + v* A[i,k]
        A[j,k] = t1
        A[i,k] = t2
      end
    end
  end

  #
  #  Multiply the rows by annihlator of the pivot element and reduce 
  #
  
  T = zero_matrix(R, 1, cols(A))
  for j in 1:cols(A)
    if A[j,j] != 0
       u = _unit(A[j,j].data, n)
      for k in 1:cols(A)
        A[j,k]=u*A[j,k]
      end
      for i in 1:j-1
        q = div(A[i,j].data, A[j,j].data)
        for k in j:cols(A)
          A[i,k]-= q*A[j,k]
        end
      end
      l = div(n,gcd(A[j,j].data,n))
      if l == 0
        continue
      end
      for k in j:cols(A)
       T[1,k]=l*A[j,k]
      end
    else
      for k in j:cols(A)
        T[1, k]= A[j,k]
      end
    end
    for i in j:cols(A) 
      g,s,t,u,v = _xxgcd(A[i,i].data, T[1,i].data,n)
      for k in 1:cols(A)
        t1 = s*A[i,k] + t*T[1,k]
        t2 = u*A[i,k] + v*T[1,k]
        A[i,k]= t1
        T[1,k]=t2
      end
    end
  end
  if iszero_row(A,rows(A))
    for i=1:cols(A)
      A[rows(A),i]=T[1,i]
    end
  end
end

function triangularize!(A::Generic.Mat{Nemo.Generic.Res{Nemo.fmpz}})

  R=base_ring(A)
  n=R.modulus

  #
  #  Get an upper triangular matrix 
  #
  
  for j=1:cols(A)
    for i=j+1:cols(A)
      g,s,t,u,v = _xxgcd(A[j,j].data,A[i,j].data,n)
      for k in 1:cols(A)
        t1 = s* A[j,k] + t* A[i,k]
        t2 = u* A[j,k] + v* A[i,k]
        A[j,k] = t1
        A[i,k] = t2
      end
    end
  end

end

function triangularize(A::Generic.Mat{Nemo.Generic.Res{Nemo.fmpz}})
  B= triangularize!(deepcopy(A))
  return B
end


function Base.nullspace(M::Generic.Mat{Nemo.Generic.Res{Nemo.fmpz}})

  R = base_ring(M)
  #
  #  If the modulus is prime, the second part of the Howell form computation is useless and I can directly call the rref
  #  but I have to test if the modulus is prime. What is better?
  #
  N = hcat(M', identity_matrix(R, cols(M)))
  N = howell_form(N)
  if gcd(prod([N[i,i] for i=1:rows(N)]).data,modulus(R))==1
    return 0, MatrixSpace(R,cols(M),1, false)
  end
  nr = 1
  while nr <= rows(N) && !iszero_row(N, nr)
    nr += 1
  end
  nr -= 1
  h = sub(N, 1:nr, 1:rows(M))
  for i=1:rows(h)
    if iszero_row(h, i)
      k = sub(N, i:rows(h), rows(M)+1:cols(N))
      return k', rows(k)
    end
  end
  
  
end

