export howell_form2

# we assume that B has at least as many rows as columns
function howell_form2(A::nmod_mat)
  #A = deepcopy(B)
  n = A.r
  m = A.c
  if n < m
    A = vcat(A, MatrixSpace(base_ring(A), m-n, m)())
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
  T = MatrixSpace(base_ring(A), 1, A.c)()
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
