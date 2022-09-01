###############################################################################
#
#   PREPROCESSING (FOR WIEDEMANN)
#
###############################################################################

function sp_prepro_1(A::SMat{T}, TA::SMat{T}, l) where T
  n,m = A.r, TA.r
  done = false
  while !done
    done = true
    for j = l+1:m
      if length(TA[j])==1 
        done = false
        i = TA[j].pos[1]           
        empty_col!(TA,A,i)
        A.nnz-=length(A[i])
        empty!(A[i].pos); empty!(A[i].values)
      end
    end
  end
  A = delete_zero_rows!(A)
  TA = transpose(A)
  A = transpose(delete_zero_rows!(TA,l+1))
  return A, TA
end

########## mods ##########
function sp_prepro_k(A::SMat{T}, TA::SMat{T}, l, k) where T <: Union{fmpz_mod, nmod, gfp_elem, gfp_fmpz_elem} #prepro for cols with k>1
  @assert k > 1
  m = TA.r
  done = false
  while !done
    done = true
    for j = l+1:m
      if length(TA[j]) == k
        done = false
        S = sort([(TA[j].pos[i],TA[j].values[i]) for i=1:k], by=x->length(A[x[1]]), rev=true)
        (p,u) = S[1]
        for i in 2:k
          add_scaled_col!(TA, A, p, S[i][1], -divexact(S[i][2],u)) #add P to Q -> Q = Q - v/u *P
        end
        empty_col!(TA, A, p)
        for i in 2:k
          add_scaled_row!(A, p, S[i][1], -divexact(S[i][2],u))
        end
        A.nnz-=length(A[p]) 
        empty!(A[p].pos); empty!(A[p].values)
      end
    end 
  end
  A = delete_zero_rows!(A)
  TA = transpose(A)
  A = transpose(delete_zero_rows!(TA,l+1))      
  return A, TA
end

########## Integers ##########
function sp_prepro_k(A::SMat{T}, TA::SMat{T}, l, k) where T <: Union{fmpz, Integer}
  @assert k > 1
  m = TA.r
  done = false
  while !done
    done = true
    for j = l+1:m
      if length(TA[j]) == k
        done = false
        S = sort([(TA[j].pos[i],TA[j].values[i]) for i=1:k], by=x->length(A[x[1]]), rev=true)
        (p,u) = S[1]
        for i in 2:k
          scale_col!(TA, A, S[i][1], u)
          add_scaled_col!(TA, A, p, S[i][1], -S[i][2]) #add P to Q -> Q = Q - v *P
        end
        empty_col!(TA, A, p)
        for i in 2:k
          scale_row!(A, S[i][1], u)
          add_scaled_row!(A, p, S[i][1], -S[i][2])
        end
        A.nnz-=length(A[p]) 
        empty!(A[p].pos); empty!(A[p].values)
      end
    end 
  end
  A = delete_zero_rows!(A)
  TA = transpose(A)
  A = transpose(delete_zero_rows!(TA,l+1))      
  return A, TA
end 

########## preprocessing ##########
function sp_prepro(A::SMat{T}, TA::SMat{T}, l, iter=5) where T
  A, TA = sp_prepro_1(A, TA, l)
  for k in 2:iter
    A, TA = sp_prepro_k(A, TA, l, k)
  end
  return A, TA
end