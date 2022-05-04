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
                delete_col(TA,A,i)
                A.nnz-=length(A[i])
                empty!(A[i].pos); empty!(A[i].values)
            end
        end
    end
    A = delete_zero_rows(A)
    TA = transpose(A)
    A = transpose(delete_zero_rows(TA,l+1))
    return A, TA
end

########## mods ##########
function sp_prepro_k(A::SMat{T}, TA::SMat{T}, l, k) where T <: Union{fmpz_mod, nmod, gfp_elem, gfp_fmpz_elem} #prepro for cols with k>1
    @assert k > 1
    n,m = A.r, TA.r
    done = false
    while !done
        done = true
        for j = l+1:m
            if length(TA[j]) == k
                done = false
                S = sort([(TA[j].pos[i],TA[j].values[i]) for i=1:k], by=x->length(A[x[1]]), rev=true)
                (p,u) = S[1]
                for i in 2:k
                    add_scaled_col_trans!(TA, A, p, S[i][1], -divexact(S[i][2],u)) #add P to Q -> Q = Q - v/u *P
                end
                delete_col(TA, A, p)
                for i in 2:k
                    add_scaled_row!(A, p, S[i][1], -divexact(S[i][2],u))
                end
                A.nnz-=length(A[p]) 
                empty!(A[p].pos); empty!(A[p].values)
            end
        end 
    end
    A = delete_zero_rows(A)
    TA = transpose(A)
    A = transpose(delete_zero_rows(TA,l+1))      
    return A, TA
end

########## Integers ##########
function sp_prepro_k(A::SMat{T}, TA::SMat{T}, l, k) where T <: Union{fmpz, Integer}
    @assert k > 1
    n,m = A.r, TA.r
    done = false
    while !done
        done = true
        for j = l+1:m
            if length(TA[j]) == k
                done = false
                S = sort([(TA[j].pos[i],TA[j].values[i]) for i=1:k], by=x->length(A[x[1]]), rev=true)
                (p,u) = S[1]
                for i in 2:k
                    scale_col_trans!(TA, A, S[i][1], u)
                    add_scaled_col_trans!(TA, A, p, S[i][1], -S[i][2]) #add P to Q -> Q = Q - v *P
                end
                delete_col(TA, A, p)
                for i in 2:k
                    scale_row!(A, S[i][1], u)
                    add_scaled_row!(A, p, S[i][1], -S[i][2])
                end
                A.nnz-=length(A[p]) 
                empty!(A[p].pos); empty!(A[p].values)
            end
        end 
    end
    A = delete_zero_rows(A)
    TA = transpose(A)
    A = transpose(delete_zero_rows(TA,l+1))      
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



###############################################################################
#
#   AUXILIARY STUFF
#
###############################################################################

function add_scaled_row!(A::SMat{T}, i::Int, j::Int, c::T) where T
    A.nnz = A.nnz - length(A[j])
    A.rows[j] = add_scaled_row(A[i], A[j], c)
    A.nnz = A.nnz + length(A[j])
    return A
end
function add_scaled_col!(A::SMat{T}, i::Int, j::Int, c::T) where T #A.nnz was not adapted
    @assert c != 0
  
    @assert 1 <= i <= ncols(A) && 1 <= j <= ncols(A)  
  
    for r in A.rows
      if i in r.pos
        i_i = findfirst(isequal(i), r.pos) #changed
        val_i = r.values[i_i]
        if j in r.pos
          i_j = findfirst(isequal(j), r.pos) #changed
          val_j = r.values[i_j]
  
          r.values[i_j] += c*r.values[i_i]
        else
          k = searchsortedfirst(r.pos, j)
          insert!(r.pos, k, j)
          insert!(r.values, k, c*r.values[i_i])
          A.nnz+=1  #added
        end
      end
    end
    return A
end
function scale_col_trans!(A, TA, j, c) #A[_j]->c*A[_,j]
    for i in TA[j].pos
        idx_j = findfirst(isequal(j), A[i].pos)
        A[i].values[idx_j]*=c
    end
    return A
end
function add_scaled_col_trans!(A, TA, i, j, c) #A[_j]->c*A[_,i]+A[_j]
    @assert c != 0
    @assert 1 <= i <= TA.r && 1 <= j <= TA.r

    for idx in TA[i].pos #indiziert Zeilen, die Eintrag iin Spalte i haben
        idx_i = findfirst(isequal(i), A[idx].pos) #indiziert i in position Array von A[idx]
        if idx in TA[j].pos
            idx_j = findfirst(isequal(j), A[idx].pos) #indiziert j in position Array von A[idx]
            A[idx].values[idx_j] += c*A[idx].values[idx_i]
        else
            k = searchsortedfirst(A[idx].pos, j)
            insert!(A[idx].pos, k, j)
            insert!(A[idx].values, k, c*A[idx].values[idx_i])
            A.nnz+=1
        end
    end
    return A
end
function delete_row(A, i) 
    non_zeros = length(A[i].pos)
    deleteat!(A.rows, i)
    A.r-=1
    A.nnz-=non_zeros
    return A
end
function delete_rows(A, I, sorted=true) #elements in I need to be ascending
    if !sorted
        sort(I)
    end
    for i in length(I):-1:1
        delete_row(A, I[i])
    end
    return A
end
function delete_zero_rows(A, s=1) #where s denotes the first column where we wanna start
    for i=A.r:-1:s
        if A[i].pos == []
            deleteat!(A.rows, i); A.r-=1
        end
    end
    return A
end
function delete_small_rows(A, s=1)
    for i=A.r:-1:s
        if length(A[i].pos) < 2 
            deleteat!(A.rows, i); A.r-=1
        end
    end
    return A
end
function delete_col(A, TA, j) #only deletes entries in column j, output same size as input
    for row in TA[j].pos 
        i = findfirst(isequal(j), A[row].pos)
        deleteat!(A[row].pos, i) ; deleteat!(A[row].values, i)
    end
    A.nnz -=length(TA[j].pos)
    return A
end
function delete_cols(A, TA, J)
    for j in J
        delete_col(A, TA, j)
    end
    return A
end