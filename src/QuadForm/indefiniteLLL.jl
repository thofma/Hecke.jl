export completebasis
export mathnf

################################################################################
#
#  indefinite LLL reduction
#
################################################################################

# Gives the Hessian Matrix (H) and a unimodular transformation matrix (U) such that AU = H.

function mathnf(A::MatElem)
    
    H, U = hnf_with_transform(reverse_cols(A'))
    H = reverse_rows(reverse_cols(H'))
    U = reverse_cols(U')

    return H, U
end

#Gives a unimodular matrix with the last column(s) equal to v.
#v can be a column vector or a rectangular matrix.
#redflag = 0 or 1. If redflag = 1, LLL-reduce the n-#v first columns.

function completebasis(v::MatElem, redflag = 0)
    
    if(redflag != 1 && redflag != 0)
        error("Wrong second input.")
    end
    n = nrows(v) #Number of rows
    m = ncols(v) #Number of cols
        
    if(n == m) #return nxn matrices
        return v
    end
    
    U = inv(mathnf(v')[2]')
       
    if(n == 1 || n-m < 0 || redflag == 0)
        return U
    end

    re = lll(U[:,1:n-m])
    l = hcat(re,vcat(zero(parent(U2[1:n-m,1:m])),one(U2[1:m,1:m])))
    re = U*l

    return re
end


