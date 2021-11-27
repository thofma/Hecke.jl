################################################################################
#
#  indefinite LLL reduction
#
################################################################################

@doc Markdown.doc"""
    mathnf(A::MatElem) -> MatElem, MatElem
    
    Given a rectangular matrix $A$ of dimension nxm with n != m. 
    The function computes the Hessian matrix $H$ of dimension 
    nxm and the unimodular transformation matrix $U$ such that A U = H.
"""
function mathnf(A::MatElem)
    
    H, U = hnf_with_transform(reverse_cols(A'))
    H = reverse_rows(reverse_cols(H'))
    U = reverse_cols(U')

    return H, U
end


@doc Markdown.doc"""
    complete_to_basis(v::MatElem, redflag = 0) -> MatElem

    Given a rectangular matrix nxm with n != m and redflag = 0.
    Computes a unimodular matrix with the last column equal to v. 
    If redflag = 1, it LLL-reduce the n-m first columns if n > m.
"""
function complete_to_basis(v::MatElem, redflag = 0)
    
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

@doc Markdown.doc"""
    ker_mod_p(M::MatElem,p) -> Int, MatElem

    Computes the kernel of the given matrix $M$ mod $p$. 
    It returns [rank,U], where rank = dim (ker M mod p) and $U$ in GLn(Z),
    The first $rank$ columns of $U$ span the kernel.
"""
function ker_mod_p(M::MatElem,p)
    ring = parent(M[1,1])
    rank, ker = kernel(change_base_ring(ResidueRing(ring,p),M))
    U = complete_to_basis(lift(ker[:,1:rank]))
    reverse_cols!(U)

    return rank, U    
end

L = MatrixSpace(ZZ,5,4)
S = MatrixSpace(ZZ,3,4)
w = L([ 0 2  3  0 ; -5 3 -5 -5; 4 3 -5  4; 1 2 3 4; 0 1 0 0])
v = S([ 0 2  3  0; -5 3 -5 -5; 4 3 -5  4])


