
################################################################################
#
#                       indefinite LLL reduction
#
################################################################################


################################################################################
#                           linear algebra
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


#Invariants computations check: myhilbertsymbol == hilbert_symbol & qflocalinvariant == hasse_invariant
# qfbreduce == Hecke.reduction_with_transformation

################################################################################
#                           Quadratic Forms Reduction
################################################################################

function abs_matrix(M::MatElem)
    n = nrows(M)
    m = ncols(M)

    L = zero(parent(M))
    for i = 1:n
        for j = 1:m 
            L[i,j] = abs(M[i,j])
        end
    end

    return L
end



@doc Markdown.doc"""
    quadratic_form_lll_gram_indef(G::MatElem,base=0) -> Dict{Int64, MatElem}
    Performs a LLL-reduction on a positive definite quadratic form QD bounding the indefinite G
    Then finishes the reduction with 
"""
function quad_form_lll_gram_indef(G::MatElem,base=0)
    n = ncols(G)
    M = one(parent(G))
    QD = G

    MS = MatrixSpace(FractionField(base_ring(G)),n,n)

    for i = 1:n-1
        
        if(QD[i,i] == 0)
            return quad_form_solve_triv(G, base)
        end
        
        M1 = one(MS)
        for j = 1:n
            M1[i,j] = - QD[i,j]//QD[i,i]
        end
        M1[i,i] = 1
        
        M = M*M1
        QD = M1'*QD*M1
    
    end

    M = inv(M)

    QD = M'*abs_matrix(QD)*M 
    QD = QD*denominator(QD)
    QD_cont = divexact(QD,content(QD))
    QD_cont = change_base_ring(base_ring(G),QD_cont)
    
    rank_QD = rank(QD_cont)
    
    S = lll_gram_with_transform(QD_cont)[2]'
    S = S[:,ncols(S)-rank_QD+1:ncols(S)]
  
    if(ncols(S) < n)
        S = complete_to_basis(S)
    end

    red = quadratic_form_solve_triv(S'*G*S,base)
    
    if(length(red) == 1)
        red[1] = S*red[1]
        return  red
    end

    red[2] = S*red[2]

    if(length(red) == 3)
        red[3] = S*red[3]
    end

    return red

end

################################################################################
#                           Quadratic Equations
################################################################################

@doc Markdown.doc"""
    quadratic_form_solve_triv(G, base = 0) -> Dictionary{Int64, MatElem} 

    Trying to solve G = 0 with small coefficients. Works if det(G) = 1, dim <= 6 and G is LLL-reduced.
    Return G,Identity if no solution is found. Exit with a norm 0 vector if one such is found.
    If base = 1 and norm 0 is obtained returns H'*G*H, H, sol 
    where sol is a norm 0 vector and is the 1st column of H.
"""
function quad_form_solve_triv(G, base = 0)
    n = ncols(G)
    H = one(parent(G))
   

    #Case 1: A basis vector is isotropic
    for i = 1:n
        if(G[i,i] == 0)
            
            sol = H[:,i]
            if(base == 0)
                d = Dict([1 => sol])
                return d
            end
            H[:,i] = H[:,1]
            H[:,1] = sol

            d = Dict([ 1 => H'*G*H, 2 => H , 3 => sol])
            return d
        end
    end

    #Case 2: G has a block +- [1 0 ; 0 -1] on the diagonal
    for i = 2:n
        if(G[i-1,i] == 0 && G[i-1,i-1]*G[i,i] == -1)
           
            H[i-1,i] = -1
            sol = H[:,1]
            if (base == 0)
                d = Dict([1 => sol])
                return d
            end 
            H[:,i] = H[:,1]
            H[:,1] = sol

            d = Dict([ 1 => H'*G*H, 2 => H , 3 => sol])
            return d
        end
    end
    
    
    #Case 3: a principal minor is 0
    for i = 1:n
        
        GG = G[1:i,1:i]
        if(det(GG) != 0)
            continue
        end
    
        sol = kernel(GG)[2][:,1]
        sol = divexact(sol,content(sol))
        sol = vcat(sol,zero(GG,n-i,1))

        if (base == 0)
            d = Dict([1 => sol])
            return d
        end
        
        H = complete_to_basis(sol)
        H[:,n] = - H[:,1]
        H[:,1] = sol
        
        d = Dict([ 1 => H'*G*H, 2 => H , 3 => sol])
        return d
    end

    d = Dict([1 => G, 2 => H])
    return d
end


L = MatrixSpace(ZZ,2,2)
M = MatrixSpace(ZZ,3,3)
G = L([5 -2 ;-2 5])
H = M([3 1 1; 1 0 1; 1 1 1])
#r = quad_form_lll_gram_indef(G)
r2 = quad_form_lll_gram_indef(H)



#L = MatrixSpace(ZZ,5,4)
#S = MatrixSpace(ZZ,3,4)
#A = MatrixSpace(ZZ,4,4)

#u = A([1 2 0 0; 2 1 0 0; 0 0 1 0; 0 0 0 1])
#w = L([ 0 2  3  0 ; -5 3 -5 -5; 4 3 -5  4; 1 2 3 4; 0 1 0 0])
#v = S([ 0 2  3  0; -5 3 -5 -5; 4 3 -5  4])
