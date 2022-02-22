
################################################################################
#
#                       indefinite LLL reduction
#
################################################################################

################################################################################
#                  Helpful
################################################################################

function round_matrix(M::MatElem)
  return map_entries(round, M)
end

function abs_matrix(M::MatElem)
    return map_entries(abs, M)
end

@doc Markdown.doc"""
  vecextract(M::MatElem,x::Int64,y::Int64) -> MatElem

"""
function vecextract(M::MatElem,x::Int64,y::Int64)
  x_bin = digits(x,base = 2)
  y_bin = digits(y, base = 2)

  list_x = [i for i = 1:length(x_bin) if x_bin[i] == 1]
  list_y = [i for i = 1:length(y_bin) if y_bin[i] == 1]

  return M[list_x , list_y]

end

function vecextract(M::MatElem, x,y::Int64)
  y_bin = digits(y, base = 2)
  list_y = [i for i = 1:length(y_bin) if y_bin[i] == 1]

  return M[x , list_y]

end

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
  H, U = hnf_with_transform(reverse_cols(transpose(A)))
  H = reverse_rows(reverse_cols(transpose(H)))
  U = reverse_cols(transpose(U))

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

  U = inv(transpose(mathnf(transpose(v))[2]))

  if(n == 1 || redflag == 0)
    return U
  end

  re = U[:,1:n-m]
  re = transpose(lll_with_transform(transpose(re))[2])

  l = diagonal_matrix(re,one(parent(v[1:m,1:m])))
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

################################################################################
#                           Quadratic Equations
################################################################################

@doc Markdown.doc"""
    quad_form_solve_triv(G, base = 0) -> Dictionary{Int64, MatElem}

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
      d = Dict([ 1 => transpose(H)*G*H, 2 => H , 3 => sol])
      return d
    end
  end

  #Case 2: G has a block +- [1 0 ; 0 -1] on the diagonal
  for i = 2:n
    if(G[i-1,i] == 0 && G[i-1,i-1]*G[i,i] == -1)
      println()
      H[i-1,i] = -1
      sol = H[:,i]
      if (base == 0)
        d = Dict([1 => sol])
        return d
      end
      H[:,i] = H[:,1]
      H[:,1] = sol
      d = Dict([ 1 => transpose(H)*G*H, 2 => H , 3 => sol])
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
    d = Dict([ 1 => transpose(H)*G*H, 2 => H , 3 => sol])
    return d
  end

  d = Dict([1 => G, 2 => H])
  return d
end

################################################################################
#                           Quadratic Forms Reduction
################################################################################

@doc Markdown.doc"""
    quadratic_form_lll_gram_indef(G::MatElem,base=0) -> Dict{Int64, MatElem}

Performs a LLL-reduction on a positive definite quadratic form QD bounding the indefinite G
Then finishes the reduction with quad_form_solve_triv.
"""
function quad_form_lll_gram_indef(G::MatElem,base=0)
  n = ncols(G)
  M = one(parent(G))
  QD = G
  MS = identity_matrix(FractionField(base_ring(G)),n)

  # GSO breaks off if one of the basis vectors is isotropic
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
    QD = transpose(M1)*QD*M1
  end

  M = inv(M)
  QD = transpose(M)*abs_matrix(QD)*M
  QD = QD*denominator(QD)
  QD_cont = divexact(QD,content(QD))
  QD_cont = change_base_ring(base_ring(G),QD_cont)
  rank_QD = rank(QD_cont)

  S = transpose(lll_gram_with_transform(QD_cont)[2])
  S = S[:,ncols(S)-rank_QD+1:ncols(S)]

  if(ncols(S) < n)
    S = complete_to_basis(S)
  end

  red = quad_form_solve_triv(transpose(S)*G*S,base)

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



@doc Markdown.doc"""
    quad_form_lll_gram_indefgoon(G::MatElem) -> Dictionary{Int64, MatElem}

LLL reduction of the quadratic form G (Gram matrix)
"""
function quad_form_lll_gram_indefgoon(G::MatElem)
  red = quad_form_lll_gram_indef(G,1)
  
  #If no isotropic vector is found
  if (length(red) == 2)
    return red
  end

  U1 = red[2]
  G2 = red[1]
  U2 = mathnf(G2[1,:])[2]
  G3 = transpose(U2)*G2*U2

  #The first line of the matrix G3 only contains 0, except some 'g' on the right, where g² | det G.
  n = ncols(G)
  U3 = one(parent(G))
  U3[1,n] = round(- G3[n,n]//2*1//G3[1,n])
  G4 = transpose(U3)*G3*U3

  #The coeff G4[n,n] is reduced modulo 2g
  U = G4[[1,n],[1,n]]

  if (n == 2)
    V = zero(parent(G[:,1]))
  else
    V = vecextract(G4, [1,n] , 1<<(n-1)-2)
  end

  B = round_matrix(-inv(change_base_ring(FractionField(base_ring(U)),U))*V)
  U4 = one(parent(G))

  for j = 2:n-1
    U4[1,j] = B[1,j-1]
    U4[n,j] = B[2,j-1]
  end

  G5 = transpose(U4)*G4*U4

  # The last column of G5 is reduced
  if (n  < 4)
    d = Dict(1 => G5 , 2 => U1*U2*U3*U4)
    return d
  end

  red = quad_form_lll_gram_indefgoon(G5[2:n-1,2:n-1])
  One = one(MatrixSpace(base_ring(G)))
  U5 = diagonal_matrix(One,red[2],One)
  G6 = transpose(U5)*G5*U5

  d = Dict(1 => G6, 2 => U1*U2*U3*U4*U5)
  return d
end


