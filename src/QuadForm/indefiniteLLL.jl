
################################################################################
#
#                       indefinite LLL reduction
#
################################################################################

################################################################################
#                  Helpful
################################################################################

#=
  _round_matrix(M::MatElem) -> MatElem

Returns the matrix $M$ where all entries are replaced by their rounded values.

$Example$
==========
julia> _round_matrix(QQ[1//3 -2 3//2; 5//3 0 -6; -7//3 -81//50 0])
[0 -2 2]
[2 0 -6] 
[-2 -2 0]
=#
function _round_matrix(M::MatElem)
  return map_entries(round, M)
end


#=
  _abs_matrix(M::MatElem) -> MatElem

Returns the matrix $M$ where all entries are replaced by their absolute values.

$Example$
==========
julia> _abs_matrix(ZZ[1 -2 3; 4 0 -6; -7 -81 0])
[1 2 3]
[4 0 6] 
[7 81 0]
=#
function _abs_matrix(M::MatElem)
    return map_entries(abs, M)
end

#=
  vecextract(M::MatElem,x::Int64,y::Int64) -> MatElem

Extracts components of $M$ with regards to the binary representation of $x$ and $y$. 
The location of the one entries give the position of the entries which should be extracted.
For example if $x$ = $y$ = 13 = (1101)_2 then M[[1,3,4], [1,3,4]] is returned.

$Example$
==========
julia> vecextract(ZZ[1 2 3; 4 5 6; 7 8 9],6,3)
[4 5]
[7 8]
=#
function _vecextract(M::MatElem,x::Int64,y::Int64)
  x_bin = digits(x,base = 2)
  y_bin = digits(y, base = 2)

  list_x = [i for i = 1:length(x_bin) if x_bin[i] == 1]
  list_y = [i for i = 1:length(y_bin) if y_bin[i] == 1]

  return M[list_x , list_y]

end

function _vecextract(M::MatElem, x::Union{Int64,Vector{Int64}},y::Int64)
  y_bin = digits(y, base = 2)
  list_y = [i for i = 1:length(y_bin) if y_bin[i] == 1]

  return M[x , list_y]

end

################################################################################
#                           linear algebra
################################################################################

#=
    _mathnf(A::MatElem) -> MatElem, MatElem

Given a rectangular matrix $A$ of dimension $nxm$. Computes the Hessian matrix $H$ of dimension $nxm$ 
and the unimodular transformation matrix $U$ such that $AU$ = $H$.
=#
function _mathnf(A::MatElem)
  H, U = hnf_with_transform(reverse_cols(transpose(A)))
  H = reverse_rows(reverse_cols(transpose(H)))
  U = reverse_cols(transpose(U))

  return H, U
end

#=
    _complete_to_basis(v::MatElem; redflag::Bool = false) -> MatElem

Given a rectangular matrix $nxm$ with $n$ != $m$ and redflag = 0.
Computes a unimodular matrix with the last column equal to the last column of $v$.
If redflag = 1, it LLL-reduce the $n$-$m$ first columns if $n$ > $m$.
=#
function _complete_to_basis(v::MatElem, redflag::Bool = false)
  
  n = nrows(v) #Number of rows
  m = ncols(v) #Number of cols

  if(n == m) #return nxn matrices
    return v
  end

  U = inv(transpose(_mathnf(transpose(v))[2]))

  if(n == 1 || redflag == false)
    return U
  end

  re = U[:,1:n-m]
  re = transpose(lll_with_transform(transpose(re))[2])

  l = diagonal_matrix(re,one(parent(v[1:m,1:m])))
  re = U*l

  return re
end

#=
    _ker_mod_p(M::MatElem,p) -> Int, MatElem

Computes the kernel of the given matrix $M$ mod $p$.
It returns [$rank$,$U$], where $rank$ = dim (ker M mod p) and $U$ in $GL_n$(Z),
The first $rank$ columns of $U$ span the kernel.; check::Bool = false
=#
function _ker_mod_p(M::MatElem,p)
  R = parent(M[1,1])
  rk, k = kernel(change_base_ring(ResidueRing(R,p),M))
  U = _complete_to_basis(lift(k[:,1:rk]))
  reverse_cols!(U)

  return rk, U
end

################################################################################
#                           Quadratic Equations
################################################################################

#=
    _quad_form_solve_triv(G::MatElem{fmpz}; base::Bool = false) -> MatElem{fmpz}

Trying to solve $G$ = 0 with small coefficients. Works if $det$($G$) = 1, dim <= 6
and $G$ is LLL-reduced. Return [$G$,$I_n$] if no solution is found.
Exit with a norm 0 vector if one such is found.
If base = 1 and a norm 0 vector is obtained, returns $transpose$($H$)*$G$*$H$, 
$H$, $sol$ where $sol$ is of norm 0 vand is the first column of $H$.
=#
function _quad_form_solve_triv(G::MatElem{fmpz}, base::Bool = false)
  n = ncols(G)
  H = one(parent(G))

  #Case 1: A basis vector is isotropic
  for i = 1:n
    if(G[i,i] == 0)
      sol = H[:,i]
      if(base == false)
        return sol
      end
      H[:,i] = H[:,1]
      H[:,1] = sol

      return transpose(H)*G*H, H, sol
    end
  end

  #Case 2: G has a block +- [1 0 ; 0 -1] on the diagonal
  for i = 2:n
    if(G[i-1,i] == 0 && G[i-1,i-1]*G[i,i] == -1)
  
      H[i-1,i] = -1
      sol = H[:,i]
      if (base == false)
        return sol
      end
      H[:,i] = H[:,1]
      H[:,1] = sol
        return transpose(H)*G*H, H, sol
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
    sol = vcat(sol,zero_matrix(base_ring(sol),n-i,1))
    if (base == false)
      return sol
    end
    H = _complete_to_basis(sol)
    H[:,n] = - H[:,1]
    H[:,1] = sol
    
    return transpose(H)*G*H, H, sol
  end

  return G,H
end

################################################################################
#                           Quadratic Forms Reduction
################################################################################

@doc Markdown.doc"""
    quadratic_form_lll_gram_indef(G::MatElem{fmpz}, base=0) 
                                              -> Tuple{MatElem{fmpz}, MatElem{fmpz}}

Given a Gram matrix `G` of an indefinite quadratic lattice with $det(G) != 0$.
Return the LLL-reduction of `G` or find an isotropic vector.
"""
function quad_form_lll_gram_indef(G::MatElem{fmpz}, base::Bool = false)
  n = ncols(G)
  M = one(parent(G))
  QD = G
  MS = identity_matrix(QQ,n)

  # GSO breaks off if one of the basis vectors is isotropic
  for i = 1:n-1
    if(QD[i,i] == 0)
      return _quad_form_solve_triv(G,base)
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
  QD = transpose(M)*_abs_matrix(QD)*M
  QD = QD*denominator(QD)
  QD_cont = divexact(QD,content(QD))
  QD_cont = change_base_ring(base_ring(G),QD_cont)
  rank_QD = rank(QD_cont)

  S = transpose(lll_gram_with_transform(QD_cont)[2])
  S = S[:,ncols(S)-rank_QD+1:ncols(S)]

  if(ncols(S) < n)
    S = _complete_to_basis(S)
  end

  red = _quad_form_solve_triv(transpose(S)*G*S,base)

  if(typeof(red) <: MatElem)
    r1 = S*red
    return r1
  end

  r1 = red[1]
  r2 = S*red[2]

  if(length(red) == 3)
    r3 = S*red[3]
    return r1,r2,r3
  end

  return r1,r2
end


@doc Markdown.doc"""
    quad_form_lll_gram_indefgoon(G::MatElem{fmpz}, check::Bool = false) 
                                              -> Tuple{MatElem{fmpz}, MatElem{fmpz}}

Perform the LLL-reduction of the indefinite Gram matrix `G` which goes on even if an 
isotropic vector is found. If check = true, the function checks if `G` is indeed indefinite,
symmetric and $det(G) != 0$. 
"""
function quad_form_lll_gram_indefgoon(G::MatElem{fmpz}, check::Bool = false)

  if(check == true)
    if(issymmetric(G) == false || det(G) == 0 || _isindefinite_gram_matrix(change_base_ring(QQ,G)) == false)
      error("Input should be a symmetric, invertible, indefinite matrix.")
    end
  end
  red = quad_form_lll_gram_indef(G,true)
  
  #If no isotropic vector is found
  if (length(red) == 2)
    return red
  end

  U1 = red[2]
  G2 = red[1]
  U2 = _mathnf(G2[1,:])[2]
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
    V = _vecextract(G4, [1,n] , 1<<(n-1)-2)
  end

  B = _round_matrix(-inv(change_base_ring(QQ,U))*V)
  U4 = one(parent(G))

  for j = 2:n-1
    U4[1,j] = B[1,j-1]
    U4[n,j] = B[2,j-1]
  end

  G5 = transpose(U4)*G4*U4

  # The last column of G5 is reduced
  if (n  < 4)
    return G5, U1*U2*U3*U4
  end

  red = quad_form_lll_gram_indefgoon(G5[2:n-1,2:n-1])
  One = identity_matrix(ZZ,1)
  U5 = diagonal_matrix(One,red[2],One)
  G6 = transpose(U5)*G5*U5

  return G6, U1*U2*U3*U4*U5
end
 
#=
    isindefinite_gram_matrix(A::MatElem{fmpq}) -> Bool

Takes a Gram-matrix and returns true if it is indefinite and otherwise false.
Computes the gram schmidt orthoganlisation and checks if the diagonal 
elements have all the same sign.
=#
function _isindefinite_gram_matrix(A::MatElem{fmpq})
  O, M = Hecke._gram_schmidt(A,QQ)
  d = diagonal(O)
  if sign(d[1]) == 0
    return true
  end
  bool = any(x -> sign(x) != sign(d[1]),d)
  return bool
end

