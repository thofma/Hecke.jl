############################################################
# This is (with permission) a port of the program qfsolve.gp by Denis
# Simon which implemented an algorithm published in
# D. Simon, Solving quadratic equations using reduced unimodular quadratic forms,
# Mathematics of Computation, Volume 74, Number 251, January 2005, Pages 1531-1543.
# (https://www.jstor.org/stable/4100193)

export lll_gram_indef_isotropic, lll_gram_indef_with_transform,
       lll_gram_indef_ternary_hyperbolic

################################################################################
#
#  Indefinite LLL reduction
#
################################################################################

################################################################################
#  Helpful
################################################################################

#=
  _mathnf(A::MatElem{ZZRingElem}) -> MatElem{ZZRingElem}, MatElem{ZZRingElem}

Given a rectangular matrix $A$ of dimension $nxm$. Compute the Hermite normal
form $H$ of dimension $nxm$ and the unimodular transformation matrix $U$ such
that $AU$ = $H$. The first n-rank(A) columns are zero and the rest are in
Gauß-form.
=#
function _mathnf(A::MatElem{ZZRingElem})
  H, U = hnf_with_transform(reverse_cols(transpose(A)))
  H = reverse_rows(reverse_cols(transpose(H)))
  U = reverse_cols(transpose(U))

  return H, U
end

#=
    _is_indefinite(A::MatElem{QQFieldElem}) -> Bool

Takes a Gram-matrix of a non-degenerate quadratic form and return true if the
form is indefinite and otherwise false.
=#
function _is_indefinite(A::MatElem{QQFieldElem})
  O, M = Hecke._gram_schmidt(A,QQ)
  d = diagonal(O)
  if sign(d[1]) == 0
    return true
  end
  bool = any(x -> sign(x) != sign(d[1]),d)
  return bool
end

################################################################################
#                           linear algebra
################################################################################

#=
  _complete_to_basis(v::MatElem{ZZRingElem}; redflag::Bool = false) -> MatElem{ZZRingElem}

Given a rectangular matrix $nxm$ with $n != m$, compute a unimodular matrix
with the last column equal to the last column of $v$. If redflag = true,
it LLL-reduce the $n-m$ first columns if $n > m$.
=#
function _complete_to_basis(v::MatElem{ZZRingElem}, redflag::Bool = false)
  
  n = nrows(v)
  m = ncols(v)

  if n == m
    return identity_matrix(v)
  end

  U = inv(transpose(_mathnf(transpose(v))[2]))

  if n == 1 || !redflag || m > n
    return U
  end

  re = U[:,1:n-m]
  re = transpose(lll_with_transform(transpose(re))[2])

  l = diagonal_matrix(re,one(parent(v[1:m,1:m])))
  re = U*l

  return re
end

################################################################################
#                           Quadratic Equations
################################################################################

#=
    _quadratic_form_solve_triv(G::MatElem{ZZRingElem}; base::Bool = false)
                                  -> MatElem{ZZRingElem}, MatElem{ZZRingElem}, MatElem{ZZRingElem}


Try to compute a non-zero vector in the kernel of $G$ with small coefficients.
`G` must be symmetric and non-degenerate.
Return $G,I,sol$ where $I$ is the identity matrix and $sol$ is non-trivial
norm 0 vector or the empty vector if no non-trivial vector is found.
If base = true and a norm 0 vector is obtained, return $H * G * H^T$, $H$ and
$sol$ where $sol$ is the first column of $H$ with norm 0.
=#
function _quadratic_form_solve_triv(G::MatElem{ZZRingElem}; base::Bool = false, check::Bool = false)

  if check && (!is_symmetric(G) || det(G) == 0)
      error("G must be non-degenrate and symmetric.")
  end

  n = ncols(G)
  H = identity_matrix(base_ring(G),n)

  #Case 1: A basis vector is isotropic
  for i = 1:n
    if G[i,i] == 0
      sol = H[:,i]
      if !base
        return G, transpose(H), transpose(sol)
      end
      H[:,i] = H[:,1]
      H[:,1] = sol

      return transpose(H)*G*H, transpose(H), transpose(sol)
    end
  end

  #Case 2: G has a block +- [1 0 ; 0 -1] on the diagonal
  for i = 2:n
    if G[i-1,i] == 0 && G[i-1,i-1]*G[i,i] == -1
  
      H[i-1,i] = -1
      sol = H[:,i]
      if !base
        return G, transpose(H), transpose(sol)
      end
      H[:,i] = H[:,1]
      H[:,1] = sol

      return transpose(H)*G*H, transpose(H), transpose(sol)
    end
  end

  #Case 3: a principal minor is 0
  for i = 1:n
    GG = G[1:i,1:i]
    if det(GG) != 0
      continue
    end
    sol = kernel(GG)[2][:,1]
    sol = divexact(sol,content(sol))
    sol = vcat(sol,zero_matrix(base_ring(sol),n-i,1))
    if !base
      return G, transpose(H), transpose(sol)
    end
    H = _complete_to_basis(sol)
    H[:,n] = - H[:,1]
    H[:,1] = sol

    return transpose(H)*G*H, transpose(H), transpose(sol)
  end

  return G, transpose(H), ZZRingElem[]
end

###############################################################################
#                           Quadratic Forms Reduction
###############################################################################

@doc raw"""
    lll_gram_indef_isotropic(G::MatElem{ZZRingElem}, base::Bool = false)
                           -> Tuple{MatElem{ZZRingElem}, MatElem{ZZRingElem}, MatElem{ZZRingElem}}

Given an indefinite Gram matrix `G` of a matrix with rational entries `M`, such that
$det(G) \neq 0$, return `G`, `I` and `sol` where `I` is the identity-matrix and
`sol` is an isotropic vector if such a vector is found.

Otherwise compute an LLL-reduction of `M` and return `G`, the transformation matrix
`U` and `ZZRingElem[]`.

If `base` is set to `true`, the first output is replaced by `U*G*transpose(U)`.

# Examples
```jldoctest
julia> G = ZZ[0 1 2; 1 -1 3; 2 3 0];

julia> lll_gram_indef_isotropic(G)
([0 1 2; 1 -1 3; 2 3 0], [1 0 0; 0 1 0; 0 0 1], [1 0 0])

julia> (ans[3]*G*transpose(ans[3]))[1] == 0
true

julia> G = ZZ[2 1 2 4;1 8 0 2;2 0 -2 5;4 2 5 0];

julia> lll_gram_indef_isotropic(G)
([2 0 1 0; 0 -4 -1 1; 1 -1 8 0; 0 1 0 -8], [1 0 0 0; -1 0 1 0; 0 1 0 0; -2 0 0 1], ZZRingElem[])
```
"""
function lll_gram_indef_isotropic(G::MatElem{ZZRingElem}; base::Bool = false)
  n = ncols(G)
  M = identity_matrix(ZZ,n)
  QD = G

  # GSO breaks off if one of the basis vectors is isotropic
  for i = 1:n-1
    if QD[i,i] == 0
      return _quadratic_form_solve_triv(G; base = base)
    end

    M1 = identity_matrix(QQ,n)
    for j = 1:n
      M1[i,j] = - QD[i,j]//QD[i,i]
    end

    M1[i,i] = 1
    M = M*M1
    QD = transpose(M1)*QD*M1
  end

  M = inv(M)
  QD = transpose(M)*map_entries(abs, QD)*M
  QD = QD*denominator(QD)
  QD_cont = divexact(QD,content(QD))
  QD_cont = change_base_ring(ZZ,QD_cont)
  rank_QD = rank(QD_cont)

  S = transpose(lll_gram_with_transform(QD_cont)[2])
  S = S[:,ncols(S)-rank_QD+1:ncols(S)]

  if ncols(S) < n
    S = _complete_to_basis(S)
  end

  red = _quadratic_form_solve_triv(transpose(S)*G*S; base = base)
  r1 = red[1]
  r2 = S*transpose(red[2])
  r3 = red[3]

  if r3 != ZZRingElem[]
    r3 = S*transpose(r3)
    return r1, transpose(r2), transpose(r3)
  end

  return r1, transpose(r2), r3
end

@doc raw"""
    lll_gram_indef_with_transform(G::MatElem{ZZRingElem}; check::Bool = false)
                                         -> Tuple{MatElem{ZZRingElem}, MatElem{ZZRingElem}}

Given an indefinite Gram matrix `G` of a matrix with rational entries `M`, such
that $det(G) \neq 0$, compute an LLL-reduction of `M` and return `(G', U)` where
`G'` is the Gram matrix associated to the reduction of `M` and `U` is the
transformation matrix. If `G` is not unimodular, eventually the algorithm
has to be applied more than once.

# Examples
```jldoctest
julia> G = ZZ[0 1 2; 1 -1 3; 2 3 0];

julia> lll_gram_indef_with_transform(G)
([0 0 1; 0 -16 0; 1 0 1], [1 0 0; 5 2 -1; 1 1 0])

julia> G = ZZ[2 1 2 4;1 8 0 2;2 0 -2 5;4 2 5 0];

julia> lll_gram_indef_with_transform(G)
([2 0 1 0; 0 -4 -1 1; 1 -1 8 0; 0 1 0 -8], [1 0 0 0; -1 0 1 0; 0 1 0 0; -2 0 0 1])
```
"""
function lll_gram_indef_with_transform(G::MatElem{ZZRingElem}; check::Bool = false)

  if check
    if !issymmetric(G) || det(G) == 0 || !_is_indefinite(change_base_ring(QQ,G))
      error("Input should be a non-degenerate indefinite Gram matrix.")
    end
  end

  red = lll_gram_indef_isotropic(G; base = true)

  #If no isotropic vector is found
  if red[3] == ZZRingElem[]
    return red[1] , red[2]
  end

  U1 = transpose(red[2])
  G2 = red[1]
  U2 = _mathnf(G2[1,:])[2]
  G3 = transpose(U2)*G2*U2

  #The first line of the matrix G3 only contains 0, except some 'g' on the right, where g² | det G.
  n = ncols(G)
  U3 = identity_matrix(ZZ,n)
  U3[1,n] = round(- G3[n,n]//2*1//G3[1,n])
  G4 = transpose(U3)*G3*U3

  #The coeff G4[n,n] is reduced modulo 2g
  U = G4[[1,n],[1,n]]

  if n == 2
    V = zero_matrix(ZZ,n,1)
  else
    V = G4[[1,n], 2:(n-1)]
  end

  B = map_entries(round, -inv(change_base_ring(QQ,U))*V )
  U4 = identity_matrix(ZZ,n)

  for j = 2:n-1
    U4[1,j] = B[1,j-1]
    U4[n,j] = B[2,j-1]
  end

  G5 = transpose(U4)*G4*U4

  # The last column of G5 is reduced
  if n  < 4
    return G5, transpose(U1*U2*U3*U4)
  end

  red = lll_gram_indef_with_transform(G5[2:n-1,2:n-1])
  One = identity_matrix(ZZ,1)
  U5 = diagonal_matrix(One,transpose(red[2]),One)
  G6 = transpose(U5)*G5*U5

  return G6, transpose(U1*U2*U3*U4*U5)
end

@doc raw"""
    lll_gram_indef_ternary_hyperbolic(G::MatElem{ZZRingElem}; check::Bool = false)
                                         -> Tuple{MatElem{ZZRingElem}, MatElem{ZZRingElem}}

Given a Gram matrix `G` of a matrix with rational entries `M`, where `G` is a 3x3 matrix
with $det(G) = -1$ and $sign(G) =  [2,1]$, compute an LLL-reduction of `M` and return
the associated Gram matrix to the reduction together with the transformation matrix.

# Examples
```jldoctest
julia> G = ZZ[1 0 0; 0 4 3; 0 3 2];

julia> lll_gram_indef_ternary_hyperbolic(G)
([0 0 -1; 0 1 0; -1 0 0], [0 1 -2; 1 0 0; 0 1 -1])
```
"""
function lll_gram_indef_ternary_hyperbolic(G::MatElem{ZZRingElem}; check::Bool = false)

  if check
    if det(G) != -1 || is_symmetric(G) == false || ncols(G) != 3 || _check_for_lll_gram_indefinite2(change_base_ring(QQ, G)) == false
      error("Input should be a Gram matrix 3x3 with det(G) = -1 and sign(G) = [2,1].")
    end
  end

  red = lll_gram_indef_isotropic(G; base = true)

  #We always find an isotropic vector
  U1 = ZZ[0 0 1; 0 1 0; 1 0 0]
  G2 = transpose(U1)*red[1]*U1

  #G2 has a 0 at the bottom right corner
  g = gcdx(G2[3,1],G2[3,2])
  U2 = ZZ[g[2] G2[3,2]//g[1] 0; g[3] -G2[3,1]//g[1] 0; 0 0 -1]
  G3 = transpose(U2)*G2*U2

  #G3 has 0 under the codiagonal
  cc = mod(G3[1,1],2)
  U3 = ZZ[1 0 0; cc 1 0;round(-(G3[1,1]+cc*(2*G3[1,2]+G3[2,2]*cc))//2//G3[1,3]) round(-(G3[1,2]+cc*G3[2,2])//G3[1,3]) 1]

  return transpose(U3)*G3*U3, transpose(U1*U2*U3)*red[2]
end

function _check_for_lll_gram_indefinite2(A::MatElem{QQFieldElem})
  O, M = Hecke._gram_schmidt(A,QQ)
  d = [sign(O[i,i]) for i=1:3]
  if sum(d) != 1 || any(i -> d[i] == 0,1:3)
    return false
  end
  return true
end

