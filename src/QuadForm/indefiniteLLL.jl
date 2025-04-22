###############################################################################
#
#  Indefinite LLL-reduction
#
#  This is (with permission) a port of the program qfsolve.gp by Denis
#  Simon which implemented an algorithm published in
#  D. Simon, Solving quadratic equations using reduced unimodular quadratic
#  forms, Mathematics of Computation, Volume 74, Number 251, January 2005,
#  Pages 1531-1543. (https://www.jstor.org/stable/4100193)
#
###############################################################################

###############################################################################
#
#  Helpful functions
#
###############################################################################

"""
  _mathnf(A::MatElem{ZZRingElem}) -> MatElem{ZZRingElem}, MatElem{ZZRingElem}

Given an integer matrix `A`, compute the lower triangular Hermite normal form
`H` of `transpose(A)` and a unimodular transformation matrix `U` such that
`AU` = `transpose(H)`.
"""
function _mathnf(A::MatElem{ZZRingElem})
  H, U = hnf_with_transform(reverse_cols(transpose(A)))
  H = reverse_rows(reverse_cols(transpose(H)))
  U = reverse_cols(transpose(U))
  return H, U
end

"""
    _is_indefinite(A::MatElem{QQFieldElem}) -> Bool

Given a full-rank symmetric matrix `A` with rational entries, return whether
non-degenerate quadratic form with Gram matrix `A` is indefinite.
"""
function _is_indefinite(A::MatElem{QQFieldElem})
  O, M = Hecke._gram_schmidt(A,QQ)
  d = diagonal(O)
  if sign(d[1]) == 0
    return true
  end
  bool = any(x -> sign(x) != sign(d[1]),d)
  return bool
end

"""
  _complete_to_basis(v::MatElem{ZZRingElem}; redflag::Bool = false)
                                                      -> MatElem{ZZRingElem}

Given a rectangular matrix nxm with `n < m`, compute a unimodular matrix
with the last row equal to the last row of `v`.
If `v` is a square matrix, return the identity matrix of size nxn.
If `redflag` is set to `true`, it LLL-reduces the `m-n` first rows.
"""
function _complete_to_basis(v::MatElem{ZZRingElem}, redflag::Bool = false)

  n = nrows(v)
  m = ncols(v)

  if n == m
    return identity_matrix(v)
  end

  U = inv(_mathnf(v)[2])

  if m == 1 || !redflag || n > m
    return U
  end

  re = U[1:m-n, :]
  re = lll_with_transform(re)[2]

  l = diagonal_matrix(re,one(parent(v[1:n,1:n])))
  re = l*U

  return re
end

###############################################################################
#
#  Solving indefinite quadratic equations
#
###############################################################################

"""
    _quadratic_form_solve_triv(G::MatElem{ZZRingElem}; base::Bool = false)
                                                         -> MatElem{ZZRingElem},
                                                            MatElem{ZZRingElem},
                                                            MatElem{ZZRingElem}


Given a full-rank symmetric matrix `G` with integer entries, try to compute
an isotropic vector for the integral quadratic form with Gram matrix `G`.

Return `G, I, sol` where `I` is the identity matrix and `sol` is an isotropic
vector. If no isotropic vector is found, `sol` is by default an empty vector.

If `base` is set to `true` and an isotropic vector `sol` is found, return
`H * G * H^T`, `H` and `sol` where `H` is unimodular matrix of base change
whose first row is equal to `sol`.
"""
function _quadratic_form_solve_triv(G::MatElem{ZZRingElem}; base::Bool = false,
                                                            check::Bool = false)

  @req !check || (is_symmetric(G) && det(G) != 0) "G must be non-degenerate and symmetric."

  n = ncols(G)
  H = identity_matrix(base_ring(G),n)

  #Case 1: A basis vector is isotropic
  for i = 1:n
    if G[i,i] == 0
      sol = H[i:i, :]
      if !base
        return G, H, sol
      end
      H[i:i,:] = H[1:1,:]
      H[1:1,:] = sol

      return H*G*transpose(H), H, sol
    end
  end

  #Case 2: G has a block +- [1 0 ; 0 -1] on the diagonal
  for i = 2:n
    if G[i-1,i] == 0 && abs(G[i-1,i-1])==1 &&abs(G[i,i])==1 && sign(G[i-1,i-1])*sign(G[i,i]) == -1

      H[i,i-1] = -1
      sol = H[i:i,:]
      if !base
        return G, H, sol
      end
      H[i:i,:] = H[1:1,:]
      H[1:1,:] = sol

      return H*G*transpose(H), H, sol
    end
  end

  #Case 3: a principal minor is 0
  for i = 1:n
    GG = G[1:i,1:i]
    if det(GG) != 0
      continue
    end
    sol = kernel(GG, side = :left)[1:1,:]
    sol = divexact(sol,content(sol))
    sol = hcat(sol,zero_matrix(base_ring(sol),1,n-i))
    if !base
      return G, H, transpose(sol)
    end
    H = _complete_to_basis(sol)
    H[n:n,:] = - H[1:1,:]
    H[1:1,:] = sol

    return H*G*transpose(H), H, sol
  end

  return G, H, ZZRingElem[]
end

###############################################################################
#
#  Reduction of indefinite form
#
###############################################################################

@doc raw"""
    lll_gram_indef_isotropic(G::MatElem{ZZRingElem}, base::Bool = false)
                                                        -> MatElem{ZZRingElem},
                                                           MatElem{ZZRingElem},
                                                           MatElem{ZZRingElem}}

Given a full-rank symmetric matrix `G` with integer entries which defines the
Gram matrix of an indefinite integral quadratic form `L`, return `G`, `I` and
`sol` where `I` is the identity matrix and `sol` is an isotropic vector of `L`,
if such a vector is found.

If no isotropic vector of `L` is found, compute an LLL-reduced basis `U` of `L`
and return `G`, the LLL-reduced basis matrix `U` and the empty vector `ZZRingElem[]`.

If `base` is set to `true`, the first output is replaced by `U*G*transpose(U)`,
the Gram matrix of `L` with respect to `U`.

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
      M1[j,i] = - QD[i,j]//QD[i,i]
    end

    M1[i,i] = 1
    M = M1*M
    QD = M1*QD*transpose(M1)
  end

  M = inv(M)
  QD = M*map_entries(abs, QD)*transpose(M)
  QD = QD*denominator(QD)
  QD_cont = divexact(QD,content(QD))
  QD_cont = change_base_ring(ZZ,QD_cont)
  rank_QD = rank(QD_cont)

  S = lll_gram_with_transform(QD_cont)[2]
  S = S[nrows(S)-rank_QD+1:nrows(S), :]

  if nrows(S) < n
    S = _complete_to_basis(S)
  end

  red = _quadratic_form_solve_triv(S*G*transpose(S); base = base)
  r1 = red[1]
  r2 = red[2]*S
  r3 = red[3]

  if r3 != ZZRingElem[]
    r3 = r3*S
    return r1, r2, r3
  end

  return r1, r2, r3
end

@doc raw"""
    lll_gram_indef_with_transform(G::MatElem{ZZRingElem}; check::Bool = false)
                                                        -> MatElem{ZZRingElem},
                                                           MatElem{ZZRingElem}

Given a full-rank symmetric matrix `G` with integer entries which defines the
Gram matrix of an non-degenerate indefinite integral quadratic form `L`, compute
an LLL-reduced basis `U` of `L` and return `(G', U)` where `G'` is the Gram
matrix of `L` with respect to `U`.

Note: if `G` is not unimodular, eventually the algorithm has to be applied
more than once.

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

  @req !check || (is_symmetric(G) && det(G) != 0 && _is_indefinite(change_base_ring(QQ,G))) "Input should be a non-degenerate indefinite Gram matrix."

  red = lll_gram_indef_isotropic(G; base = true)

  #If no isotropic vector is found
  if red[3] == ZZRingElem[]
    return red[1] , red[2]
  end

  U1 = red[2]
  G2 = red[1]
  U2 = transpose(_mathnf(G2[1:1,:])[2])
  G3 = U2*G2*transpose(U2)

  #The first line of the matrix G3 only contains 0, except some 'g' on the right, where g² | det G.
  n = ncols(G)
  U3 = identity_matrix(ZZ,n)
  U3[n,1] = round(ZZRingElem, - G3[n,n]//2*1//G3[1,n])
  G4 = U3*G3*transpose(U3)

  #The coeff G4[n,n] is reduced modulo 2g
  U = G4[[1,n],[1,n]]

  if n == 2
    V = zero_matrix(ZZ,n,1)
  else
    V = G4[[1,n], 2:(n-1)]
  end

  B = map_entries(x->round(ZZRingElem, x), -inv(change_base_ring(QQ,U))*V)
  U4 = identity_matrix(ZZ,n)

  for j = 2:n-1
    U4[j,1] = B[1,j-1]
    U4[j,n] = B[2,j-1]
  end

  G5 = U4*G4*transpose(U4)

  # The last column of G5 is reduced
  if n  < 4
    return G5, U4*U3*U2*U1
  end

  red = lll_gram_indef_with_transform(G5[2:n-1,2:n-1])
  One = identity_matrix(ZZ,1)
  U5 = diagonal_matrix(One,red[2],One)
  G6 = U5*G5*transpose(U5)

  return G6, U5*U4*U3*U2*U1
end

@doc raw"""
    lll_gram_indef_ternary_hyperbolic(G::MatElem{ZZRingElem}; check::Bool = false)
                                                        -> MatElem{ZZRingElem},
                                                           MatElem{ZZRingElem}

Given a full-rank symmetric matrix `G` with integer entries which defines the
Gram matrix of a non-degenerate ternary hyperbolic integral quadratic form `L`,
compute an LLL-reduced basis `U` of `L` and return `(G', U)` where `G'` is the
Gram matrix of `L` with respect to `U`.

# Examples
```jldoctest
julia> G = ZZ[1 0 0; 0 4 3; 0 3 2];

julia> lll_gram_indef_ternary_hyperbolic(G)
([0 0 -1; 0 1 0; -1 0 0], [-1 -1 0; 0 0 -1; -2 -1 0])
```
"""
function lll_gram_indef_ternary_hyperbolic(G::MatElem{ZZRingElem}; check::Bool = false)

  @req !check || (is_symmetric(G) && ncols(G) != 3 && _check_for_lll_gram_indefinite2(change_base_ring(QQ, G))) "Input should be the Gram matrix of a non-degenerate indefinite integral form of rank 3"

  e = det(G) == -1 ? 1 : -1

  red = lll_gram_indef_isotropic(e*G; base = true)

  #We always find an isotropic vector
  U1 = ZZ[0 0 1; 0 1 0; 1 0 0]
  G2 = U1*red[1]*transpose(U1)

  #G2 has a 0 at the bottom right corner
  g = gcdx(G2[3,1],G2[3,2])
  U2 = ZZ[g[2] g[3] 0; G2[3,2]//g[1] -G2[3,1]//g[1] 0; 0 0 -1]
  G3 = U2*G2*transpose(U2)

  #G3 has 0 under the codiagonal
  cc = mod(G3[1,1],2)
  U3 = ZZ[1 cc round(-(G3[1,1]+cc*(2*G3[1,2]+G3[2,2]*cc))//2//G3[1,3]); 0 1 round(-(G3[1,2]+cc*G3[2,2])//G3[1,3]); 0 0 1]

  return e*U3*G3*transpose(U3), red[2]*U3*U2*U1
end

function _check_for_lll_gram_indefinite2(A::MatElem{QQFieldElem})
  O, M = Hecke._gram_schmidt(A,QQ)
  d = [sign(O[i,i]) for i=1:3]
  if abs(sum(d)) != 1 || any(i -> d[i] == 0,1:3)
    return false
  end
  return true
end

