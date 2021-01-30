# workaround a bug in flint
function _inv(a::Union{fmpz_mod_mat, nmod_mat})
  R = base_ring(a)
  y = Hecke.lift(a)
  m, d = pseudo_inv(y)
  return change_base_ring(R, m) * inv(R(d))
end

function _val(m::nmod, p)
  if m == 0
    return inf
  end
  return valuation(lift(m), p)
end


function _min_val(M, p)
  L = [_val(a, p) for a in M]
  return minimum(L)
end

@doc Markdown.doc"""
    _last_block_index(G::nmod_mat, p) -> Integer

Return the starting index of the last modular block.
Assumes that $G$ is a block diagonal matrix.
"""
function _last_block_index(G::nmod_mat, p)
  n = nrows(G)
  val = _min_val(G[n,:], p)
  val_current = val
  for k in 1:n-1
    val_current = _min_val(G[n-k,:], p)
    if val != val_current
      return n-k+1, val, val_current
    end
  end
  return 1, val, val_current
end

@doc Markdown.doc"""
    _Hensel_qf(Z::nmod_mat, G::nmod_mat, F::nmod_mat, a, b, p)

The real worker for `Hensel_qf`.

  - $Z,G,F$ -- symmetric `n \times n` matrices
  - $a,b$ -- integers with $a<b$
We require that the triple $(Z, G, F)$ is $a$-adapted.

OUTPUT:

a matrix `Fl` such that `(Z, G, Fl)` is $b$-adapted
in particular $F \equiv Flift \mod p^b$.
"""
function _Hensel_qf(Z::nmod_mat, G::nmod_mat, F::nmod_mat, a, b, p)
  #@req _min_val(Z-F*G*F',p)>=a,"input must be adapted"
  i, s1, s2 = _last_block_index(G, p)
  Z = divexact(Z, p^s1)
  G = divexact(G, p^s1)
  s = s2 - s1
  if s == 0
    @assert i == 1
    s = b-a
  end
  if p == 2
    _Hensel_qf_modular = _Hensel_qf_modular_even
  else
    _Hensel_qf_modular = _Hensel_qf_modular_odd
  end
  Zn = Z[i:end,i:end] - F[i:end,1:i-1]*G[1:i-1,1:i-1]*F[i:end,1:i-1]'
  Gn = G[i:end,i:end]
  F[i:end,i:end] = _Hensel_qf_modular(Zn, Gn, F[i:end,i:end], a, b)
  K = _inv(G[i:end,i:end]*F[i:end,i:end]')
  if i == 1
    return F
  end
  while a < b
    # an extra line that recomputes the upper block diagonal
    # if the input really is adapted this should not be necessary
    # but in any case it does not hurt
    F[1:i-1,i:end] = (Z[1:i-1,i:end] - F[1:i-1,1:i-1]*G[1:i-1,1:i-1]*F[i:end,1:i-1]') * K
    Zn = Z[1:i-1,1:i-1] - F[1:i-1,i:end]*G[i:end,i:end]*F[1:i-1,i:end]'
    F[1:i-1,1:i-1] = _Hensel_qf(Zn, G[1:i-1,1:i-1], F[1:i-1,1:i-1], a, a+s, p)
    F[1:i-1,i:end] = (Z[1:i-1,i:end] - F[1:i-1,1:i-1]*G[1:i-1,1:i-1]*F[i:end,1:i-1]') * K
    a = a + s
  end
  return F
end

@doc Markdown.doc"""
    _Hensel_qf_modular_odd(Z::nmod_mat, G::nmod_mat, F::nmod_mat, a, b)

Helper function for `_Hensel_qf`.

`Z,G` are assumed to be modular symmetric matrices
We require that the triple `(Z,G,F)` is `a`-adapted.
"""
function _Hensel_qf_modular_odd(Z::nmod_mat, G::nmod_mat, F::nmod_mat, a, b)
  while a < b
    Y = divexact(Z - F*G*F', 2)
    F = F + Y*_inv(G*F')
    a = 2 * a
  end
  return F
end

function _solve_X(Y::nmod_mat, b, g, ker=false)
  F = FiniteField(2)
  Y = change_base_ring(F, lift(Y))
  b = [F(lift(i)) for i in b]
  g = [F(lift(i)) for i in g]
  return _solve_X(Y, b, g, ker)
end

@doc Markdown.doc"""_solve_X(Y::gfp_mat, b, g, ker=false) -> gfp_mat
    Solve a certain linear equation mod `2`.

This is a helper function for `_Hensel_qf_modular_even`.

$$Y = X + X^T$$

$$b_i = X_{ii} + \sum_{j=1}^n X_{ij}g_j \quad i \in \{1, \dots, n\}$$
"""
function _solve_X(Y::gfp_mat, b, g, ker=false)
  k = base_ring(Y)
  Y = matrix(k, nrows(Y), ncols(Y), [k(lift(a)) for a in Y])'

  @req(Y == Y', "Y must be symmetric")
  @req(ncols(Y)==nrows(Y), "Y must be a square matrix")
  #@req base_ring(b)==k,
  #@req base_ring(g)==k,
  n = ncols(Y)

  equations = []
  for i in 1:n
    R = zero_matrix(k, n, n)
    R[i,:] = g
    R[i,i] += 1
    eqn = [a for a in R']
    push!(eqn, b[i])
    push!(equations, eqn)
  end
  # equations to a symmetric matrix
  for i in 1:n
    for j in i+1:n
      R = zero_matrix(k, n, n)
      R[i, j] = 1
      R[j, i] = 1
      eq = [a for a in R']
      push!(eq, Y[i, j])
      push!(equations, eq)
    end
  end
  r = size(equations)[1]
  l = size(equations[1])[1]
  equations = [i for i in Iterators.flatten(equations)]
  A = matrix(k,r,l, equations)
  c = A[:, l]
  A = A[:, 1:end-1]
  # A*Xcoeff == c
  _, Xcoeff = can_solve_with_solution(A, c, side=:right)
  X = matrix(k, n, n, [a for a in Xcoeff'])
  if ker
    Ker = []
    r, K = right_kernel(A)
    for i in 1:r
      X = matrix(k, n, n, [a for a in K[:,i]])
      push!(Ker, X)
    end
    return Ker
  end
  # confirm the computation
  @assert Y == X + X'
  for i in 1:n
    @assert b[i] == X[i,i] + sum([X[i,j]*g[j] for j in 1:n])
  end
  return X
end

@doc Markdown.doc"""Hensel_qf(G::nmod_mat, F::nmod_mat, a, b, p)
Lift `F` modulo `p^n` satisfying `G == F * G * F'`.

- `G` -- a block diagonal matrix of the form
`[G0*p^n0, G1*p^n1, ... , Gk*p^nk]`
with integers `nk < .... < n1 < n0`
and `Gi` unimodular and symmetric.
- `F` -- invertible `p`-adic matrix
  such that `(G, G, F)` is `a`-adapted
- `a` -- integer the starting precision
- `b`-- integer the target precision

OUTPUT:

- `Fk` -- the lift of `F` such that
  `Z == F * G * F'` modulo `p^n` with `n = prec`
"""
function Hensel_qf(G::nmod_mat, F::nmod_mat, a, b, p)
  # Input checks
  @req(isunit(det(F)), "F must be invertible")
  @req(ncols(G)== ncols(F) & nrows(G) == nrows(F), "G, F must have the same size")
  @req(base_ring(G) == base_ring(F), "not the same basering")
  @req(G == G', "G must be symmetric")
  R = base_ring(G)
  #n = modulus(R)
  #@req(b > n,"Desired precision is higher than base ring precision")
  for k in 1:ncols(G)-1
    n1 = _min_val(G[k,:], p)
    n2 = _min_val(G[k+1,:], p)
    @req(n1 >= n2, "block valuations must be descending")
  end
  @req(_min_val(F*G*F'-G, p) >= a,"F must satisfy Z == F * G * F'  modulo p^a.")
  if p == 2 & a==1
    @req(_min_val(diagonal(F*G*F'-G), p) >= a+1,"input is not adapted")
  end
  if ncols(F) == 0
    return F
  end
  # the real worker
  F = _Hensel_qf(G, G, F, a, b, p) #works inplace
  return F
end

@doc Markdown.doc"""_block_indices_vals(G::nmod_mat, p)
Return a list of indices and a list of valuation of the homogeneous blocks.

`G` is assumed to be a symmetric `p`-adic block diagonal matrix with modular blocks
which have descending valuations.
"""
function _block_indices_vals(G::nmod_mat, p)
  indices = []
  valuations = []
  while ncols(G) != 0
    i, val, _ = _last_block_index(G, p)
    push!(indices, i)
    push!(valuations, val)
    G = G[1:i-1,1:i-1]
  end
  reverse!(indices)
  reverse!(valuations)
  return indices, valuations
end




#=
r"""
    Helper function for `_Hensel_qf`.

    Deals with the case that `G` is modular and `p=2`.

    INPUT:

    - `Z` -- symmetric `p`-adic `n \times n` matrix
    - `G` -- symmetric `p`-adic `n \times n` matrix
    - `F` -- symmetric `p`-adic `n \times n` matrix
    - `a` -- integer
    - `b` -- integer

    We require that the triple `(Z, G, F)` is `a`-adapted.

    OUTPUT:

    - `Fl` such that `(Z, G, Fl)` is `b`-adapted
    - raises a `ValueError` if `F` cannot be lifted
"""
=#
function _Hensel_qf_modular_even(Z::nmod_mat, G::nmod_mat, F::nmod_mat, a, b)
  n = ncols(Z)
  @req(a != 0, "a must be a non-zero integer")
  if a == 1
    R = base_ring(Z)
    v = _min_val(G, 2)
    G = divexact(G, 2^v)
    Z = divexact(Z, 2^v)
    Y = Z - F*G*F'
    X = _solve_X(divexact(Y, 2), [divexact(y, 4) for y in diagonal(Y)], diagonal(_inv(G)))
    X = 2 * change_base_ring(R, lift(X))
    F = F + X*_inv(G*F')
    a = 2
  end
  while a < b
    Y = Z - F*G*F'
    for i in 1:n
      #Y[i,i+1:end] = 0
      for j in i+1:ncols(Y)
        Y[i, j] = 0
      end
      Y[i,i] = divexact(Y[i,i], 2)
    end
    F = F + Y*_inv(G*F')
    a = 2*a - 1
  end
  # confirm computation
  @assert _min_val(Z-F*G*F', 2) >= b
  @assert _min_val(diagonal(Z-F*G*F'),2) >= b + 1
  return F
end

