function _val(m::zzModRingElem, p)
  if m == 0
    return inf
  end
  return valuation(lift(m), p)
end


function _min_val(M, p)
  L = Union{PosInf, Int}[_val(a, p) for a in M]
  return minimum(L)
end

@doc raw"""
    _last_block_index(G::Union{zzModMatrix, ZZModMatrix}, p) -> Int, Int, Int

Return the starting index of the last modular block, as well as its valuation
and the valuation of the second to last modular block.

Assumes that $G$ is a block diagonal matrix.
"""
function _last_block_index(G::Union{zzModMatrix, ZZModMatrix}, p)
  n = nrows(G)
  val = _min_val(G[n:n,:], p)
  val_current = val
  for k in 1:n-1
    val_current = _min_val(G[(n-k):(n-k),:], p)
    if val != val_current
      return n-k+1, val, val_current
    end
  end
  return 1, val, val_current
end

@doc raw"""
    _hensel_qf(Z::T, G::T, F::T, a, b, p) where T <: Union{zzModMatrix, ZZModMatrix}

The real worker for `hensel_qf`. Input is
  - $Z, G, F$, symmetric `n \times n` matrices.
  - $a, b$, integers with $a<b$.
We require that the triple $(Z, G, F)$ is $a$-adapted.

Return a matrix `F_l` such that $(Z, G, F_l)$ is $b$-adapted in particular $F
\equiv F_l \mod p^b$.
"""
function _hensel_qf(Z::T, G::T, F::T, a, b, p) where {T <: Union{zzModMatrix, ZZModMatrix}}
  #@req _min_val(Z-F*G*transpose(F),p)>=a,"input must be adapted"
  i, s1, s2 = _last_block_index(G, p)
  R = base_ring(Z)
  Z = change_base_ring(R, divexact(lift(Z), p^s1))
  G = change_base_ring(R, divexact(lift(G), p^s1))
  s = s2 - s1
  if s == 0
    @assert i == 1
    s = b-a
  end
  even = p == 2
  Zn = Z[i:end,i:end] - F[i:end,1:i-1]*G[1:i-1,1:i-1]*transpose(F[i:end,1:i-1])
  Gn = G[i:end,i:end]
  if even
    F[i:end,i:end] = _hensel_qf_modular_even(Zn, Gn, F[i:end,i:end], a, b)
  else
    F[i:end,i:end] = _hensel_qf_modular_odd(Zn, Gn, F[i:end,i:end], a, b)
  end
  K = inv(G[i:end,i:end]*transpose(F[i:end,i:end]))
  if i == 1
    return F
  end
  while a < b
    # an extra line that recomputes the upper block diagonal
    # if the input really is adapted this should not be necessary
    # but in any case it does not hurt
    F[1:i-1,i:end] = (Z[1:i-1,i:end] - F[1:i-1,1:i-1]*G[1:i-1,1:i-1]*transpose(F[i:end,1:i-1])) * K
    Zn = Z[1:i-1,1:i-1] - F[1:i-1,i:end]*G[i:end,i:end]*transpose(F[1:i-1,i:end])
    F[1:i-1,1:i-1] = _hensel_qf(Zn, G[1:i-1,1:i-1], F[1:i-1,1:i-1], a, a+s, p)
    F[1:i-1,i:end] = (Z[1:i-1,i:end] - F[1:i-1,1:i-1]*G[1:i-1,1:i-1]*transpose(F[i:end,1:i-1])) * K
    a = a + s
  end
  return F
end

@doc raw"""
    _hensel_qf_modular_odd(Z::T, G::T, F::T, a, b)
                                        where T <: Union{zzModMatrix, ZZModMatrix}

Helper function for `_hensel_qf`. Matrices $Z$ and $G$ are assumed to be
modular symmetric matrices. We require that the triple $(Z,G,F)$ is
`a`-adapted.
"""
function _hensel_qf_modular_odd(Z::T, G::T, F::T, a, b) where {T <: Union{zzModMatrix, ZZModMatrix}}
  while a < b
    Y = divexact(Z - F*G*transpose(F), 2)
    F = F + Y*inv(G*transpose(F))
    a = 2 * a
  end
  return F
end

function _solve_X(Y::Union{zzModMatrix, ZZModMatrix}, b, g)
  F = Native.GF(2)
  Y = change_base_ring(F, lift(Y))
  b = [F(lift(i)) for i in b]
  g = [F(lift(i)) for i in g]
  return _solve_X(Y, b, g)
end

function _solve_X_ker(Y::Union{zzModMatrix, ZZModMatrix}, b, g)
  F = Native.GF(2)
  Y = change_base_ring(F, lift(Y))
  b = [F(lift(i)) for i in b]
  g = [F(lift(i)) for i in g]
  return _solve_X_ker(Y, b, g)
end

function _solve_X_get_A_and_c(Y::fpMatrix, b, g)
  k = base_ring(Y)
  Y = transpose(matrix(k, nrows(Y), ncols(Y), [k(lift(a)) for a in Y]))

  @req is_symmetric(Y) "Y must be symmetric"
  @req ncols(Y) == nrows(Y) "Y must be a square matrix"
  n = ncols(Y)

  equations = Vector{elem_type(k)}[]
  for i in 1:n
    R = zero_matrix(k, n, n)
    R[i,:] = g
    R[i,i] += 1
    eqn = reshape(collect(transpose(R)), :)
    push!(eqn, b[i])
    push!(equations, eqn)
  end
  # equations to a symmetric matrix
  for i in 1:n
    for j in i+1:n
      R = zero_matrix(k, n, n)
      R[i, j] = 1
      R[j, i] = 1
      eq = reshape(collect(transpose(R)), :)
      push!(eq, Y[i, j])
      push!(equations, eq)
    end
  end
  r = length(equations)
  l = length(equations[1])
  equations = elem_type(k)[i for i in Iterators.flatten(equations)]
  A = matrix(k,r,l, equations)
  c = A[:, l:l]
  A = A[:, 1:end-1]
  return A, c
end

@doc raw"""
    _solve_X(Y::fpMatrix, b, g, ker=false) -> fpMatrix

Solve a certain linear equation modulo $2$. This is a helper function for
`_hensel_qf_modular_even`. We find the solution $X$ such that

$$Y = X + X^t$$

and

$$b_i = X_{ii} + \sum_{j=1}^n X_{ij}g_j \quad i \in \{1, \dots, n\}.$$
"""
function _solve_X(Y::fpMatrix, b, g)
  k = base_ring(Y)
  n = ncols(Y)
  # A*Xcoeff == c
  A, c = _solve_X_get_A_and_c(Y, b, g)
  fl, Xcoeff = can_solve_with_solution(A, c, side=:right)
  @assert fl
  X = matrix(k, n, n, reshape(collect(transpose(Xcoeff)), :))
  # confirm the computation
  @hassert :Lattice Y == X + transpose(X)
  for i in 1:n
    @hassert :Lattice b[i] == X[i,i] + sum([X[i,j]*g[j] for j in 1:n])
  end
  return X
end

function _solve_X_ker(Y::fpMatrix, b, g)
  # A*Xcoeff == 0
  k = base_ring(Y)
  n = ncols(Y)
  A, c = _solve_X_get_A_and_c(Y, b, g)
  Ker = dense_matrix_type(k)[]
  K = kernel(A; side = :right)
  for i in 1:ncols(K)
    tmp = vec(collect(K[:,i]))
    X = matrix(k, n, n, tmp)
    push!(Ker, X)
  end
  return Ker
end

@doc raw"""
    hensel_qf(G::T, F::T, a, b, p) where T <: Union{zzModMatrix, ZZModMatrix}

Lift `F` modulo `p^n` satisfying `G == F * G * F'`.

- `G` -- a block diagonal matrix of the form `[G0*p^n0, G1*p^n1,...,Gk*p^nk]`
  with integers `nk < .... < n1 < n0` and `Gi` unimodular and symmetric.
- `F` -- invertible `p`-adic matrix
  such that `(G, G, F)` is `a`-adapted
- `a` -- integer the starting precision
- `b`-- integer the target precision

Return `Fk` such that
- `Fk`- the lift of `F` such that
  `Z == F * G * F'` modulo `p^n` with `n = prec`
"""
function hensel_qf(G::T, F::T, a, b, p) where {T <: Union{zzModMatrix, ZZModMatrix}}
  # Input checks
  @req is_unit(det(F)) "F must be invertible"
  @req ncols(G)== ncols(F) && nrows(G) == nrows(F) "G, F must have the same size"
  @req base_ring(G) == base_ring(F) "not the same basering"
  @req is_symmetric(G) "G must be symmetric"
  R = base_ring(G)
  #n = modulus(R)
  #@req(b > n,"Desired precision is higher than base ring precision")
  for k in 1:ncols(G)-1
    n1 = _min_val(G[k,:], p)
    n2 = _min_val(G[k+1,:], p)
    @req n1 >= n2 "block valuations must be descending"
  end
  @req _min_val(F*G*transpose(F)-G, p) >= a "F must satisfy G == F * G * transpose(F) mod p^a"
  if p == 2 & a == 1
    @req _min_val(diagonal(F*G*transpose(F)-G), p) >= a+1 "input is not adapted"
  end
  if ncols(F) == 0
    return F
  end
  # the real worker
  F = _hensel_qf(G, G, F, a, b, p) #works inplace
  return F
end

@doc raw"""
    _block_indices_vals(G:::Union{zzModMatrix, ZZModMatrix}, p)
                                                     -> Vector{Int}, Vector{Int}

Return a list of indices and a list of valuation of the homogeneous blocks.

The matrix `G` is assumed to be a symmetric `p`-adic block diagonal matrix with
modular blocks which have descending valuations.
"""
function _block_indices_vals(G::Union{zzModMatrix, ZZModMatrix}, p)
  indices = Int[]
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
    Helper function for `_hensel_qf`.

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
=#
function _hensel_qf_modular_even(Z::T, G::T, F::T, a, b) where {T <: Union{zzModMatrix, ZZModMatrix}}
  n = ncols(Z)
  @req a != 0 "a must be a non-zero integer"
  if a == 1
    R = base_ring(Z)
    v = _min_val(G, 2)::Int
    G = divexact(G, 2^v)
    Z = divexact(Z, 2^v)
    Y = Z - F*G*transpose(F)
    X = _solve_X(divexact(Y, 2), [divexact(y, 4) for y in diagonal(Y)], diagonal(inv(G)))
    X = 2 * change_base_ring(R, lift(X))::T
    F = F + X*inv(G*transpose(F))
    a = 2
  end
  while a < b
    Y = Z - F*G*transpose(F)
    for i in 1:n
      #Y[i,i+1:end] = 0
      for j in i+1:ncols(Y)
        Y[i, j] = 0
      end
      Y[i,i] = divexact(Y[i,i], 2)
    end
    F = F + Y*inv(G*transpose(F))
    a = 2*a - 1
  end
  # confirm computation
  @hassert :Lattice _min_val(Z-F*G*transpose(F), 2) >= b
  @hassert :Lattice _min_val(diagonal(Z-F*G*transpose(F)),2) >= b + 1
  return F
end


@doc raw"""
    weak_approximation(V::QuadSpace, target) -> QQMatrix

Return $f \in SO(V)$ such that $f \cong f_p \mod p^{v_p}$ for the given $f_p$ and $v_p$
where  `target` has the format `[(f_p, p, v_p), .... ]`.

It is required that $f_p \in SO(V_p)$ for all $p$.
If the precision of $f_p$ is too low, an `ErrorException` is raised.
"""
function weak_approximation(V::QuadSpace, target::Vector{Tuple{QQMatrix,ZZRingElem,Int}})
  gramV = gram_matrix(V)
  @req is_diagonal(gramV) "gram matrix must be diagonal"
  primes = [i[2] for i in target]
  @assert length(unique(primes))==length(primes)
  refsAA = []
  for (fp, p, vp) in target
    d = det(fp) - 1
    @req (d == 0 ? inf : valuation(d, p)) >= vp "fp must be in SO(V)"
    precp = vp
    # decompose fp into a product of reflections
    err, refs = Hecke._decompose_in_reflections(gramV, fp, p)
    refs = [change_base_ring(ZZ, denominator(i) * i) for i in refs]
    # check that the approximation is good enough
    if err < vp
      error("insufficient precision of fp for p=$p. See hensel_qf for a possible way to increase the precision")
    end
    push!(refsAA, (refs, p))
  end

  # Since `fp in SO(V)` the number of reflections is even.
  # To do CRT this number must be the same for each prime p.
  # If it is shorter, then we fill up by an even number of reflections
  # in the first standard basis vector
  e1 = zero_matrix(ZZ, 1, dim(V)); e1[1,1] = 1
  maxlength = maximum([length(i[1]) for i in refsAA])
  for (refs, p) in refsAA
    j = maxlength - length(refs)
    @assert mod(j,2)==0
    for i in 1:j
      pushfirst!(refs, e1)
    end
  end

  # CRT on the reflection vectors
  @label crt
  fudge = 2*dim(V)+10
  crt_prec = [i[3]+fudge for i in target]
  refsQQ = []
  for i in 1:maxlength
    Ve = ZZMatrix[]
    for (refs, p) in refsAA
      vp = refs[i]
      push!(Ve, vp)
    end
    v = _crt(Ve, primes, crt_prec)
    push!(refsQQ, v)
  end
  f = prod([reflection(gramV, v) for v in refsQQ])

  # increase overall precision if we fail
  for (fp, p, vp) in target
    deltap = f - fp
    if deltap != 0 && valuation(deltap, p) < vp
      fudge = fudge + 10
      @goto crt
    end
  end
  return f
end


"""
Chinese remainder for row vecors.
"""
function _crt(V::Vector{ZZMatrix},B::Vector{ZZRingElem}, prec::Vector{Int})
  B = copy(B)
  V = reduce(vcat, V)
  for i in 1:length(B)
    B[i] = B[i]^prec[i]
  end
  sol = zero_matrix(QQ, 1, ncols(V))
  for i in 1:ncols(V)
    sol[1,i] = crt(vec(collect(V[:,i])), B)
  end
  return sol
end
