@doc raw"""
    collect_small_blocks(G::MatElem) -> Vector{MatElem}

Given a block diagonal matrix $G$ consisting of blocks of size $1$ or $2$,
returns the blocks.
"""
function collect_small_blocks(G)
  L = _get_small_block_indices(G)
  blocks = typeof(G)[]
  for i in 1:length(L)
    j, nj = L[i]
    l = j + nj - 1
    push!(blocks, G[j:l, j:l])
  end
  return blocks
end

function _unit_part(x, p)
  if iszero(x)
    return x
  end
  v = _val(x, p)
  y = divexact(x, parent(x)(p^v))
  return y
end

function _ispadic_normal_form(G, p)
  if isodd(p)
    return _ispadic_normal_form_odd(G, p)
  else
    return _ispadic_normal_form_dyadic(G, p)
  end
end

function _ispadic_normal_form_odd(G, p)
  _D = G
  B = collect_small_blocks(_D)
  if G != diagonal_matrix(B)
    return false
  end
  curv = valuation(reduce(gcd, _eltseq(B[1])), p)
  blocks = [[divexact(B[1], QQFieldElem(p)^curv)]]
  for i in 2:length(B)
    v = valuation(reduce(gcd, _eltseq(B[i])), p)
    if v == curv
      push!(blocks[end], divexact(B[i], QQFieldElem(p)^curv))
    else
      curv = v
      push!(blocks, [divexact(B[i], QQFieldElem(p)^curv)])
    end
  end

  for b in blocks
    if !(all(x -> nrows(x) == 1, b))
      return false
    end
  end

  o = identity_matrix(QQ, 1)

  F,  = finite_field(p, 1, cached = false)

  for i in 1:length(blocks)
    if all(==(o), blocks[i])
      continue
    else
      if !(all(==(o), blocks[i][1:end-1]))
        return false
      end
      u = blocks[i][end][1, 1]
      m = FlintZZ(u)
      if is_square(F(m))
        return false
      end
      for i in 1:(m-1)
        if !is_square(F(i))
          return false
        end
      end
    end
  end
  return true
end

function _ispadic_normal_form_dyadic(G, p)
  _D = G
  B = collect_small_blocks(_D)
  if G != diagonal_matrix(B)
    return false
  end
  curv = valuation(reduce(gcd, _eltseq(B[1])), 2)
  blocks = [[divexact(B[1], QQFieldElem(2)^curv)]]
  for i in 2:length(B)
    v = valuation(reduce(gcd, _eltseq(B[i])), 2)
    if v == curv
      push!(blocks[end], divexact(B[i], QQFieldElem(2)^curv))
    else
      curv = v
      push!(blocks, [divexact(B[i], QQFieldElem(2)^curv)])
    end
  end

  U = matrix(FlintQQ,2,2,[0,1,1,0])
  V = matrix(FlintQQ,2,2,[2,1,1,2])
  W1 = matrix(FlintQQ,1,1,[1])
  W3 = matrix(FlintQQ,1,1,[3])
  W5 = matrix(FlintQQ,1,1,[5])
  W7 = matrix(FlintQQ,1,1,[7])

  for B in blocks
    i = 1
    while i <= length(B) && B[i] == U
      i += 1
    end

    if i <= length(B) && B[i] == V
      i += 1
    end

    if i <= length(B) && (B[i] == W1 || B[i] == W3 || B[i] == W5 || B[i] == W7)
      i += 1
    end

    if i <= length(B) && (B[i] == W1 || B[i] == W3 || B[i] == W5 || B[i] == W7)
      i += 1
    end

    if i != length(B) + 1
      return false
    end
  end
  return true
end

@doc raw"""
    padic_normal_form(G::MatElem, p::ZZRingElem; prec::Int = -1, partial::Bool = false)
                                              -> MatElem{QQFieldElem}, MatElem{QQFieldElem}

Return the normal `D` and the transformation `T` to the `p`-adic normal form of
the symmetric matrix `G`, such that `d * D = d * B * G * transpose(B)` holds modulo `p^prec`.
If `prec == -1`,

Let `p` be odd and `u` be the smallest non-square modulo `p`.  The normal form
is a block diagonal matrix with blocks `p^k G_k` such that `G_k` is either the
identity matrix or the identity matrix with the last diagonal entry replaced by
`u`.

If `p = 2`, define the `1` by `1` matrices

    W1 = [1;]
    W3 = [3;]
    W5 = [5;]
    W7 = [7;]

and the `2` by `2` matrices

    U = [0 1;
         1 0]
    V = [2 1;
         1 2]

For `p = 2` the partial normal form is a block diagonal matrix with blocks
`2^k G_k` such that $G_k$ is a block diagonal matrix of the form
`[U`, ... , `U`, `V`, `Wa`, `Wb]`
where we allow `V`, `Wa`, `Wb` to be `0 \times 0` matrices.

Further restrictions to the full normal form apply.
We refer to [MirMor2009]_ IV Definition 4.6. for the details.

If `partial` is set, only the partial normal form is returned.
"""
function padic_normal_form(G, p::IntegerUnion; prec::Int = -1, partial::Bool = false)
  return _padic_normal_form(change_base_ring(FlintQQ, G), ZZRingElem(p), prec = prec, partial = partial)
end

# For a definition in the even case, see Definition 4.6 of Miranda, Morrison,
# "Embeddings of Integral Quadratic Forms", 2009.
function _padic_normal_form(G::QQMatrix, p::ZZRingElem; prec::Int = -1, partial::Bool = false)
  _G = deepcopy(G)
  dd = denominator(G)
  G0 = change_base_ring(FlintZZ, dd * G)
  d = valuation(dd, p)
  n = nrows(G)
  r = rank(G0)

  if r != n
    _, U = hnf_with_transform(G0)
    _ker = U[(r + 1):n, :]
    _nondeg = U[1:r, :]
    ker = change_base_ring(FlintQQ, _ker)
    nondeg = change_base_ring(FlintQQ, _nondeg)
    G = p^d * nondeg * G * transpose(nondeg)
  else
    ker = zero_matrix(FlintQQ, 0, n)
    nondeg = identity_matrix(FlintQQ, n)
    G = p^d * G
  end
  # continue with the non-degenerate part

  if prec == -1
    prec = valuation(det(G)::QQFieldElem, p) + 4
  end

  modu = p^prec
  R = residue_ring(FlintZZ, modu, cached = false)[1]
  Gmod = map(q -> R(invmod(denominator(q), modu) * numerator(q)), G) # this will probably fail
  D = deepcopy(Gmod)

  n = ncols(Gmod)

  Qp = padic_field(p, precision = prec, cached = false)

  if n == 0
    return (zero_matrix(FlintQQ, n, n), zero_matrix(FlintQQ, n, n))::Tuple{QQMatrix, QQMatrix}
  end

  # the transformation matrix is called B

  if p == 2
    D, B = _jordan_2_adic(Gmod)
  else
    D, B = _jordan_odd_adic(Gmod, p)
  end

  @assert B * Gmod * transpose(B) == D

  D, B1 = _normalize(D, p)
  B = B1 * B

  @assert B * Gmod * transpose(B) == D
  # we have reached a normal form for p != 2
  # for p == 2 extra work is necessary
  if p == 2
    D, B1 = _two_adic_normal_forms(D, p, partial = partial)
    B = B1 * B
  end
  @assert B * Gmod * transpose(B) == D

  __nondeg = B * map_entries(x -> R(numerator(x)), nondeg)
  B = vcat(__nondeg, map_entries(x -> R(numerator(x)), ker))
  D = diagonal_matrix([D, zero_matrix(base_ring(D), nrows(ker), nrows(ker))])
  _Gmod = map(q -> R(invmod(denominator(q), modu) * numerator(q)), p^d * _G)
  if p == 2
    @assert B * _Gmod * transpose(B) == diagonal_matrix(collect_small_blocks(D)) == D
  else
    @assert B * _Gmod * transpose(B) == diagonal_matrix(diagonal(D)) == D
  end
  #    if debug:
  @assert _val(det(B), p) == 0     # B is invertible!

  DD = map_entries(x -> FlintQQ(lift(x))//p^d, D)
  BB = map_entries(x -> FlintQQ(lift(x)), B)
  return (DD, BB)::Tuple{QQMatrix, QQMatrix}
end

#def _find_min_p(G, cnt, lower_bound=0):
#    r"""
#    Find smallest valuation below and right from ``cnt`` preferring the diagonal.
#
#    INPUT:
#
#    - ``G`` -- a symmetric `n` by `n` matrix in `\QQ_p`
#    - ``cnt`` -- start search from this index
#    - ``lower_bound`` -- an integer (default: ``0``)
#      a lower bound for the valuations used for optimization
#
#    OUTPUT:
#
#    - ``min`` -- minimal valuation
#    - ``min_i`` -- row index of the minimal valuation
#    - ``min_j`` -- column index of the minimal valuation
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _find_min_p
#        sage: G = matrix(Qp(2, show_prec=False), 3, 3, [4,0,1,0,4,2,1,2,1])
#        sage: G
#        [2^2   0   1]
#        [  0 2^2   2]
#        [  1   2   1]
#        sage: _find_min_p(G, 0)
#        (0, 2, 2)
#        sage: G = matrix(Qp(3, show_prec=False), 3, 3, [4,0,1,0,4,2,1,2,1])
#        sage: G
#        [1 + 3     0     1]
#        [    0 1 + 3     2]
#        [    1     2     1]
#        sage: _find_min_p(G, 0)
#        (0, 0, 0)
#    """

function _find_min_p(G, p, cnt, lower_bound = 0)
  n = ncols(G)
  minval = _val(G[cnt, cnt], p)
  min_i = cnt
  min_j = cnt
  # diagonal has precedence
  for i in cnt:n
    v = _val(G[i, i], p)
    if v == lower_bound
      return lower_bound, i, i
    end
    if v < minval
      min_i = i
      min_j = i
      minval = v
    end
  end
  for i in cnt:n
    for j in (i + 1):n
      v = _val(G[i, j], p)
      if v == lower_bound
        return lower_bound, i, j
      end
      if v < minval
        min_i = i
        min_j = j
        minval = v
      end
    end
  end
  return minval, min_i, min_j
end

#def _get_small_block_indices(G):
#    r"""
#    Return the indices of the blocks.
#
#    For internal use in :meth:`collect_small_blocks`.
#
#    INPUT:
#
#    - ``G`` -- a block_diagonal matrix consisting of `1` by `1` and `2` by `2` blocks
#
#    OUTPUT:
#
#    - a list of integers
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _get_small_block_indices
#        sage: W1 = Matrix([1])
#        sage: U = Matrix(ZZ, 2, [0, 1, 1, 0])
#        sage: G = Matrix.block_diagonal([W1, U, U, W1, W1, U, W1, U])
#        sage: _get_small_block_indices(G)
#        [0, 1, 3, 5, 6, 7, 9, 10]

function _get_small_block_indices(G)
  L = Tuple{Int, Int}[]
  n = ncols(G)
  i = 1
  while i < n
    if !iszero(G[i, i + 1])
      push!(L, (i, 2))
      i += 2
    else
      push!(L, (i, 1))
      i += 1
    end
  end

  if i == n
    push!(L, (i, 1))
  end

  return L
end

#    """

#    L = []
#    n = G.ncols()
#    i = 0
#    while i < n-1:
#        L.append(i)
#        if G[i, i+1]!=0:
#            i += 2
#        else:
#            i += 1
#    if i == n-1:
#        L.append(i)
#    return L[:]
#
#def _get_homogeneous_block_indices(G):
#    r"""
#    Return the indices of the homogeneous blocks.
#
#    We call a matrix homogeneous if it is a multiple of an invertible matrix.
#    Sometimes they are also called modular.
#
#    INPUT:
#
#    - ``G`` - a block diagonal matrix over the p-adics
#      with blocks of size at most `2`.
#
#    OUTPUT:
#
#    - a list of integers
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _get_homogeneous_block_indices
#        sage: W1 = Matrix(Zp(2), [1])
#        sage: V = Matrix(Zp(2), 2, [2, 1, 1, 2])
#        sage: G = Matrix.block_diagonal([W1, V, V, 2*W1, 2*W1, 8*V, 8*W1, 16*V])
#        sage: _get_homogeneous_block_indices(G)
#        ([0, 5, 7, 10], [0, 1, 3, 4])
#        sage: G = Matrix.block_diagonal([W1, V, V, 2*W1, 2*W1, 8*V, 8*W1, 16*W1])
#        sage: _get_homogeneous_block_indices(G)
#        ([0, 5, 7, 10], [0, 1, 3, 4])
#    """
function _get_homogeneous_block_indices(G, p)
  L = Int[]
  vals = Int[]
  n = ncols(G)
  i = 1
  val = -5
  while i < n
    if G[i, i + 1] != 0
      m = _val(G[i, i + 1], p)
    else
      m = _val(G[i, i], p)
    end
    if m > val
      push!(L, i)
      val = m
      push!(vals, val)
    end
    if G[i, i + 1] != 0
      i += 1
    end
    i += 1
  end
  if i == n
    m = _val(G[i, i], p)
    if m > val
      push!(L, i)
      val = m
      push!(vals, val)
    end
  end
  return L, vals
end

#def _homogeneous_normal_form(G, w):
#    r"""
#    Return the homogeneous normal form of the homogeneous ``G``.
#
#    INPUT:
#
#    - ``G`` -- a modular symmetric matrix over the `2`-adic integers
#      in partial normal form
#
#    OUTPUT:
#
#    - ``B`` -- an invertible matrix over the basering of ``G``
#      such that ``B*G*B.T`` is in homogeneous normal form
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _homogeneous_normal_form
#        sage: R = Zp(2, type = 'fixed-mod', print_mode='terse', show_prec=False)
#        sage: U = Matrix(R, 2, [0,1,1,0])
#        sage: V = Matrix(R, 2, [2,1,1,2])
#        sage: W1 = Matrix(R, 1, [1])
#        sage: W3 = Matrix(R, 1, [3])
#        sage: W5 = Matrix(R, 1, [5])
#        sage: W7 = Matrix(R, 1, [7])
#        sage: G = Matrix.block_diagonal([V, W1])
#        sage: B = _homogeneous_normal_form(G, 1)[1]
#        sage: B * G * B.T
#        [2 1 0]
#        [1 2 0]
#        [0 0 1]
#        sage: G = Matrix.block_diagonal([V, W1, W3])
#        sage: B = _homogeneous_normal_form(G, 2)[1]
#        sage: B * G * B.T
#        [2 1 0 0]
#        [1 2 0 0]
#        [0 0 1 0]
#        [0 0 0 3]
#        sage: G = Matrix.block_diagonal([U, V, W1, W5])
#        sage: B = _homogeneous_normal_form(G, 2)[1]
#        sage: B * G * B.T
#        [0 1 0 0 0 0]
#        [1 0 0 0 0 0]
#        [0 0 0 1 0 0]
#        [0 0 1 0 0 0]
#        [0 0 0 0 7 0]
#        [0 0 0 0 0 7]
#        sage: G = Matrix.block_diagonal([U, W7, W3])
#        sage: B = _homogeneous_normal_form(G, 2)[1]
#        sage: B * G * B.T
#        [0 1 0 0]
#        [1 0 0 0]
#        [0 0 3 0]
#        [0 0 0 7]
#        sage: G = Matrix.block_diagonal([V, W5, W5])
#        sage: B = _homogeneous_normal_form(G, 2)[1]
#        sage: B * G * B.T
#        [0 1 0 0]
#        [1 0 0 0]
#        [0 0 3 0]
#        [0 0 0 7]
#        sage: G = Matrix.block_diagonal([V, W3, W3])
#        sage: B = _homogeneous_normal_form(G, 2)[1]
#        sage: B * G * B.T
#        [0 1 0 0]
#        [1 0 0 0]
#        [0 0 1 0]
#        [0 0 0 5]
#        sage: G = Matrix.block_diagonal([V, W1, W3])
#        sage: B = _homogeneous_normal_form(G, 2)[1]
#        sage: B * G * B.T
#        [2 1 0 0]
#        [1 2 0 0]
#        [0 0 1 0]
#        [0 0 0 3]
#        sage: G = Matrix.block_diagonal([W3, W3])
#        sage: B = _homogeneous_normal_form(G, 2)[1]
#        sage: B * G * B.T
#        [7 0]
#        [0 7]
#    """
function _homogeneous_normal_form(G, w, p)
  D = deepcopy(G)
  R = base_ring(G)
  n = ncols(G)
  B = identity_matrix(base_ring(G), n)
  if w == 2
    if n > 2 && !iszero(D[end - 2, end - 2])
      v = 2
    else
      v = 0
    end

    if v == 2
      e1 = _unit_part(D[end - 1, end - 1], p)
      e2 = _unit_part(D[end - 0, end - 0], p)
      e = Set([e1, e2])
      E = [Set(R.([1, 3])), Set(R.([1, 7])), Set(R.([5, 7])), Set(R.([3, 5]))]
      if !(e in E)
        B[end - 3:end, :] = _relations(D[(end - 3):end, (end - 3):end], 5, p) * B[(end - 3):end, :]
        D = B * G * transpose(B)
      end
    end

    e1 = _unit_part(D[end - 1, end - 1], p)
    e2 = _unit_part(D[end - 0, end - 0], p)
    e = Set([e1, e2])
    E = [Set(R.([3, 3])), Set(R.([3, 5])), Set(R.([5, 5])), Set(R.([5, 7]))]
    if e in E
      B[end - 1:end, :] = _relations(D[(end - 1):end, end - 1:end], 1, p) * B[end - 1:end, :]
      D = B * G * transpose(B)
    end
    # assert that e1 < e2
    e1 = _unit_part(D[end - 1, end - 1], p)
    e2 = _unit_part(D[end - 0, end - 0], p)
    if lift(e1) > lift(e2)
      swap_rows!(B, n, n - 1)
      swap_rows!(D, n, n - 1)
      swap_cols!(D, n, n - 1)
    end
  end
  return D, B
end

#        # assert that e1 < e2
#        e1 = D[-2,-2].unit_part()
#        e2 = D[-1,-1].unit_part()
#        if ZZ(e1) > ZZ(e2):
#            B.swap_rows(n-1, n-2)
#            D.swap_rows(n-1, n-2)
#            D.swap_columns(n-1, n-2)
#    return D, B
#
#def _jordan_odd_adic(G):
#    r"""
#    Return the Jordan decomposition of a symmetric matrix over an odd prime.
#
#    INPUT:
#
#    - a symmetric matrix over `\ZZ_p` of type ``'fixed-mod'``
#
#    OUTPUT:
#
#    - ``D`` -- a diagonal matrix
#    - ``B`` -- a unimodular matrix such that ``D = B * G * B.T``
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _jordan_odd_adic
#        sage: R = Zp(3, prec=2, print_mode='terse', show_prec=False)
#        sage: A4 = Matrix(R,4,[2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2])
#        sage: A4
#        [2 8 0 0]
#        [8 2 8 0]
#        [0 8 2 8]
#        [0 0 8 2]
#        sage: D, B = _jordan_odd_adic(A4)
#        sage: D
#        [2 0 0 0]
#        [0 2 0 0]
#        [0 0 1 0]
#        [0 0 0 8]
#        sage: D == B*A4*B.T
#        True
#        sage: B.determinant().valuation() == 0
#        True
#    """
function _jordan_odd_adic(G, p)
  R = base_ring(G)
  D = deepcopy(G)
  n = nrows(G)

  # transformation matrix
  B = identity_matrix(R, n)
  cnt = 1
  minval = 0
  while cnt <= n
    pivot = _find_min_p(D, ZZRingElem(p), cnt, minval)
    piv1 = pivot[2]
    piv2 = pivot[3]
    minval = pivot[1]
    # the smallest valuation is on the diagonal
    if piv1 == piv2
      # move pivot to position [cnt, cnt]
      if piv1 != cnt
        swap_rows!(B, cnt, piv1)
        swap_rows!(D, cnt, piv1)
        swap_cols!(D, cnt, piv1)
      end
      # we are already orthgonal to the part with i < cnt
      # now make the rest orthgonal too
      for i in (cnt + 1):n
        if !iszero(D[i, cnt])
          c = divexact(D[i, cnt], D[cnt, cnt])
          for j in 1:ncols(B)
            B[i, j] = B[i, j] - c * B[cnt, j]
            D[i, j] = D[i, j] - c * D[cnt, j]
          end
          for j in 1:nrows(D)
            D[j, i] = D[j, i] - c * D[j, cnt]
          end
        end
      end
      cnt += 1
    else
      # the smallest valuation is off the diagonal
      row = pivot[2]
      col = pivot[3]
      for j in 1:ncols(B)
        B[row, j] = B[row, j] + B[col, j]
        D[row, j] = D[row, j] + D[col, j]
      end
      for j in 1:nrows(D)
        D[j, row] = D[j, row] + D[j, col]
      end
      # the smallest valuation is now on the diagonal
    end
  end
  return D, B
end
#                    D[:, i] += - c * D[:, cnt]
#            cnt = cnt + 1
#        else:
#            # the smallest valuation is off the diagonal
#            row = pivot[1]
#            col = pivot[2]
#            B[row, :] += B[col, :]
#            D[row, :] += D[col, :]
#            D[:, row] += D[:, col]
#            # the smallest valuation is now on the diagonal
#    return D, B
#
#def _jordan_2_adic(G):
#    r"""
#    Transform a symmetric matrix over the `2`-adic integers into jordan form.
#
#    Note that if the precision is too low, this method fails.
#    The method is only tested for input over `\ZZ_2` of ``'type=fixed-mod'``.
#
#    INPUT:
#
#    - ``G`` -- symmetric `n` by `n` matrix in `\ZZ_p`
#
#    OUTPUT:
#
#    - ``D`` -- the jordan matrix
#    - ``B`` -- transformation matrix, i.e, ``D = B * G * B^T``
#
#    The matrix ``D`` is a block diagonal matrix consisting
#    of `1` by `1` and `2` by `2` blocks.
#    The `2` by `2` blocks are matrices of the form
#    `[[2a,  b], [b, 2c]] * 2^k`
#    with `b` of valuation `0`.
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _jordan_2_adic
#        sage: R = Zp(2, prec=3, print_mode='terse', show_prec=False)
#        sage: A4 = Matrix(R,4,[2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2])
#        sage: A4
#        [2 7 0 0]
#        [7 2 7 0]
#        [0 7 2 7]
#        [0 0 7 2]
#        sage: D, B = _jordan_2_adic(A4)
#        sage: D
#        [ 2  7  0  0]
#        [ 7  2  0  0]
#        [ 0  0 12  7]
#        [ 0  0  7  2]
#        sage: D == B*A4*B.T
#        True
#        sage: B.determinant().valuation() == 0
#        True
#    """

function _jordan_2_adic(G)
  D = deepcopy(G)
  n = ncols(G)
  R = base_ring(G)

  # transformation matrix
  B = identity_matrix(base_ring(G), n)

  # indices of the diagonal entries which are already used
  cnt = 1
  local minval::Union{Int,PosInf}
  while cnt <= n
    pivot = _find_min_p(D, ZZRingElem(2), cnt)
    minval = pivot[1]
    piv1 = pivot[2]
    piv2 = pivot[3]
    # the smallest valuation is on the diagonal
    if piv1 == piv2
      # move pivot to position [cnt, cnt]
      if piv1 != cnt
        swap_rows!(B, cnt, piv1)
        swap_rows!(D, cnt, piv1)
        swap_cols!(D, cnt, piv1)
      end
      # we are already orthogonal to the part with i < cnt
      # now make the rest orthogonal too
      for i in cnt+1:n
        if !iszero(D[i, cnt])
          c = divexact(D[i, cnt], D[cnt, cnt])
          for j in 1:ncols(B)
            B[i, j] = B[i, j] - c * B[cnt, j]
            D[i, j] = D[i, j] - c * D[cnt, j]
          end
          for j in 1:nrows(D)
            D[j, i] = D[j, i] - c * D[j, cnt]
          end
        end
      end
      cnt = cnt + 1
    else
      # the smallest valuation is off the diagonal
      # move this 2 x 2 block to the top left (starting from cnt)
      if piv1 != cnt
        swap_rows!(B, cnt, piv1)
        swap_rows!(D, cnt, piv1)
        swap_cols!(D, cnt, piv1)
      end
      if piv2 != cnt + 1
        swap_rows!(B, cnt + 1, piv2)
        swap_rows!(D, cnt + 1, piv2)
        swap_cols!(D, cnt + 1, piv2)
      end
      # we split off a 2 x 2 block
      # if it is the last 2 x 2 block, there is nothing to do.
      if cnt != n - 1
        content = R(ZZRingElem(2)^minval)
        DD = D[cnt:cnt + 1, cnt:cnt + 1]
        #@show objectid(DD)
        _eqn_mat = Hecke._eltseq(DD)
        eqn_mat = matrix(R, 2, 2, [divexact(e, content) for e in _eqn_mat])
        # calculate the inverse without using division
        eqn_mat_inv = inv(det(eqn_mat)) * matrix(R, 2, 2, [eqn_mat[2, 2], -eqn_mat[1, 2], -eqn_mat[2, 1], eqn_mat[1, 1]])
        @assert isone(eqn_mat * eqn_mat_inv)
        B1 = B[cnt:cnt+1, :]
        #@show objectid(B1)
        DD = D[cnt + 2:nrows(D), cnt:cnt + 1]
        #@show objectid(DD)
        B2 = DD * eqn_mat_inv
        for i in 1:nrows(B2)
          for j in 1:ncols(B2)
            B2[i, j] = divexact(B2[i, j], content)
          end
        end
        Bv = @view B[cnt + 2:nrows(B), :]
        add!(Bv, Bv, -B2 * B1)
        Dv = @view D[cnt:nrows(D),cnt:ncols(D)]
        BB = B[cnt:nrows(B), :]
        mul!(Dv, BB * G, transpose(BB))
      end
      cnt += 2
    end
  end
  return D, B
end

#
#def _min_nonsquare(p):
#    r"""
#    Return the minimal nonsquare modulo the prime `p`.
#
#    INPUT:
#
#    - ``p`` -- a prime number
#
#    OUTPUT:
#
#    - ``a`` -- the minimal nonsquare mod `p`
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _min_nonsquare
#        sage: _min_nonsquare(2)
#        sage: _min_nonsquare(3)
#        2
#        sage: _min_nonsquare(5)
#        2
#        sage: _min_nonsquare(7)
#        3
#    """
#    R = GF(p)
#    for i in R:
#        if not R(i).is_square():
#            return i


function _min_nonsquare(p)
  Rx, x = polynomial_ring(GF(p, cached = false), "x", cached = false)
  for i in 1:p
    if length(factor(x^2 - i)) == 1
      return Int(i)
    end
  end
  error("this can't be reached")
end

function _issquare(d::Nemo.ZZModRingElem, p::ZZRingElem)
  @assert valuation(lift(d), p) == 0
  Rx, x = polynomial_ring(parent(d), "x", cached = false)
  rts = roots(x^2 - d, p, valuation(modulus(parent(d)), p))
  return length(rts) > 0
end

function _issquare(d::zzModRingElem, p)
  f = ZZ(modulus(parent(d)))
  R = residue_ring(FlintZZ, f, cached = false)[1]
  g = R(d)
  return _issquare(g, ZZ(p))
end

function _sqrt(d::Nemo.ZZModRingElem, p::ZZRingElem)
  @assert valuation(lift(d), p) == 0
  Rx, x = polynomial_ring(parent(d), "x", cached = false)
  rts = roots(x^2 - d, p, valuation(modulus(parent(d)), p))
  r = rts[1][1]
  @assert r^2 == d
  return r
end


#
#def _normalize(G, normal_odd=True):
#    r"""
#    Return the transformation to sums of forms of types `U`, `V` and `W`.
#
#    Part of the algorithm :meth:`p_adic_normal_form`.
#
#    INPUT:
#
#    - ``G`` -- a symmetric matrix over `\ZZ_p` in Jordan form --
#      the output of :meth:`p_adic_normal_form` or :meth:`_jordan_2_adic`
#    - ``normal_odd`` -- bool (default: True) if true and `p` is odd,
#      compute a normal form.
#
#    OUTPUT:
#
#    - ``(D, B)`` -- a pair of matrices such that ``D=B*G*B.T``
#      is a sum of forms of types `U`, `V` and `W` for `p=2` or
#      diagonal with diagonal entries equal `1` or `u`
#      where `u` is the smallest non-square modulo the odd prime `p`.
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _normalize
#        sage: R = Zp(3, prec = 5, type = 'fixed-mod', print_mode='series', show_prec=False)
#        sage: G = matrix.diagonal(R, [1,7,3,3*5,3,9,-9,27*13])
#        sage: D, B =_normalize(G)
#        sage: D
#        [    1     0     0     0     0     0     0     0]
#        [    0     1     0     0     0     0     0     0]
#        [    0     0     3     0     0     0     0     0]
#        [    0     0     0     3     0     0     0     0]
#        [    0     0     0     0   2*3     0     0     0]
#        [    0     0     0     0     0   3^2     0     0]
#        [    0     0     0     0     0     0 2*3^2     0]
#        [    0     0     0     0     0     0     0   3^3]
#    """

function _normalize(G, p, normal_odd = true)
  R = base_ring(G)
  D = deepcopy(G)
  n = ncols(G)
  B = identity_matrix(R, n)
  if p != 2
    # squareclasses 1, v
    v = _min_nonsquare(p)
    vv = R(v)
    non_squares = []
    val = 0
    for i in 1:n
      if _val(D[i, i], p) > val
        # a new block starts
        val = _val(D[i, i], p)
        if normal_odd && length(non_squares) != 0
          # move the non-square to the last entry of the previous block
          j = pop!(non_squares)
          swap_rows!(B, j, i - 1)
        end
      end
      d = _unit_part(D[i, i], p)
      if _issquare(d, p)
        D[i, i] = 1
        c = _sqrt(inv(d), p)
        for j in 1:ncols(B)
          B[i, j] = c * B[i, j]
        end
      else
        D[i, i] = vv
        for j in 1:ncols(B)
          B[i, j] = B[i, j] * _sqrt(vv * inv(d), p)
        end
        if normal_odd && length(non_squares) != 0
          # we combine two non-squares to get the 2 x 2 identity matrix
          j = pop!(non_squares)
          trafo = _normalize_odd_twobytwo(D[[i, j], [i, j]], p)
          _BB = trafo * B[[i, j], :]
          B[i:i, :] = _BB[1:1, :]
          B[j:j, :] = _BB[2:2, :]
          #B[[i, j], :] = trafo * B[[i, j], :]
          D[i, i] = 1
          D[j, j] = 1
        else
          push!(non_squares, i)
        end
      end
    end
    if normal_odd && length(non_squares) != 0
      j = pop!(non_squares)
      swap_rows!(B, j, n)
    end
  else
    # squareclasses 1, 3, 5, 7 modulo 8
    for i in 1:n
      d = _unit_part(D[i, i], p)
      if !iszero(d)
        vv = R(mod(lift(d), 8))
        for j in 1:ncols(B)
          B[i, j] = B[i, j] * _sqrt(vv * inv(d), p)
        end
      end
    end
    D = B * G * transpose(B)
    for i in 1:(n - 1)
      if !iszero(D[i, i + 1])
        # there is a 2 x 2 block here
        block = D[i:i+1, i:i+1]
        trafo = _normalize_twobytwo(block, p)
        Bv = @view B[i:i+1, :]
        T = trafo * Bv
        for i in 1:nrows(T)
          for j in 1:ncols(T)
            Bv[i, j] = T[i, j]
          end
        end
        #mul!(Bv, trafo, Bv)
      end
    end
  end
  D = B * G * transpose(B)
  return D, B
end

#def _normalize_2x2(G):
#    r"""
#    Normalize this indecomposable `2` by `2` block.
#
#    INPUT:
#
#    ``G`` - a `2` by `2` matrix over `\ZZ_p`
#    with ``type = 'fixed-mod'`` of the form::
#
#        [2a  b]
#        [ b 2c] * 2^n
#
#    with `b` of valuation 1.
#
#    OUTPUT:
#
#    A unimodular `2` by `2` matrix ``B`` over `\ZZ_p` with
#    ``B * G * B.transpose()``
#    either::
#
#        [0 1]              [2 1]
#        [1 0] * 2^n  or    [1 2] * 2^n
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _normalize_2x2
#        sage: R = Zp(2, prec = 15, type = 'fixed-mod', print_mode='series', show_prec=False)
#        sage: G = Matrix(R, 2, [-17*2,3,3,23*2])
#        sage: B =_normalize_2x2(G)
#        sage: B * G * B.T
#        [2 1]
#        [1 2]
#
#        sage: G = Matrix(R,2,[-17*4,3,3,23*2])
#        sage: B = _normalize_2x2(G)
#        sage: B*G*B.T
#        [0 1]
#        [1 0]
#
#        sage: G = 2^3 * Matrix(R, 2, [-17*2,3,3,23*2])
#        sage: B = _normalize_2x2(G)
#        sage: B * G * B.T
#        [2^4 2^3]
#        [2^3 2^4]
#    """
#    from sage.rings.all import polynomial_ring
#    from sage.modules.free_module_element import vector

function _normalize_twobytwo(G, p)
  # p = ZZRingElem(2)

  R = base_ring(G)
  B = identity_matrix(R, nrows(G))
  P, x = polynomial_ring(R, "x", cached = false)
  odd1 = _val(G[1, 1], p) < _val(G[2, 1], p)
  odd2 = _val(G[2, 2], p) < _val(G[2, 1], p)
  if odd1 || odd2
    error("Not a valid 2 x 2 block.")
  end
  scale = p^(_val(G[1, 2], p))
  D = map_entries(d -> divexact(d, R(scale)), G) # G is symmetric
  # now D is of the form
  # [2a b ]
  # [b  2c]
  # where b has valuation 1.
  G = deepcopy(D)
  # Make sure G[2, 2] has valuation 1.
  if _val(D[2, 2], p) > _val(D[1, 1], p)
    swap_cols!(B, 1, 2)
    swap_cols!(D, 1, 2)
    swap_rows!(D, 1, 2)
  end
  if _val(D[2, 2], p) != 1
    # this works because
    # D[0, 0] has valuation at least 2
    for j in 1:ncols(B)
      B[2, j] = B[2, j] + B[1, j]
    end
    D = B * G * transpose(B)
  end
  @assert _val(D[2, 2], p) == 1

  if mod(lift(det(D)), 8) == 3
#        #  in this case we can transform D to
#        #  2 1
#        #  1 2
#        # Find a point of norm 2
#        # solve: 2 == D[1,1]*x^2 + 2*D[1,0]*x + D[0,0]
    pol = map_coefficients(y -> divexact(y, R(2)), D[2, 2]*x^2 + 2*D[2, 1]*x + D[1, 1] - 2, parent = parent(x))
    sol = roots(pol, p, valuation(modulus(base_ring(G)), p))[1][1]
    @assert pol(sol) == 0
    #pol = divexact(D[2, 2]*x^2 + 2*D[2, 1]*x + D[1, 1] - 2, R(2))
    #sol = _solve_quadratic_dyadic(pol)
    B[1, 2] = sol
    D = B * G * transpose(B)
    # make D[1, 2] = 1
    for j in 1:ncols(B)
      B[2, j] = B[2, j] * inv(D[2, 1])
    end
    D = B * G * transpose(B)

    if D[2, 2] != 2
      v = matrix(P, 1, 2, [x, -2*x + 1])
      pol = map_coefficients(y -> divexact(y, R(2)), (v * change_base_ring(P, D) * transpose(v))[1, 1] - 2, parent = P)
      sol = roots(pol, p, valuation(modulus(R), p))[1][1]
      for j in 1:ncols(B)
        B[2, j] = sol * B[1, j] + (-2 * sol + 1) * B[2, j]
      end
      D = B * G * transpose(B)
    end
    # check the result
    @assert D == matrix(R, 2, 2, [2, 1, 1, 2])
  elseif mod(lift(det(D)), 8) == 7
    # in this case we can transform D to
    #  0 1
    #  1 0
    # Find a point representing 0
    # solve: 0 == D[1,1]*x^2 + 2*D[1,0]*x + D[0,0]
    pol = map_coefficients(y -> divexact(y, R(2)), D[2, 2]*x^2 + 2*D[2,1]*x + D[1,1], parent = P)
    sol = roots(pol, p, valuation(modulus(R), p))[1][1]
    for j in 1:ncols(B)
      B[1, j] = B[1, j] + sol * B[2, j]
    end
    D = B * G * transpose(B)
    # make the second basis vector have 0 square as well.
    for j in 1:ncols(B)
      B[2, j] = B[2, j] - divexact(D[2, 2], 2 * D[1, 2]) * B[1, j]
    end
    D = B * G * transpose(B)
    # rescale to get D[0,1] = 1
    for j in 1:ncols(B)
      B[1, j] = B[1, j] * inv(D[2, 1])
    end
    D = B * G * transpose(B)
    # check the result
    @assert D == matrix(R, 2, 2, [0, 1, 1, 0])
  end
  return B
end

#def _normalize_odd_2x2(G):
#    r"""
#    Normalize this `2` by `2` block.
#
#    INPUT:
#
#    - ``G`` -- a multiple of the `2` by `2` identity_matrix
#      over the `p`-adics for `p` odd.
#
#    OUTPUT:
#
#    - A transformation matrix ``B`` such that
#      ``B * G * B.T`` is the identity matrix
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _normalize_odd_2x2
#        sage: R = Zp(5, type='fixed-mod', print_mode='terse', show_prec=False)
#        sage: G = 2 * Matrix.identity(R, 2)
#        sage: B = _normalize_odd_2x2(G)
#        sage: B*G*B.T
#        [1 0]
#        [0 1]
#    """
function _normalize_odd_twobytwo(G, p)
  @assert G[1, 1] == G[2, 2]
  u = G[1, 1]
  y = zero(base_ring(G))
  while !_issquare(inv(u) - y^2, p)
    y = y + 1
  end
  x = _sqrt(inv(u) - y^2, p)
  B = identity_matrix(base_ring(G), nrows(G))
  B[1, 1] = x
  B[1, 2] = y
  B[2, 1] = y
  B[2, 2] = -x

  D = B * G * transpose(B)
  # check the result
  @assert D == matrix(base_ring(G), 2, 2, [1, 0, 0, 1])
  return B
end

#    B = copy(G.parent().identity_matrix())
#    B[0,0] = x
#    B[0,1] = y
#    B[1,0] = y
#    B[1,1] = -x
#    return B
#
#def _partial_normal_form_of_block(G):
#    r"""
#    Return the partial normal form of the homogeneous block ``G``.
#
#    For internal use in :meth:`_two_adic_normal_forms`.
#
#    INPUT:
#
#    - ``G`` -- a modular symmetric matrix over the `2`-adic integers
#
#    OUTPUT:
#
#    - ``D, B, w`` -- with ``B`` a transformation matrix such that
#      ``B * G * B.T`` is in partial normal form
#      and `w = 0, 1, 2` is the size of the part consisting of forms of type W
#
#    EXAMPLES::
#
#        sage: from sage.quadratic_forms.genera.normal_form import _partial_normal_form_of_block
#        sage: R = Zp(2,prec=4, type = 'fixed-mod',print_mode='terse', show_prec=False)
#        sage: U = Matrix(R, 2, [0,1,1,0])
#        sage: V = Matrix(R, 2, [2,1,1,2])
#        sage: W1 = Matrix(R, 1, [1])
#        sage: W3 = Matrix(R, 1, [3])
#        sage: W5 = Matrix(R, 1, [5])
#        sage: W7 = Matrix(R, 1, [7])
#        sage: G = Matrix.block_diagonal([W1, U, V, W5, V, W3, V, W7])
#        sage: B = _partial_normal_form_of_block(G)[1]
#        sage: B * G * B.T
#        [0 1 0 0 0 0 0 0 0 0 0 0]
#        [1 0 0 0 0 0 0 0 0 0 0 0]
#        [0 0 0 1 0 0 0 0 0 0 0 0]
#        [0 0 1 0 0 0 0 0 0 0 0 0]
#        [0 0 0 0 0 1 0 0 0 0 0 0]
#        [0 0 0 0 1 0 0 0 0 0 0 0]
#        [0 0 0 0 0 0 0 1 0 0 0 0]
#        [0 0 0 0 0 0 1 0 0 0 0 0]
#        [0 0 0 0 0 0 0 0 2 1 0 0]
#        [0 0 0 0 0 0 0 0 1 2 0 0]
#        [0 0 0 0 0 0 0 0 0 0 1 0]
#        [0 0 0 0 0 0 0 0 0 0 0 7]
#        sage: G = Matrix.block_diagonal([W1, U, V, W1, V, W1, V, W7])
#        sage: B = _partial_normal_form_of_block(G)[1]
#        sage: B * G * B.T
#        [0 1 0 0 0 0 0 0 0 0 0 0]
#        [1 0 0 0 0 0 0 0 0 0 0 0]
#        [0 0 0 1 0 0 0 0 0 0 0 0]
#        [0 0 1 0 0 0 0 0 0 0 0 0]
#        [0 0 0 0 0 1 0 0 0 0 0 0]
#        [0 0 0 0 1 0 0 0 0 0 0 0]
#        [0 0 0 0 0 0 0 1 0 0 0 0]
#        [0 0 0 0 0 0 1 0 0 0 0 0]
#        [0 0 0 0 0 0 0 0 0 1 0 0]
#        [0 0 0 0 0 0 0 0 1 0 0 0]
#        [0 0 0 0 0 0 0 0 0 0 3 0]
#        [0 0 0 0 0 0 0 0 0 0 0 7]
#    """
function _partial_normal_form_of_block(G, p)
  D = deepcopy(G)
  n = ncols(G)
  B = identity_matrix(G, n) # transformation matrixj
  blocks = _get_small_block_indices(D)
  # collect the indices of forms of types U, V and W
  U = Int[]
  V = Int[]
  W = Int[]
  for (i,ni) in blocks
    if ni == 1
      push!(W, i)
    else
      if !iszero(D[i, i])
        append!(V, [i, i + 1])
      else
        append!(U, [i, i + 1])
      end
    end
    if length(W) == 3
      # W W W transforms to W U or W V
      #B[W, :] = _relations(D[W, W], 2, p) * B[W, :]
      _BB = _relations(D[W, W], 2, p) * B[W, :]
      for (j, l) in enumerate(W)
        for ll in 1:ncols(B)
          B[l, ll] = _BB[j, ll]
        end
      end
      D = B * G * transpose(B)
      # identify if U or V
      a = W[2]
      b = W[3]
      v = _val(D[a,b],p)
      if _val(D[a,a],p)== v+1 && _val(D[b,b],p) == v+1
      #if mod(lift(_unit_part(det(D[W[2:end], W[2:end]]), p)), 8) == 3 # bug because computing the determinant requires higher precision
        append!(V, W[2:end])
      else
        append!(U, W[2:end])
      end
      W = Int[W[1]]
    end
    if length(V) == 4
      B[V, :] = _relations(D[V, V], 3, p) * B[V, :]
      append!(U, V)
      V = Int[]
      D = B * G * transpose(B)
    end
  end
  # put everything into the right order
  UVW = append!(copy(U), V)
  UVW = append!(UVW, W)
  B = B[UVW, :]
  D = B * G * transpose(B)
  return D, B, length(W)
end
#def _relations(G,n):
#    r"""
#    Return relations of `2`-adic quadratic forms.
#
#    See [MirMor2009]_ IV Prop. 3.2. This function is for internal use only.
#
#    INPUT:
#
#    - ``n`` -- an integer between 1 and 10 -- the number of the relation
#    - ``G`` -- a block diagonal matrix consisting of blocks of types `U, V, W`
#      the left side of the relation. If ``G`` does not match `n` then the
#      results are unpredictable.
#
#    OUTPUT:
#
#    - square matrix ``B`` such that ``B * G * B.T`` is the right side of the
#      relation which consists of blocks of types `U`, `V`, `W` again
function _relations(G, n, p)
  R = base_ring(G)
  if n == 1
    e1 = _unit_part(G[1, 1], p)
    e2 = _unit_part(G[2, 2], p)
    B = matrix(R, 2, 2, [1, 2, 2*e2, -e1])
  elseif n == 2
    e1 = _unit_part(G[1, 1], p)
    e2 = _unit_part(G[2, 2], p)
    e3 = _unit_part(G[3, 3], p)
    B = matrix(R, 3, 3, [1, 1, 1, e2, -e1, 0, e3, 0, -e1])
  elseif n == 3
    if !all(i==G[1,1] for i in diagonal(G))
      error("W is of the wrong type for relation 3")
    end
    B = matrix(R, 4, 4, [1, 1, 1, 0,  1, 1, 0, 1,  1, 0, -1, -1,  0, 1, -1, -1])
  elseif n == 4
    error("Relation 4 is not needed")
  elseif n == 5
    e1 = _unit_part(G[3, 3],  p)
    e2 = _unit_part(G[4, 4],  p)
    if mod(lift(e1), 4) != mod(lift(e2), 4)
      error("W is of the wrong type for relation 5")
    end
    B = matrix(R, 4, 4, [  1,   0,        1,     1,
                           0,   1,        1,     1,
                         -e2, -e2,        0,     3,
                         -e1, -e1, 2*e2 + 3, -2*e1])
  elseif n == 6
    if _val(G[1, 1], p) + 1 != _val(G[2, 2], p)
      error("Wrong scales for relation 6")
    end
    e1 = _unit_part(G[1, 1],  p)
    e2 = _unit_part(G[2, 2],  p)
    B = matrix(R, 2, 2, [1, 1, -2*e2, e1])
  elseif n == 7
    e = _unit_part(G[1, 1], p)
    B = matrix(R, 3, 3, [-3,  e^2,  e^2,  2*e,  1,  0,  2*e,  0,  1])
  elseif n == 8
    e = _unit_part(G[3, 3], p)
    if iszero(G[1, 1])
      B = matrix(R, 3, 3, [e, 0, -1,
                           0, e, -1,
                           2, 2,  1])
    else
      B = matrix(R, 3, 3, [  1,   0,   1,
                             0,   1,   1,
                           2*e, 2*e, - 3])
    end
  elseif n == 9
    e1 = _unit_part(G[1,1], p)
    e2 = _unit_part(G[2,2], p)
    e3 = _unit_part(G[3,3], p)
    B = matrix(R, 3, 3, [1, 0, 1,
                         2*e3, 1,
                        -e1, -2*e2*e3, 2*e1^2*e3 + 4*e1*e3^2, e1*e2])
  elseif n == 10
    e1 = _unit_part(G[1, 1],  p)
    e2 = _unit_part(G[2, 2],  p)
    B = matrix(R, 2, 2, [1, 1, -4*e2, e1])
  else
    error("Relation ($n) must be between 1 and 10")
  end
  D, B1 = _normalize(B * G * transpose(B), p)
  return B1 * B
end

#def _two_adic_normal_forms(G, partial=False):
#    r"""
#    Return the 2-adic normal form of a symmetric matrix.
#
#    INPUT:
#
#    - ``G`` -- block diagonal matrix with blocks of type `U`, `V`, `W`
#    - ``partial`` -- bool (default: ``False``)
#
#    OUTPUT:
#
#    - ``D``, ``B`` -- such that ``D = B * G * B.T``
function _two_adic_normal_forms(G, p; partial = false)
  RR = base_ring(G)
  B = identity_matrix(G, nrows(G))
  h, scales = _get_homogeneous_block_indices(G, p)
  push!(h, ncols(B) + 1)
  # UVlist[k] is a list of indices of the block of scale p^k.
  # It contains the indices of the part of types U or V.
  # So it may be empty.
  UVlist = Vector{Int}[Int[], Int[]] # empty lists are appended to avoid special cases.
  Wlist = Vector{Int}[Int[],Int[]]
  # homogeneous normal form for each part
  for k in 0:(scales[end] - scales[1])
    if k + scales[1] in scales
      i = findfirst(isequal(k + scales[1]), scales)
      @assert i !== nothing
      Gk = G[h[i]:h[i+1]-1, h[i]:h[i+1]-1]
      Dk, Bk, wk = _partial_normal_form_of_block(Gk, p)
      B[h[i]:h[i+1]-1, :] = Bk * B[h[i]:h[i+1]-1, :]
      if !partial
        Dk, B1k = _homogeneous_normal_form(Dk, wk, p)
        B[h[i]:h[i+1]-1,:] = B1k * B[h[i]:h[i+1]-1, :]
      end
      push!(UVlist, collect(h[i]:(h[i + 1] - wk - 1)))
      push!(Wlist, collect((h[i + 1] - wk):h[i + 1] - 1))
    else
      push!(UVlist, Int[])
      push!(Wlist, Int[])
    end
  end
  D = B * G * transpose(B)

  if partial
    return D, B
  end

  # use relations descending in k
  # we never leave partial normal form
  # but the homogeneous normal form may be destroyed
  # it is restored at the end.
  for k in length(UVlist):-1:3
    # setup notation
    W = Wlist[k]
    Wm = Wlist[k - 1]
    Wmm = Wlist[k - 2]
    UV = UVlist[k]
    UVm = UVlist[k - 1]
    UVlistk = UVlist[k]
    # UVlistk is either empty or contains at least two elements
    if length(UVlistk) == 0
      V = Int[]
    else
      V = UVlist[k][end-1:end]
    end
    if length(V) != 0 && D[V[1], V[1]] == 0
      V = Int[]
      # condition b)
    end
    if length(Wm) != 0
      if length(V) == 2
        R = append!([Wm[1]], V)
        B[R, :] = _relations(D[R, R], 7, p) * B[R, :]
        V = Int[]
        D = B * G * transpose(B)
      end
      E = [RR(3), RR(7)]
      for w in W
        if _unit_part(D[w, w], p) in E
          R = [Wm[1], w]
          B[R, :] = _relations(D[R, R], 6, p) * B[R, :]
          D = B * G * transpose(B)
        end
      end
    end
    # condition c)
    # We want type a or W = []
    # modify D[w,w] to go from type b to type a
    x = append!([length(V)], [(mod(lift(_unit_part(w, p)),8)) for w in diagonal(D[W,W])])

    if length(x) == 3 && x[2] > x[3]
      x[2], x[3] = x[3], x[2]
    end
    # the first entry of x is either
    # 0 if there is no type V component or
    # 2 if there is a single type V component
    # a = [[0,1], [2,3], [2,5], [0,7], [0,1,1], [2,1,3], [0,7,7], [0,1,7]]
    b = [[0,5], [2,7], [2,1], [0,3], [0,1,5], [2,1,7], [0,3,7], [0,1,3]]
    if x in b
      w = W[end]
      if x == [0,3,7]
        # relation 10 should be applied to 3 to stay in homogeneous normal form
        w = W[1]
      end
      if length(UVm) > 0
        R = push!(UVm[end-1:end], w)
        B[R,:] = _relations(D[R,R], 8, p) * B[R,:]
      elseif length(Wmm) > 0
        R = push!([Wmm[1]], w)
        B[R,:] = _relations(D[R,R],10,p) * B[R,:]
      elseif length(Wm) == 2
        e0 = _unit_part(D[Wm,Wm][1,1], p)
        e1 = _unit_part(D[Wm,Wm][2,2], p)
        if mod(lift(e1-e0),4) == 0
          R = push!(copy(Wm), w)
          B[R,:] = _relations(D[R,R], 9, p) * B[R,:]
        end
      end
    end
    D = B * G * transpose(B)
    # condition a) - stay in homogeneous normal form
    R = append!(copy(UV), W)
    Dk = D[R,R]
    _, Bk = _homogeneous_normal_form(Dk, length(W), p)
    #B[R,:] = Bk * B[R,:]
    _B = Bk * B[R, :]
    for (l, i) in enumerate(R)
      for j in 1:ncols(B)
        B[i, j] = _B[l, j]
      end
    end
    D = B * G * transpose(B)
    # we need to restore the homogeneous normal form of  k-1
    if length(Wm) > 0
      R = append!(copy(UVm), Wm)
      Dkm = D[R,R]
      _, Bkm = _homogeneous_normal_form(Dkm, length(Wm), p)
      #B[R,:] = Bkm * B[R,:]
      BB = Bkm * B[R,:]
      for (i, r) in enumerate(R)
        for j in 1:ncols(B)
          B[r, j] = BB[i, j]
        end
      end

      D = B * G * transpose(B)
    end
  end
  return D, B
end

################################################################################
#
#  Helper function to treat ZZ/p^k as ZZ_p
#
################################################################################

_val(x::Nemo.ZZModRingElem, y::IntegerUnion) = iszero(x) ? inf : valuation(lift(x), y)

