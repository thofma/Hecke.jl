###############################################################################
#
# Computation of genus symbols
#
###############################################################################

@doc raw"""
    _iseven(A::MatElem) -> (Bool, Int)

Determines if the integral matrix `A` has even diagonal
(i.e. represents only even numbers).  If not, then it returns the
index of an odd diagonal entry.  If it is even, then return the
index -1.
"""
function _iseven(A::MatElem)
  for i in 1:nrows(A)
    if isodd(ZZ(A[i,i]))
      return false, i
    end
  end
  return true, -1
end

@doc raw"""
    _split_odd(A::MatElem) -> (ZZRingElem, ZZMatrix)

Given a non-degenerate Gram matrix `A (\mod 8)`, return a splitting
``[u] + B`` such that u is odd && `B` is not even.
Return `(u,B)`.
"""
function _split_odd(A::MatElem)
  n0 = nrows(A)
  if n0 == 1
    return A[1, 1], zero_matrix(ZZ, 0, ncols(A))
  end
  even, i = _iseven(A)
  R = base_ring(A)
  C = zero_matrix(R, n0 - 1, n0)
  u = A[i,i]
  for j in 1:n0-1
    if j < i
      C[j,j] = 1
      C[j,i] = -A[j,i] * u
    else
      C[j,j+1] = 1
      C[j,i] = -A[j+1,i] * u
    end
  end
  B = C*A*transpose(C)
  even, j = _iseven(B)
  if even
    I = parent(A)(1)
    # TODO: we could manually (re)construct the kernel here...
    if i == 1
      I[2,1] = 1 - A[2,1]*u
      i = 2
    else
      I[1,i] = 1 - A[1,i]*u
      i = 1
    end
    A = I * A * transpose(I)
    u = A[i,i]
    C = zero_matrix(R, n0-1, n0)
    for j in 1:n0-1
      if j < i
        C[j,j] = 1
        C[j,i] = -A[j,i] * u
      else
        C[j,j+1] = 1
        C[j,i] = -A[j+1,i] * u
    end
  end
  B = C * A * transpose(C)
  end
  even, j = _iseven(B)
  @assert !even
  return u, B
end

@doc raw"""
    _trace_diag_mod_8(A::MatElem) -> ZZRingElem

Return the trace of the diagonalised form of `A` of an integral
symmetric matrix which is diagonalizable `\mod 8`.  (Note that since
the Jordan decomposition into blocks of size `<=` 2 is not unique
here, this is not the same as saying that `A` is always diagonal in
any `2`-adic Jordan decomposition!)

INPUT:

- ``A`` -- symmetric matrix with coefficients in `\ZZ` which is odd in
  `\ZZ/2\ZZ` && has determinant not divisible by `8`.
"""
function _trace_diag_mod_8(A::ZZMatrix)
  R = residue_ring(ZZ, 8)[1]
  A8 = change_base_ring(R, A)
  tr = R(0)
  while nrows(A8) > 0
    u, A8 = _split_odd(A8)
    tr += u
  end
  return lift(ZZ, tr)
end

@doc raw"""
    _p_adic_symbol(A::MatElem) -> Vector{Vector{Int64}}

Given a symmetric matrix `A` && prime `p`, return the Conway Sloane
genus symbol at `p` represented as a list of lists.

The genus symbol of a component `p^m f` is of the form ``(m,n, d)``,
where

- `m` = valuation of the component
- `n` = dimension of `f`
- `d = det(f)` in `{1,-1}`
"""
function _p_adic_symbol(A::ZZMatrix, p::ZZRingElem, val::Int)
  if p == 2
    return _two_adic_symbol(A, val)
  end
  if nrows(A)>0
    m0 = minimum(valuation(c, p) for c in A if c!=0)
  else
    m0 = 0
  end
  q = p^m0
  n = nrows(A)
  A = divexact(A, q)
  Fp = Native.GF(p)
  A_p = change_base_ring(Fp, A)
  B_p = kernel(A_p, side = :left)
  rref!(B_p)
  if nrows(B_p) == 0
    e0 = _kronecker_symbol(lift(det(A_p)),p)
    return Vector{Int}[Int[m0, n, e0]]
  else
    C_p = _basis_complement(B_p)
    e0 = _kronecker_symbol(lift(det(C_p * A_p * transpose(C_p))), p)
    n0 = nrows(C_p)
    sym = Vector{Int}[Int[0, n0, e0]]
  end
  r = nrows(B_p)
  B = map_entries(lift, B_p)
  C = map_entries(lift, C_p)
  # Construct the blocks for the Jordan decomposition [F,X;X,A_new]
  F = change_base_ring(QQ, C * A * transpose(C))
  U = F^-1
  d = denominator(U)
  R = residue_ring(ZZ, p^(val + 3))[1]
  u = R(d)^-1

  UZZ = change_base_ring(ZZ, U * d *lift(u))

  X = C * A
  A = B * (A - transpose(X)*UZZ*X) * transpose(B)
  union!(sym, _p_adic_symbol(A, p, val))
  for s in sym
    s[1] += m0
  end
  return sym
end

_p_adic_symbol(A::ZZMatrix, p::Int, val::Int) = _p_adic_symbol(A, ZZ(p), val)

@doc raw"""
    _two_adic_symbol(A::MatElem, val) -> Vector{Vector{Int64}}

Given a symmetric matrix `A` over `Z`, return the Conway Sloane
genus symbol at `2` represented as a list of lists.

The genus symbol of a component `2^m f` is of the form ``(m,n,s,d[,o])``,
where

- `m` = valuation of the component
- `n` = dimension of `f`
- `d` = det(f) in {1,3,5,7}`
- `s` = 0` (or `1`) if even (or odd)
- `o` = oddity of `f` (`= 0` if `s = 0`) in `Z/8Z`

INPUT:

- ``A`` -- symmetric matrix with integer coefficients, non-degenerate
- ``val`` -- non-negative integer; valuation of maximal `2`-elementary divisor

OUTPUT:

a list of lists of integers (representing a Conway-Sloane `2`-adic symbol)
"""
function _two_adic_symbol(A::ZZMatrix, val::Int)
  n = nrows(A)
  # deal with the empty matrix
  if n == 0
    return Vector{Int}[Int[0, 0, 1, 0, 0]]
  end
  m0 = minimum(valuation(c,2) for c in A if c!=0)
  q = ZZ(2)^m0
  A = divexact(A, q)
  A_2 = change_base_ring(Native.GF(2), A)
  B_2 = kernel(A_2, side = :left)
  rref!(B_2)
  R_8 = residue_ring(ZZ, 8)[1]
  # deal with the matrix being non-degenerate mod 2.
  if nrows(B_2) == 0
    d0 = mod(det(A), 8)
    @assert d0 != 0    # SANITY CHECK: The mod 8 determinant shouldn't be zero.
    even, i = _iseven(A)    # Determine whether the matrix is even || odd.
    if even
      return Vector{Int}[Int[m0, n, Int(d0), 0, 0]]
    else
      tr8 = _trace_diag_mod_8(A)  # Here we already know that A_8 is odd
                                  # && diagonalizable mod 8.
      return Vector{Int}[Int[m0, n, Int(d0), 1, Int(tr8)]]
    end
  # deal with the matrix being degenerate mod 2.
  else
    C_2 = _basis_complement(B_2)
    n0 = nrows(C_2)
    C = map_entries(lift, C_2)
    A_new = C * A * transpose(C)
    # compute oddity modulo 8
    d0 = mod(det(A_new), 8)
    @assert d0 != 0
    even, i = _iseven(A_new)
    if even
      sym = Vector{Int}[Int[0, n0, Int(d0), 0, 0]]
    else
      tr8 = _trace_diag_mod_8(A_new)
      sym = Vector{Int}[Int[0, n0, Int(d0), 1, Int(tr8)]]
    end
  end
  r = nrows(B_2)
  B = map_entries(lift, B_2)
  C = map_entries(lift, C_2)
  F = change_base_ring(QQ, C * A * transpose(C))
  U = F^-1
  d = denominator(U)
  R = residue_ring(ZZ,ZZ(2)^(val + 3))[1]
  u = lift(R(d)^-1)
  UZZ = change_base_ring(ZZ,U * d * u)
  X = C * A

  A = B * (A - transpose(X)*UZZ*X) * transpose(B)
  union!(sym, _two_adic_symbol(A, val))
  for s in sym
    s[1] += m0
  end
  return sym
end


@doc raw"""
    _basis_complement(B::MatElem) -> MatElem

Given an echelonized basis matrix `B` (over a field), calculate a
matrix whose rows form a basis complement of the rows of `B`.

julia> B = matrix(ZZ, 1, 2, [1,0])
[1  0]
julia> Hecke.basis_complement(B)
[0  1]
"""
function _basis_complement(B::MatElem)
  F = base_ring(B)
  m = nrows(B)
  n = ncols(B)
  C = zero_matrix(F, n - m, n)
  k = 1
  l = 1
  for i in 1:m
    for j in k:n
      if B[i,j] == 0
        C[l,j] = 1
        l += 1
      else
        k = j+1
        break
      end
    end
  end
  for j in k:n
    C[l + j - k, j] = 1
  end
  return C
end

###############################################################################
#
# Constructors
#
###############################################################################

@doc raw"""
    genus(A::MatElem) -> ZZGenus

Return the genus of a $\mathbb Z$-lattice with gram matrix `A`.
"""
function genus(A::MatElem)
  @req ncols(A) == nrows(A) "Input must be a square matrix"
  @req rank(A) == ncols(A) "Input must have full rank"
  return genus(integer_lattice(; gram = A))
end

@doc raw"""
    genus(L::ZZLat) -> ZZGenus

Return the genus of the lattice `L`.
"""
function genus(L::ZZLat)
  A = gram_matrix(L)
  denom = denominator(A)
  AZZ = change_base_ring(ZZ, denom^2 * A)
  symbols = ZZLocalGenus[]
  if ncols(AZZ)>0
    el = lcm(diagonal(hnf(AZZ)))
    primes = prime_divisors(el)
  else
    primes = [ZZ(2)]
    el = ZZ(1)
  end
  if !(2 in primes)
    prepend!(primes, 2)
  end
  for p in primes
    val = valuation(el, p)
    if p == 2
      val += 3
    end
    push!(symbols, genus(AZZ, p, val; offset = 2*valuation(denom, p)))
  end
  DA = diagonal(rational_span(L))
  neg = count(x < 0 for x in DA)
  pos = count(x > 0 for x in DA)
  @req neg + pos == ncols(A) "Underlying quadratic form is degenerate"
  return ZZGenus((pos, neg), symbols, L)
end

@doc raw"""
    genus(L::ZZLat, p::IntegerUnion) -> ZZLocalGenus

Return the local genus symbol of `L` at the prime `p`.
"""
function genus(L::ZZLat, p::IntegerUnion)
  return genus(gram_matrix(L), p)
end

function genus(A::ZZMatrix, p::ZZRingElem, val::Int; offset::Int = 0)
  symbol = _p_adic_symbol(A, p, val)
  for i in 1:size(symbol)[1]
    symbol[i][1] = symbol[i][1] - offset
  end
  return ZZLocalGenus(p, symbol)
end

@doc raw"""
    genus(A::QQMatrix, p::IntegerUnion) -> ZZLocalGenus

Return the local genus symbol of a Z-lattice with gram matrix `A` at the prime `p`.
"""
function genus(A::QQMatrix, _p::IntegerUnion)
  @req is_symmetric(A) "Input must be symmetric"
  @req rank(A) == nrows(A) "Input must have full rank"
  p = ZZ(_p)
  offset = 0
  d = denominator(A)
  offset = valuation(d, p)
  AZZ = change_base_ring(ZZ, A*(d^2*(1//p)^offset))
  val = valuation(det(AZZ), p)
  if p == 2
    val += 3
  end
  return genus(AZZ, p, val; offset)
end

genus(A::ZZMatrix, _p::IntegerUnion) = genus(change_base_ring(QQ, A), _p)

@doc raw"""
    direct_sum(S1::ZZLocalGenus, S2::ZZLocalGenus) -> ZZLocalGenus

Return the local genus of the direct sum of two representatives.
"""
function direct_sum(S1::ZZLocalGenus, S2::ZZLocalGenus)
  @req prime(S1) == prime(S2) "The local genus symbols must be over the same prime"
  if rank(S1) == 0
    return S2
  elseif rank(S2) == 0
    return S1
  end
  _sym1 = Hecke.symbol(S1)
  _sym2 = Hecke.symbol(S2)
  m1 = min(_sym1[1][1], _sym2[1][1])
  m2 = max(_sym1[end][1], _sym2[end][1])
  sym1 = Dict([[s[1], s] for s in _sym1])
  sym2 = Dict([[s[1], s] for s in _sym2])
  symbol = Vector{Int}[]
  for k in m1:m2
    if prime(S1) == 2
      b = Int[k, 0, 1, 0, 0]
    else
      b = Int[k, 0, 1]
    end
    for sym in [sym1, sym2]
      if haskey(sym, k)
        s = sym[k]
        b[2] += s[2]
        b[3] *= s[3]
        if prime(S1) == 2
          b[3] = mod(b[3], 8)
          if s[4] == 1
            b[4] = s[4]
          end
          b[5] = mod(b[5] + s[5], 8)
        end
      end
    end
    if b[2] != 0
      push!(symbol, b)
    end
  end
  return ZZLocalGenus(prime(S1), symbol)
end

@doc raw"""
    direct_sum(G1::ZZGenus, G2::ZZGenus) -> ZZGenus

Return the genus of the direct sum of `G1` and `G2`.

The direct sum is defined via representatives.
"""
function direct_sum(G1::ZZGenus, G2::ZZGenus)
  p1, n1 = signature_pair(G1)
  p2, n2 = signature_pair(G2)
  sign_pair = (p1 + p2, n1 + n2)
  primes = Hecke.primes(G1)
  union!(primes, Hecke.primes(G2))
  sort!(primes)
  local_symbols = ZZLocalGenus[]
  for p in primes
    sym_p = direct_sum(local_symbol(G1, p), local_symbol(G2, p))
    push!(local_symbols, sym_p)
  end
  return ZZGenus(sign_pair, local_symbols)
end

###############################################################################
#
# Enumeration of genus symbols
#
###############################################################################

@doc raw"""
    integer_genera(sig_pair::Vector{Int}, determinant::RationalUnion;
           min_scale::RationalUnion = min(one(QQ), QQ(abs(determinant))),
           max_scale::RationalUnion = max(one(QQ), QQ(abs(determinant))),
           even=false)                                         -> Vector{ZZGenus}

Return a list of all genera with the given conditions. Genera of non-integral
$\mathbb Z$-lattices are also supported.

# Arguments
- `sig_pair`: a pair of non-negative integers giving the signature
- `determinant`: a rational number; the sign is ignored
- `min_scale`: a rational number; return only genera whose scale is an integer
  multiple of `min_scale` (default: `min(one(QQ), QQ(abs(determinant)))`)
- `max_scale`: a rational number; return only genera such that `max_scale` is an
  integer multiple of the scale (default: `max(one(QQ), QQ(abs(determinant)))`)
- `even`: boolean; if set to true, return only the even genera (default: `false`)
"""
function integer_genera(sig_pair::Tuple{Int,Int}, _determinant::RationalUnion;
                min_scale::RationalUnion = min(one(QQ), QQ(abs(_determinant))),
                max_scale::RationalUnion = max(one(QQ), QQ(abs(_determinant))),
                even=false)
  @req all(s >= 0 for s in sig_pair) "The signature vector must be a pair of non negative integers."
  determinant = QQ(_determinant)
  denominator(determinant) != 1 && even && return ZZGenus[]
  @req min_scale > 0 "Minimal scale must be a positive integer"
  _min_scale = QQ(min_scale)
  @req max_scale > 0 "Maximal scale must be a positive integer"
  _max_scale = QQ(max_scale)
  rank = sig_pair[1] + sig_pair[2]
  out = ZZGenus[]
  local_symbols = Vector{ZZLocalGenus}[]
  pd = prime_divisors(numerator(determinant))
  union!(pd, prime_divisors(denominator(determinant)),
             prime_divisors(numerator(_min_scale)),
             prime_divisors(denominator(_min_scale)),
             prime_divisors(numerator(_max_scale)),
             prime_divisors(denominator(_max_scale)))
  sort!(pd)
  # every global genus has a 2-adic symbol
  if !(2 in pd)
    push!(local_symbols, _local_genera(2, rank, 0, 0, 0, even))
  end
  # collect the p-adic symbols
  for p in pd
    det_val = valuation(determinant, p)
    minscale_p = valuation(_min_scale, p)
    maxscale_p = valuation(_max_scale, p)
    local_symbol_p = _local_genera(p, rank, det_val, minscale_p, maxscale_p, even)
    filter!(s -> (prime(s) == 2) || (length(symbol(s)) > 1) || (symbol(s)[1][1] != 0), local_symbol_p)
    isempty(local_symbol_p) && return out
    push!(local_symbols, local_symbol_p)
  end
  # take the cartesian product of the collection of all possible
  # local genus symbols one for each prime
  # && check which combinations produce a global genus
  # TODO:
  # we are overcounting. Find a more
  # clever way to directly match the symbols for different primes.
  for g in cartesian_product_iterator(local_symbols)
    # create a Genus from a list of local symbols
    G = ZZGenus(sig_pair, copy(g))
    !is_equal(abs(det(G)), abs(determinant)) && continue
    even && !iseven(G) && continue
    # discard the empty genera
    if _isglobal_genus(G)
      push!(out, G)
    end
  end
  # render the output deterministic for testing
  sort!(out; by=x -> Vector{Vector{Int}}[s._symbol for s in x._symbols])
  return out
end

@doc raw"""
    _local_genera(p, rank, det_val, min_scale, max_scale, even) -> Vector{ZZLocalGenus}

Return all `p`-adic genera with the given conditions.

This is a helper function for `genera`.
No input checks are done.

# Arguments
- `p`: a prime number
- `rank`: the rank of this genus
- `det_val`: valuation of the determinant at p
- `min_scale`: an integer the minimal scale of a jordan block
- `max_scale`: an integer the maximal scale of a jordan block
- `even`: `bool`; is ignored if `p` is not `2`
    """
function _local_genera(p::ZZRingElem, rank::Int, det_val::Int, min_scale::Int,
                       max_scale::Int, even::Bool)
  scales_rks = Vector{Vector{Int}}[] # contains possibilities for scales & ranks
  for rkseq in _integer_lists(rank, min_scale, max_scale)
    # rank sequences
    # sum(rkseq) = rank
    # length(rkseq) = max_scale - min_scale + 1
    # now assure that we get the right determinant
    d = 0
    pgensymbol = Vector{Int}[]
    for i in min_scale:max_scale
      d += i * rkseq[i-min_scale+1]
      # blocks of rank 0 are omitted
      if rkseq[i-min_scale+1] != 0
        push!(pgensymbol, Int[i, rkseq[i-min_scale+1], 0])
      end
    end
    if d == det_val
      push!(scales_rks, pgensymbol)
    end
  end
  # add possible determinant square classes
  symbols = Vector{ZZLocalGenus}()
  if p != 2
    for g in scales_rks
      n = length(g)
      for v in cartesian_product_iterator([[-1, 1] for i in 1:n])
        g1 = deepcopy(g)
        for k in 1:n
          g1[k][3] = v[k]
        end
        g1 = ZZLocalGenus(p, g1)
        push!(symbols, g1)
      end
    end
  end
  # for p == 2 we have to include determinant, even/odd, oddity
  # further restrictions apply && are deferred to _blocks
  # (brute force sieving is too slow)
  # TODO: If this is too slow, enumerate only the canonical symbols.
  # as a drawback one has to reconstruct the symbol from the canonical symbol
  # this is more work for the programmer
  if p == 2
    for g in scales_rks
      poss_blocks = Vector{Vector{Vector{Int}}}()
      for b in g
        append!(b, Int[0, 0])
        push!(poss_blocks, _blocks(b, (even && b[1] == 0)))
      end
      for _g1 in cartesian_product_iterator(poss_blocks)
        if _is2adic_genus(_g1)
          g1 = ZZLocalGenus(p, copy(_g1))
          # some of our symbols have the same canonical symbol
          # thus they are equivalent - we want only one in
          # each equivalence class
          if !(g1 in symbols)
            push!(symbols, g1)
          end
        end
      end
    end
  end
  return symbols
end

function _local_genera(p::Int, rank::Int, det_val::Int, min_scale::Int,
                       max_scale::Int, even::Bool)
  return _local_genera(ZZ(p), rank, det_val, min_scale, max_scale, even)
end

@doc raw"""
    _blocks(b::Array{Int}, even_only=false) -> Vector{Vector{Int}}

Return all viable `2`-adic jordan blocks with rank && scale given by ``b``

This is a helper function for `_local_genera`.
It is based on the existence conditions for a modular `2`-adic genus symbol.

INPUT:

- ``b`` -- a list of `5` non-negative integers the first two are kept
and all possibilities for the remaining `3` are enumerated

- ``even_only`` -- bool (default: ``true``) if set, the blocks are even
"""
function _blocks(b::Array{Int}, even_only=false)
  @req length(b) == 5 "must be a 2-adic block"
  blocks = Vector{Vector{Int}}()
  rk = b[2]
  # recall: 2-genus_symbol is [scale, rank, det, even/odd, oddity]
  if rk == 0
    @assert b[3] == 1
    @assert b[4] == 0
    @assert b[5] == 0
    push!(blocks, copy(b))
  elseif rk == 1 && !even_only
    for det in [1, 3, 5, 7]
      b1 = copy(b)
      b1[3] = det
      b1[4] = 1
      b1[5] = det
      push!(blocks, b1)
    end
  elseif rk == 2
    b1 = copy(b)
    # even case
    b1[4] = 0
    b1[5] = 0
    b1[3] = 3
    push!(blocks, b1)
    b1 = copy(b1)
    b1[3] = 7
    push!(blocks, b1)
    # odd case
    if !even_only
      # format (det, oddity)
      for s in Tuple{Int, Int}[(1,2), (5,6), (1,6), (5,2), (7,0), (3,4)]
        b1 = copy(b)
        b1[3] = s[1]
        b1[4] = 1
        b1[5] = s[2]
        push!(blocks, b1)
      end
    end
  elseif rk % 2 == 0
    # the even case has even rank
    b1 = copy(b)
    b1[4] = 0
    b1[5] = 0
    d = mod((-1)^(rk//2), 8)
    for det in Int[d, mod(d * (-3) , 8)]
      b1 = copy(b1)
      b1[3] = det
      push!(blocks, b1)
    end
    # odd case
    if !even_only
      for s in Tuple{Int, Int}[(1,2), (5,6), (1,6), (5,2), (7,0), (3,4)]
        b1 = copy(b)
        b1[3] = mod(s[1]*(-1)^(rk//2 -1) , 8)
        b1[4] = 1
        b1[5] = s[2]
        push!(blocks, b1)
      end
      for s in Tuple{Int, Int}[(1,4), (5,0)]
        b1 = copy(b)
        b1[3] = mod(s[1]*(-1)^(rk//2 - 2) , 8)
        b1[4] = 1
        b1[5] = s[2]
        push!(blocks, b1)
      end
    end
  elseif rk % 2 == 1 && !even_only
    # odd case
    for t in Int[1, 3, 5, 7]
      d = mod((-1)^div(rk, 2) * t , 8)
      for det in Int[d, mod(-3*d, 8)]
        b1 = copy(b)
        b1[3] = det
        b1[4] = 1
        b1[5] = t
        push!(blocks, b1)
      end
    end
  end
  # convert ints to integers
  return blocks
end

###############################################################################
#
# Existence conditions
#
###############################################################################

@doc raw"""
    _isglobal_genus(G::ZZGenus) -> Bool

Return if `S` is the symbol of of a global quadratic form || lattice.
"""
function _isglobal_genus(G::ZZGenus)
  if denominator(scale(G)) != 1
    return _isglobal_genus(rescale(G, denominator(scale(G))))
  end
  D = ZZ(det(G))
  r, s = signature_pair(G)
  R = residue_ring(ZZ, 8)[1]
  oddi = R(r - s)
  for loc in local_symbols(G)
    p = prime(loc)
    sym = symbol(loc)
    v = sum(ss[1] * ss[2] for ss in sym, init = 0)
    _a = divexact(D, p^v)
    denominator(_a) == 1 || return false
    a = numerator(_a)
    b = prod(ss[3] for ss in sym; init = 1)
    if p == 2
      if !_is2adic_genus(sym)
        return false
      end
      if _kronecker_symbol(a*b, p) != 1
        return false
      end
      oddi -= oddity(loc)
    else
      if _kronecker_symbol(a, p) != b
        return false
      end
      oddi += excess(loc)
    end
  end
  if oddi != 0
    return false
  end
  return true
end

@doc raw"""
    _is2adic_genus(symbol::Vector{Vector{Int}})-> Bool

Given a `2`-adic local symbol check whether it is symbol of a `2`-adic form.
"""
function _is2adic_genus(S::ZZLocalGenus)
  @req prime(S) == 2 "The symbol must be 2-adic"
  return _is2adic_genus(symbol(S))
end

@doc raw"""
    _is2adic_genus(symbol::Vector{Vector{Int}}) -> Bool

Given a `2`-adic local symbol (as the underlying list of quintuples)
check whether it is the `2`-adic symbol of a `2`-adic form.

INPUT:

- ``genus_symbol_quintuple_list`` -- a quintuple of integers (with certain
  restrictions).
  """
function _is2adic_genus(symbol::Vector{Vector{Int}})
  for s in symbol
    ## Check that we have a quintuple (i.e. that p=2 && not p >2)
    @req size(s)[1] == 5 ("The genus symbols are not quintuples, so it's not a genus "*
            "symbol for the prime p=2.")
    ## Check the Conway-Sloane conditions
    if s[2] == 1
      if s[4] == 0 || s[3] != s[5]
        return false
      end
    end
    if s[2] == 2 && s[4] == 1
      if mod(s[3], 8) in (1, 7)
        if !(s[5] in (0, 2, 6))
          return false
        end
      end
      if mod(s[3], 8) in (3, 5)
        if !(s[5] in (2, 4, 6))
          return false
        end
      end
    end
    if mod(s[2] - s[5], 2) == 1
      return false
    end
    if s[4] == 0 && s[5] != 0
      return false
    end
  end
  return true
end

###############################################################################
#
# Equality and hash
#
###############################################################################

@doc raw"""
   (==)(G1::ZZLocalGenus, G2::ZZLocalGenus) -> Bool

Return whether the local genus symbols `G1` and `G2` define the same local
genus.
"""
function Base.:(==)(G1::ZZLocalGenus, G2::ZZLocalGenus)
  # This follows p.381 Chapter 15.7 Theorem 10 in Conway Sloane's book
  @req prime(G1) == prime(G2) ("Symbols must be over the same prime "
                                *"to be comparable")

  # make a copy and enforce sparsity
  sym1 = [g for g in symbol(G1) if g[2] != 0]
  sym2 = [g for g in symbol(G2) if g[2] != 0]
  if length(sym1) == 0 || length(sym2) == 0
    return sym1 == sym2
  end
  if prime(G1) != 2
    return sym1 == sym2
  end
  n = length(sym1)
  # scales && ranks
  s1 = Vector{Int}[g[1:2] for g in sym1]
  s2 = Vector{Int}[g[1:2] for g in sym2]
  if s1 != s2
    return false
  end
  # parity
  s1 = Int[g[4] for g in sym1]
  s2 = Int[g[4] for g in sym2]
  if s1 != s2
    return false
  end
  push!(sym1, Int[sym1[end][1]+1, 0, 1, 0, 0])
  push!(sym2, Int[sym1[end][1]+1, 0, 1, 0, 0])
  pushfirst!(sym1, Int[-1, 0, 1, 0, 0])
  pushfirst!(sym1, Int[-2, 0, 1, 0, 0])
  pushfirst!(sym2, Int[-1, 0, 1, 0, 0])
  pushfirst!(sym2, Int[-2, 0, 1, 0, 0])
  n = length(sym1)
  # oddity && sign walking conditions
  det_differs = Int[i for i in 1:n if _kronecker_symbol(sym1[i][3], 2)
                  != _kronecker_symbol(sym2[i][3], 2)]
  odd = Int[sym1[i][1] for i in 1:n if sym1[i][4] == 1]
  for m in sym2[1][1]:sym2[n][1]
    # "for each integer m for which f_{2^m} has type II, we have..."
    if m in odd
      continue
    end
    # sum_{q<2^m}(t_q-t'_q)
    l = sum(sym1[i][5]-sym2[i][5] for i in 1:n if sym1[i][1] < m; init = ZZ(0))
    # 4 (min(a,m)+min(b,m)+...)
    # where 2^a, 2^b are the values of q for which e_q!=e'_q
    r = 4*sum(min(ZZ(m), sym1[i][1]) for i in det_differs; init = ZZ(0))
    if 0 != mod(l-r, 8)
      return false
    end
  end
  return true
end

@doc raw"""
    (==)(G1::ZZGenus, G2::ZZGenus) -> Bool

Return if the genus symbols `G1` and `G2` define the same genus.
"""
function Base.:(==)(G1::ZZGenus, G2::ZZGenus)
  if signature_tuple(G1) != signature_tuple(G2)
    return false
  end
  bad_primes(G1) == bad_primes(G2) || return false
  return local_symbols(G1) == local_symbols(G2)
end

function Base.hash(G::ZZGenus, u::UInt)
  h = reduce(xor,(hash(x) for x in local_symbols(G)), init = hash(signature_pair(G)))
  return xor(h, u)
end

function Base.hash(G::ZZLocalGenus, u::UInt)
  if prime(G)!=2
    # unique symbol
    h = xor(hash(prime(G)),  hash(symbol(G)))
  else
    # symbol is not unique but at least scales and ranks
    h = reduce(xor, (hash(s[1:2]) for s in symbol(G)), init = hash(prime(G)))
  end
  return xor(h, u)
end

###############################################################################
#
# Printing
#
###############################################################################

function Base.show(io::IO, ::MIME"text/plain", G::ZZGenus)
  io = pretty(io)
  println(io, "Genus symbol for integer lattices")
  println(io, "Signatures: ", signature_tuple(G))
  s = local_symbols(G)
  if length(s) == 1
    println(io, "Local symbol:")
    print(io, Indent())
    show(io, s[1])
    print(io, Dedent())
  else
    println(io, "Local symbols:")
    print(io, Indent())
    for i in 1:(length(s)-1)
      show(io, s[i])
      println(io)
    end
    show(io, s[end])
    print(io, Dedent())
  end
end

function Base.show(io::IO, G::ZZGenus)
  if !is_terse(io)
    print(io, "Genus symbol: ")
  end
  print(io, iseven(G) ? "II" : "I")
  p, n = signature_pair(G)
  print(io, "_($p, $n)")
  print(io, _write_global_symbol(G))
end

function Base.show(io::IO, ::MIME"text/plain", G::ZZLocalGenus)
  io = pretty(io)
  println(io, "Local genus symbol for integer lattices")
  println(io, "Prime: ", prime(G))
  s = symbol(G)
  if length(s) in [0,1]
    print(io, "Jordan block ")
  else
    print(io, "Jordan blocks ")
  end
  if prime(G) == 2
    print(io, "(val, rank, det, sign, oddity):")
  else
    print(io, "(val, rank, det):")
  end
  print(io, Indent())
  if length(s) == 0
    nothing
    print(io, Dedent())
  else
    println(io)
    for i in 1:length(s)-1
      println(io, Tuple(s[i]))
    end
    print(io, Tuple(s[end]))
    print(io, Dedent())
  end
end

function Base.show(io::IO, G::ZZLocalGenus)
  if is_terse(io)
    if length(symbol(G)) == 0
      print(io, "Empty local integer genus")
    else
      print(io, prime(G), ": ")
      for sym in symbol(G)
        print(io, Tuple(sym))
      end
    end
  else
    print(io, "Local genus symbol at ", prime(G), ":", _write_local_symbol(G))
  end
end

function _write_local_symbol(G::ZZLocalGenus; ones::Bool = true)
  p = prime(G)
  CS_string = ""
  if p == 2
    for sym in symbol(G)
      s, r, d, e, o = sym
      d = _kronecker_symbol(d, 2)
      !ones && (s == 0) && continue
      if s>=0
        CS_string *= " $(p^s)^$(d * r)"
      else
        CS_string *=" (1/$(p^-s))^$(d * r)"
      end
      if e == 1
        CS_string *= "_$o"
      end
    end
  else
    for sym in symbol(G)
      s, r,d = sym
      !ones && (s == 0) && continue
      if s >= 0
        CS_string *= " $(p^s)^$(d * r)"
      else
        CS_string *= " (1/$(p^-s))^$(d*r)"
      end
    end
  end
  return CS_string
end

function _write_global_symbol(G::ZZGenus)
  s = local_symbols(G)
  sort!(s, lt = (l1, l2) -> prime(l1) < prime(l2))
  str = ""
  for g in s
    str *= _write_local_symbol(g, ones = false)
  end
  return str
end

function Base.show(io::IO, ::MIME"text/latex", G::ZZGenus)
  str = iseven(G) ? "II" : "I"
  p, n = signature_pair(G)
  str *= "_{($p, $n)}"
  s = local_symbols(G)
  sort!(s, lt = (l1, l2) -> prime(l1) < prime(l2))
  print(io, str)
  for g in s
    show(io, "text/latex", g)
  end
end

function Base.show(io::IO, ::MIME"text/latex", g::ZZLocalGenus)
  p = prime(g)
  str = ""
  if p == 2
    for sym in symbol(g)
      sym[1] == 0 && continue
      s, r, d, e, o = sym
      d = _kronecker_symbol(d, 2)
      if s >= 0
        str *= "$(p^s)^{$(d * r)}"
      else
        str *= "(1/$(p^-s))^{$(d * r)}"
      end
      if e == 1
        str *= "_{$o}"
      end
    end
  else
    for sym in symbol(g)
      sym[1] == 0 && continue
      s, r, d = sym
      if s >= 0
        str *= "$(p^s)^{$(d * r)}"
      else
        str *= "(1/$(p^-s))^{$(d * r)}"
      end
    end
  end
  print(io, str)
end

###############################################################################
#
# Invariants and properties
#
###############################################################################

@doc raw"""
    prime(S::ZZLocalGenus) -> ZZRingElem

Return the prime `p` of this `p`-adic genus.
"""
function prime(S::ZZLocalGenus)
  return S._prime
end

@doc raw"""
    symbol(S::ZZLocalGenus) -> Vector{Vector{Int}}

Return the underlying lists of integers for the Jordan blocks of `S`.
"""
function symbol(S::ZZLocalGenus)
  return S._symbol
end

@doc raw"""
    iseven(S::ZZLocalGenus) -> Bool

Return if the underlying `p`-adic lattice is even.

If `p` is odd, every lattice is even.
"""
function iseven(S::ZZLocalGenus)
  if prime(S) != 2 || rank(S) == 0
    return true
  end

  sym = symbol(S)[1]
  return sym[1] > 0 || sym[4] == 0
end

@doc raw"""
    symbol(S::ZZLocalGenus, scale::Int) -> Vector{Int}

Return the underlying lists of integers
for the Jordan block of the given scale
"""
function symbol(S::ZZLocalGenus, scale::Int)
  sym = symbol(S)
  for s in sym
    if s[1] == scale
      return copy(s)
    end
  end
  if prime(S) != 2
    return Int[scale, 0, 1]
  else
    return Int[scale, 0, 1, 0, 0]
  end
end

@doc raw"""
    hasse_invariant(S::ZZLocalGenus) -> Int

Return the Hasse invariant of a representative.
If the representative is diagonal (a_1, ... , a_n)
Then the Hasse invariant is

$\prod_{i < j}(a_i, a_j)_p$.
"""
function hasse_invariant(S::ZZLocalGenus)
  # Conway Sloane Chapter 15 5.3
  n = dim(S)
  d = det(S)
  f0 = ZZRingElem[squarefree_part(numerator(d)*denominator(d))]
  append!(f0, eltype(f0)[one(ZZ) for i in 2:n])
  mf0 = diagonal_matrix(f0)
  gf0 = genus(mf0, prime(S))
  if excess(S) == excess(gf0)
    return 1
  else
    return -1
  end
end

@doc raw"""
    det(S::ZZLocalGenus) -> QQFieldElem

Return an rational representing the determinant of this genus.
"""
function det(S::ZZLocalGenus)
  p = prime(S)
  e = prod(s[3] for s in symbol(S); init = 1)
  if p == 2
    e = e % 8
  elseif e == -1
    e = Int(_min_nonsquare(p))
  end
  return e*prod(QQ(p)^(s[1]*s[2]) for s in symbol(S); init = QQ(1))
end


@doc raw"""
    dim(S::ZZLocalGenus) -> Int

Return the dimension of this genus.
"""
function dim(S::ZZLocalGenus)
  return sum(s[2] for s in symbol(S); init=0)
end

@doc raw"""
    rank(S::ZZLocalGenus) -> Int

Return the rank of (a representative of) `S`.
"""
function rank(S::ZZLocalGenus)
  return dim(S)
end

@doc raw"""
    excess(S::ZZLocalGenus) -> zzModRingElem

Return the p-excess of the quadratic form whose Hessian
matrix is the symmetric matrix A.

When p = 2 the p-excess is
called the oddity.
The p-excess is always even && is divisible by 4 if
p is congruent 1 mod 4.

# Reference
[CS99](@cite) pp 370-371.
"""
function excess(S::ZZLocalGenus)
  R = residue_ring(ZZ, 8)[1]
  p = prime(S)
  if p == 2
    return dim(S) - oddity(S)
  end
  k = 0
  for s in symbol(S)
    if isodd(s[1]) && s[3] == -1
      k += 1
    end
  end
  e = R(4*k)
  for s in symbol(S)
    if s[1] >= 0
      e += R(s[2]*(p^s[1]-1))
    else
      e += R(s[2])*(inv(R(p^(-s[1])))-R(1))
    end
  end
  return e
end

@doc raw"""
    signature(S::ZZLocalGenus) -> zzModRingElem

Return the $p$-signature of this $p$-adic form.
"""
function signature(S::ZZLocalGenus)
  R = residue_ring(ZZ, 8)[1]
  if prime(S) == 2
    return oddity(S)
  else
    return R(dim(S)) - excess(S)
  end
end

@doc raw"""
    oddity(S::ZZLocalGenus) -> zzModRingElem

Return the oddity of this even form.
The oddity is also called the $2$-signature
"""
function oddity(S::ZZLocalGenus)
  R = residue_ring(FlintZZ, 8)[1]
  p = prime(S)
  @req p == 2 "The oddity is only defined for p=2"
  k = 0
  for s in symbol(S)
    if mod(s[1], 2) == 1 && (s[3]  == 3 || s[3] == 5)
      k += 1
    end
  end
  return R(sum(s[5] for s in symbol(S); init = 0) + 4*k)
end

@doc raw"""
    scale(S::ZZLocalGenus) -> QQFieldElem

Return the scale of this local genus.

Let `L` be a lattice with bilinear form `b`.
The scale of `(L,b)` is defined as the ideal
`b(L,L)`.
"""
function scale(S::ZZLocalGenus)
  if rank(S) == 0
    return zero(QQ)
  end
  s = symbol(S)[1][1]
  return QQ(prime(S))^s
end

@doc raw"""
    norm(S::ZZLocalGenus) -> QQFieldElem

Return the norm of this local genus.

Let `L` be a lattice with bilinear form `b`.
The norm of `(L,b)` is defined as the ideal
generated by $\{b(x,x) | x \in L\}$.
"""
function norm(S::ZZLocalGenus)
  if rank(S) == 0
    return zero(QQ)
  end
  p = prime(S)
  if p == 2
    FqPolyRepFieldElem = symbol(S)[1]
    return QQ(prime(S))^(FqPolyRepFieldElem[1] + 1 - FqPolyRepFieldElem[4])
  else
    return scale(S)
  end
end
@doc raw"""
    level(S::ZZLocalGenus) -> QQFieldElem

Return the maximal scale of a jordan component.
"""
function level(S::ZZLocalGenus)
  if rank(S) == 0
    return one(QQ)
  end
  e = symbol(S)[end][1]
  return QQ(prime(S))^e
end

@doc raw"""
    iseven(G::ZZGenus) -> Bool

Return if this genus is even.
"""
function iseven(G::ZZGenus)
  if rank(G) == 0
    return true
  end
  if !is_integral(G)
    return false
  end
  return iseven(local_symbol(G, 2))
end


@doc raw"""
    signature(G::ZZGenus) -> Int

Return the signature of this genus.

The signature is `p - n` where `p` is the number of positive eigenvalues
and `n` the number of negative eigenvalues.
"""
function signature(G::ZZGenus)
  p, n = signature_pair(G)
  return p - n
end

@doc raw"""
    signature_pair(G::ZZGenus) -> Tuple{Int,Int}

Return the signature pair of this genus.

The signature is `[p, n]` where `p` is the number of positive eigenvalues
and `n` the number of negative eigenvalues.
"""
function signature_pair(G::ZZGenus)
  return G._signature_pair
end

@doc raw"""
    signature_tuple(G::ZZGenus) -> Tuple{Int, Int, Int}

Return the signature tuple of this genus.

The signature is `[p, d, n]` where `p` is the number of positive eigenvalues,
`d` is the number of zero eigenvalues and `n` is the number of negative eigenvalues.
"""
function signature_tuple(G::ZZGenus)
  s = signature_pair(G)
  return (s[1], 0, s[2])
end

@doc raw"""
    det(G::ZZGenus) -> QQFieldElem

Return the determinant of this genus.
"""
function det(G::ZZGenus)
  p, n = signature_pair(G)
  d = QQ(-1)^n
  return QQ(-1)^n*prod(QQ(prime(g))^sum(Int[s[1]*s[2] for s in g._symbol],init=0)
                       for g in G._symbols)
end

@doc raw"""
    dim(G::ZZGenus) -> Int

Return the dimension of this genus.
"""
function dim(G::ZZGenus)
  return sum(signature_pair(G))
end

@doc raw"""
    rank(G::ZZGenus) -> Int

Return the rank of a (representative of) the genus `G`.
"""
rank(G::ZZGenus) = dim(G)

@doc raw"""
    local_symbols(G::ZZGenus) -> Vector{ZZLocalGenus}

Return the local symbols.
"""
function local_symbols(G::ZZGenus)
  return G._symbols
end

@doc raw"""
    local_symbol(G::ZZGenus, p) -> ZZLocalGenus

Return the local symbol at `p`.
"""
function local_symbol(G::ZZGenus, p)
  p = ZZ(p)
  for sym in local_symbols(G)
    if p == prime(sym)
      return sym
    end
  end
  @assert p != 2
  sym_p = Vector{Int}[Int[0, rank(G), _kronecker_symbol(numerator(det(G)),p)*_kronecker_symbol(denominator(det(G)), p)]]
  return ZZLocalGenus(p, sym_p)
end

@doc raw"""
    level(G::ZZGenus) -> QQFieldElem

Return the level of this genus.

This is the denominator of the inverse gram matrix
of a representative.
"""
function level(G::ZZGenus)
  return prod(level(sym) for sym in local_symbols(G); init = QQ(1))
end

@doc raw"""
    scale(G::ZZGenus) -> QQFieldElem

Return the scale of this genus.

Let `L` be a lattice with bilinear form `b`.
The scale of `(L,b)` is defined as the ideal
`b(L,L)`.
"""
function scale(G::ZZGenus)
  return prod(scale(s) for s in local_symbols(G); init = QQ(1))
end

@doc raw"""
    norm(G::ZZGenus) -> QQFieldElem

Return the norm of this genus.

Let `L` be a lattice with bilinear form `b`.
The norm of `(L,b)` is defined as the ideal
generated by $\{b(x,x) | x \in L\}$.
"""
function norm(G::ZZGenus)
  return prod(norm(s) for s in local_symbols(G); init = QQ(1))
end

@doc raw"""
    primes(G::ZZGenus) -> Vector{ZZRingElem}

Return the list of primes of the local symbols of `G`.

Note that 2 is always in the output since the 2-adic symbol
of a `ZZGenus` is, by convention, always defined.
"""
primes(G::ZZGenus) = prime.(local_symbols(G))

@doc raw"""
    is_integral(G::ZZGenus) -> Bool

Return whether `G` is a genus of integral $\mathbb Z$-lattices.
"""
is_integral(G::ZZGenus) = is_integral(scale(G))

###############################################################################
#
# Representative & discriminant group
#
###############################################################################

@doc raw"""
    quadratic_space(G::ZZGenus) -> QuadSpace{QQField, QQMatrix}

Return the quadratic space defined by this genus.
"""
function quadratic_space(G::ZZGenus)
  dimension = dim(G)
  if dimension == 0
    qf = zero_matrix(QQ, 0, 0)
    return quadratic_space(QQ, qf)
  end
  determinant = det(G)
  prime_neg_hasse = [prime(s) for s in local_symbols(G) if hasse_invariant(s)==-1]
  neg = signature_pair(G)[2]
  qf =_quadratic_form_with_invariants(dimension, determinant, prime_neg_hasse,
                                      neg)
  return quadratic_space(QQ, qf)
end

@doc raw"""
    rational_representative(G::ZZGenus) -> QuadSpace{QQField, QQMatrix}

Return the quadratic space defined by this genus.
"""
rational_representative(G::ZZGenus) = quadratic_space(G)

@doc raw"""
    discriminant_group(G::ZZGenus) -> TorQuadModule

Return the discriminant form associated to this genus.
"""
function discriminant_group(G::ZZGenus)
  @req is_integral(G) "G must be a genus of integral lattices"
  qL = QQMatrix[]
  for gs in G._symbols
    p = gs._prime
    for block in gs._symbol
      q = _gram_from_jordan_block(p, block, true)
      push!(qL, q)
    end
  end
  q = diagonal_matrix(qL)
  return torsion_quadratic_module(q)
end

@doc raw"""
    representative(G::ZZGenus) -> ZZLat

Compute a representative of this genus && cache it.
"""
function representative(G::ZZGenus)
  if isdefined(G, :_representative)
    return G._representative
  end
  if denominator(scale(G)) != 1
    L = representative(rescale(G, denominator(scale(G))))
    L = rescale(L, 1//denominator(scale(G)))
    G._representative = L
    return L
  end
  V = quadratic_space(G)
  if rank(G) == 0
    return lattice(V)
  end
  L = lattice(V)
  L = maximal_integral_lattice(L)
  for sym in G._symbols
    p = prime(sym)
    L = local_modification(L, representative(sym), p)
  end
  # confirm the computation
  @hassert :Lattice 1 genus(L) == G
  G._representative = L
  return L
end

@doc raw"""
    is_definite(G::ZZGenus) -> Bool

Return if this genus is definite.
"""
is_definite(G::ZZGenus) = any(is_zero, signature_pair(G))

@doc raw"""
    representatives(G::ZZGenus) -> Vector{ZZLat}

Return a list of representatives of the isometry classes in this genus.
"""
function representatives(G::ZZGenus)
  L = representative(G)
  rep = genus_representatives(L)
  @hassert :Lattice 2 !is_definite(G) || mass(G) == sum(QQFieldElem[1//automorphism_group_order(S) for S in rep]; init=QQ(0))
  return rep
end

@doc raw"""
    gram_matrix(S::ZZLocalGenus) -> MatElem

Return a gram matrix of some representative of this local genus.
"""
function gram_matrix(S::ZZLocalGenus)
  G = QQMatrix[]
  p = prime(S)
  for block in S._symbol
    push!(G, _gram_from_jordan_block(p, block))
  end
  G = diagonal_matrix(QQ, G)
  @hassert :Lattice 1  S == genus(G, p)
  return G
end

@doc raw"""
    representative(S::ZZLocalGenus) -> ZZLat

Return an integer lattice which represents this local genus.
"""
function representative(S::ZZLocalGenus)
  return integer_lattice(; gram = gram_matrix(S))
end

@doc raw"""
    _gram_from_jordan_block(p::ZZRingElem, block, discr_form=false) -> MatElem

Return the gram matrix of this jordan block.

This is a helper for `discriminant_form` && `representative`.
No input checks.

INPUT:

- ``p`` -- a prime number

- ``block`` -- a list of 3 integers || 5 integers if `p` is `2`

- ``discr_form`` -- Bool (default: ``false``); if ``true`` invert the scales
  to obtain a gram matrix for the discriminant form instead.
"""
function _gram_from_jordan_block(p::ZZRingElem, block, discr_form=false)
  level = block[1]
  rk = block[2]
  det = block[3]
  if p == 2
    o = block[4]
    t = block[5]
    U = QQ[0 1; 1 0]
    V = QQ[2 1; 1 2]
    W = QQ[1;]
    if o == 0
      if det in [1, 7]
        qL = QQMatrix[U for i in 1:div(rk, 2)]
      else
        qL = QQMatrix[U for i in 1:(div(rk, 2) - 1)]
        push!(qL, V)
      end
    elseif o == 1
      if rk % 2 == 1
        qL = QQMatrix[U for i in 1:max(0, div(rk - 3, 2))]
        if t*det % 8 in [3, 5]
          push!(qL,V)
        elseif rk >= 3
          push!(qL, U)
        end
        push!(qL, t * W)
      else
        if det in [3, 5]
          det = -1
        else
          det = 1
        end
        qL = QQMatrix[U for i in 1:max(0, div(rk - 4, 2))]
        if (det , t) == (1, 0)
          append!(qL, QQMatrix[U, W, 7 * W])
        elseif (det , t) == (1, 2)
          append!(qL, QQMatrix[U, W, W])
        elseif (det , t) == (1, 4)
          append!(qL , QQMatrix[V, W, 3 * W])
        elseif (det , t) == (1, 6)
          append!(qL, QQMatrix[U, 7 * W, 7 * W])
        elseif (det , t) == (-1, 0)
          append!(qL, QQMatrix[V, W, 7 * W])
        elseif (det , t) == (-1, 2)
          append!(qL, QQMatrix[U, 3 * W, 7 * W])
        elseif (det , t) == (-1, 4)
          append!(qL, QQMatrix[U, W, 3 * W])
        elseif (det , t) == (-1, 6)
          append!(qL, QQMatrix[U, W, 5 * W])
        else
          error("invalid symbol $block")
        end
          # if the rank is 2 there is a U too much
        if rk == 2
          qL = qL[end-1:end]
        end
      end
    end
    if size(qL)[1] != 0
      q = diagonal_matrix(qL)
    else
      q = zero_matrix(QQ, 0, 0)
    end
    if discr_form
      map_entries!(x -> x * (1//2)^level, q, q)
    else
      map_entries!(x -> x * QQ(2)^level, q, q)
    end
  elseif p != 2 && discr_form
    q = identity_matrix(QQ, rk)
    d = 2^(rk % 2)
    if _kronecker_symbol(d, p) != det
      u = _min_nonsquare(p)
      q[1,1] = u
    end
    map_entries!(x -> x * (2 // QQ(p)^level), q, q)
  end
  if p != 2 && !discr_form
    q = identity_matrix(QQ, rk)
    if det != 1
      u = _min_nonsquare(p)
      q[1,1] = u
    end
    map_entries!(x -> x * QQ(p)^level, q, q)
  end
  return q
end

###############################################################################
#
#  Spinor Genera
#
###############################################################################

@doc raw"""
    automorphous_numbers(g::ZZLocalGenus) -> Vector{ZZRingElem}

Return generators of the group of automorphous square classes at this prime.

A `p`-adic square class `r` is called automorphous if it is
the spinor norm of a proper `p`-adic integral automorphism of this form.
See [CS99](@cite) Chapter 15, 9.6 for details.
"""
function automorphous_numbers(g::ZZLocalGenus)
  @req is_integral(scale(g)) "g must have integral scale"
  automorphs = ZZRingElem[]
  sym = symbol(g)
  G = change_base_ring(ZZ, gram_matrix(g))
  p = prime(g)
  if p != 2
    up = ZZ(_min_nonsquare(p))
    I = diagonal(G)
    for r in I
      # We need to consider all pairs in I
      # since at most 2 elements are part of a pair
      # we need need at most 2 of each type
      if count(==(r), I) > 2
        deleteat!(I, findfirst(x->x==r, I))
      end
    end
    # products of all pairs
    for r1 in I
      for r2 in I
        push!(automorphs, r1 * r2)
      end
    end
    # supplement (i)
    for block in sym
      if block[2] >= 2
        push!(automorphs, up)
        break
      end
    end
    # normalize the square classes and remove duplicates
    automorphs1 = Set{ZZRingElem}()
    for s in automorphs
      v = valuation(s,p)
      u = divexact(s, p^v)
      if kronecker_symbol(u, p) == -1
        u = up
      else
        u = ZZRingElem(1)
      end
      v = mod(v, 2)
      sq = u * p^v
      push!(automorphs1,sq)
    end
    return sort!(collect(automorphs1))
  end
  # p = 2
  I = ZZRingElem[]
  II = ZZRingElem[]
  for block in collect_small_blocks(G)
    if ncols(block) == 1
      u = block[1,1]
      if count(==(u),I) < 2
        push!(I, block[1,1])
      end
    else # rank2
      q = block[1,2]
      append!(II, ZZRingElem[2*q, 3*2*q, 5*2*q, 7*2*q])
    end
  end
  # We need to consider all pairs in L
  # since at most 2 elements are part of a pair
  # we need need at most 2 of each type
  L = ZZRingElem[]
  append!(L, I)
  append!(L, II)
  for r in L     # remove triplicates
    if count(==(r),L) > 2
      deleteat!(L, findfirst(==(r),L))
    end
  end
  n = length(L)
  for i in 1:n
    for j in 1:i-1
      r = L[i] * L[j]
      push!(automorphs, r)
    end
  end

  # supplement (i)
  n = length(sym)
  for k in 1:n
    s = sym[k]
    if sum([b[2] for b in sym[k:end] if b[1] - s[1] < 4]) >= 3
      append!(automorphs, ZZRingElem[1, 3, 5, 7])
      break
    end
  end

  # supplement (ii)
  sort(I, by=x->valuation(x,2))
  n = length(I)
  for i in 1:n
    for j in 1:i-1
      r = I[i] // I[j]
      v = valuation(r, 2)
      u = divexact(r, QQ(2)^v)
      u = mod(u, 8)
      @assert v >= 0
      if v==0 && u==1
        push!(automorphs, 2)
      end
      if v==0 && u==5
        push!(automorphs, 6)
      end
      if v in [0, 2, 4]  # this overlaps with the first two cases!
        push!(automorphs, 5)
      end
      if v in [1, 3] && u in [1, 5]
        push!(automorphs, 3)
      end
      if v in [1, 3] && u in [3, 7]
        push!(automorphs, 7)
      end
    end
  end
  # normalize the square classes and remove duplicates
  automorphs1 = ZZRingElem[]
  for s in automorphs
    v = valuation(s, 2)
    u = divexact(s, QQ(2)^v)
    u = mod(u, 8)
    v = mod(v, 2)
    sq = u * 2^v
    push!(automorphs1, sq)
  end
  return sort!(unique!(automorphs1))
end

@doc raw"""
    local_multiplicative_group_modulo_squares(primes::Vector{ZZRingElem})

Return the product $\prod_p \QQ_p* / (\QQ_p*)^2$ where `p in primes`.
"""
function local_multiplicative_group_modulo_squares(primes::Vector{ZZRingElem})
  K, _ = Hecke.rationals_as_number_field()
  # f : QQ -> K
  f = MapFromFunc(QQ, K, x -> K(x), x -> coeff(x, 0))
  OK = maximal_order(K)
  primes_as_ideals = [prime_decomposition(OK, p)[1][1] for p in primes]
  stuff = [Hecke.local_multiplicative_group_modulo_squares(P) for P in primes_as_ideals]
  grps = [s[1] for s in stuff]
  maps = Any[s[2] for s in stuff]
  A, proj, inj = direct_product(grps..., task = :both)
  backwardmap = x -> sum([inj[i](maps[i]\(f(x))) for i in 1:length(maps)])
  forwardmap = function(x)
    elems = [f\(maps[i](proj[i](x))) for i in 1:length(grps)]
    elems_integral = ZZRingElem[]
    for i in 1:(length(elems) - 1)
      push!(elems_integral, ZZ(denominator(elems[i])^2 * elems[i]))
    end
    cprimes = copy(primes)
    for i in 1:length(primes)
      if cprimes[i] == 2
        cprimes[i] = primes[i]^4
      else
        cprimes[i] = primes[i]^3
      end
    end
    y = crt(elems_integral, cprimes)
    if sign(y) == sign(elems[end])
      z = QQ(y)
    else
      z = QQ(y + sign(elems[end]) * prod(cprimes))
    end
    @assert backwardmap(z) == x
    return z
  end
  diagonal_morphism = inv(MapFromFunc(A, QQ, forwardmap, backwardmap))
  projd = Any[(primes[i],proj[i]*maps[i]*inv(f)) for i in 1:length(primes)]
  injd = Any[(primes[i],f*inv(maps[i])*inj[i]) for i in 1:length(primes)]
  return A, Dict(projd), Dict(injd), diagonal_morphism
end

@doc raw"""
    _automorphous_numbers(G::ZZGenus)

Return `(Delta, f)` where f: QQ^x -> Delta`

has the property that q is automorphous if and only if $f(q)=0$.
Further Delta is in bijection with the proper spinor genera of `G`.
"""
@attr Any function _automorphous_numbers(G::ZZGenus)
  @assert is_integral(G)
  P = [prime(g) for g in local_symbols(G)]
  A, proj, inj, diagonal_map = local_multiplicative_group_modulo_squares(P)
  gens_automorph = elem_type(A)[]
  for g in local_symbols(G)
    p = prime(g)
    for r in automorphous_numbers(g)
      r = QQ(r)
      S = [i for i in P if i!=p]
      pv,u = ppio(ZZ(r),p)
      pv = QQ(pv); u = QQ(u)
      push!(gens_automorph, inj[p](u) + sum([inj[q](pv) for q in S], init=A()))
    end
  end
  s = signature_tuple(G)
  if s[1]*s[3]>0
    # -1 is -1-adically automorphous
    for p in P
      push!(gens_automorph, inj[p](QQ(-1)))
    end
  end
  gens_local_automorphs = elem_type(A)[]
  for p in P
    if p ==2
      u_p = inj[p](QQ(3))
      push!(gens_local_automorphs, u_p)
      u_p = inj[p](QQ(5))
      push!(gens_local_automorphs, u_p)
    else
      u_p = inj[p](QQ(lift(ZZ, non_square(GF(p)))))
      push!(gens_local_automorphs, u_p)
    end
  end
  B,b = sub(A,gens_local_automorphs)
  C,c = sub(B, [preimage(b,i) for i in gens_automorph])
  Delta, proj = cokernel(c, false)
  binv = MapFromFunc(A, B, x -> preimage(b, x), b)
  f1 = compose(diagonal_map, binv)
  f2 = compose(f1, proj)
  f3 = Dict([(p,compose(compose(inj[p], binv), proj)) for p in keys(inj)])

  function delta(p::ZZRingElem, r::QQFieldElem)
    v = valuation(r, p)
    pr = QQ(p)^v
    ur = divexact(r, pr)
    a = sum([f3[l](pr) for l in P if l!=p], init=Delta())
    a = a + f3[p](ur)
    return a
  end

  return Delta, f2, delta
end

function is_unimodular(g::ZZLocalGenus)
  return scale(g) == level(g) == 1
end

@doc raw"""
    bad_primes(g::ZZGenus) -> Vector{ZZRingElem}

Return `2` and the primes at which `g` is not unimodular.
"""
function bad_primes(g::ZZGenus)
  return [prime(g) for g in local_symbols(g) if !is_unimodular(g) || prime(g)==2]
end

@doc raw"""
    is_automorphous(G::ZZGenus, q::RationalUnion) -> Bool

Return if `q` is the spinor norm of an element of `SO(V)` where `V` is the
rational quadratic space of `G`.

See [CS99](@cite) Chapter 15, Theorem 18.
"""
function is_automorphous(G::ZZGenus, q::RationalUnion)
  @req is_integral(G) "G must be a genus of integral lattices"
  q = QQ(q)
  P = bad_primes(G)
  if any(valuation(q,p)>0 for p in P)
    error("q=$q contains a bad prime")
  end
  _, f2 = _automorphous_numbers(G)
  return iszero(f2(q))
end

@doc raw"""
    improper_spinor_generators(G::ZZGenus) -> Vector{ZZRingElem}

Return a list of primes describing the improper spinor genera of `G`.

Namely if $L$` is lattice in `G` and $L_i$ is a $p_i$-neigbhor of $L$
where the `p_1, \dots, p_n$` are the improper spinor generators, then
$L, L_1,\dots, L_n$ are representatives for the improper spinor genera of `G`.

See [CS99](@cite) Chapter 15, Theorem 15.

# Example
The following genus consists of two proper spinor genera but only
one improper spinor genus.

```jldoctest
julia> L1 = integer_lattice(gram=ZZ[3 0 -1 1; 0 3 -1 -1; -1 -1 6 0; 1 -1 0 6]);

julia> length(Hecke.proper_spinor_generators(genus(L1)))
1

julia> length(Hecke.improper_spinor_generators(genus(L1)))
0
```
"""
function improper_spinor_generators(G::ZZGenus)
  if denominator(scale(G)) != 1
    return improper_spinor_generators(rescale(G, denominator(scale(G))))
  end
  return _improper_spinor_generators(G)[1]
end

"""
    _improper_spinor_generators(G::ZZGenus) -> Vector{ZZRingElem}, map

The first return value are the improper spinor generators.
The second return value is a map f:QQ -> AbelianGroup
(not defined over the bad primes)
which satisfies f(r) == 0 if and only if r is improperly automorphous.
"""
function _improper_spinor_generators(G::ZZGenus)
  @assert is_integral(G)
  P = bad_primes(G)
  Delta, i_prop,Deltap = _automorphous_numbers(G)
  S = ZZRingElem[]

  a = Delta()
  for p in P
    a += Deltap(p, _norm_generator(local_symbol(G,p)))
  end
  _, inc = sub(Delta, [a], false) # no need for the group lattice
  Delta_improp,proj = cokernel(inc, false)
  i_improp = compose(i_prop, proj)
  spin_gens = Set{elem_type(Delta_improp)}()
  push!(spin_gens, Delta_improp())

  C = order(Delta_improp)
  p = 1
  while length(spin_gens) < C
    p = next_prime(p)
    if p in P
      continue
    end
    Delta_x = i_improp(QQ(p))
    if Delta_x in spin_gens
      continue
    end
    push!(S, p)
    push!(spin_gens, Delta_x)
  end
  return S,i_improp
end

function _norm_generator(G::ZZLocalGenus)
  @assert is_integral(scale(G))
  h1 = ZZLocalGenus(prime(G), symbol(G)[1:1])
  g = gram_matrix(h1)
  if g[end, end] == 0
    # hyperbolic plane
    return 2 * g[end - 1, end]
  end
  return g[end, end]
end

@doc raw"""
    proper_spinor_generators(G::ZZGenus) -> Vector{ZZRingElem}

Return a list of primes describing the proper spinor genera of `G`.

Namely if $L$` is lattice in `G` and $L_i$ is a $p_i$-neigbhor of $L$
where the `p_1, \dots, p_n$` are the proper spinor generators, then
$L, L_1,\dots, L_n$ are representatives for the proper spinor genera of `G`.

See [CS99](@cite) Chapter 15, Theorem 15.

# Example
The following genus consists of two proper spinor genera.
```jldoctest
julia> L1 = integer_lattice(gram=ZZ[6 3 0; 3 6 0; 0 0 2]);

julia> length(Hecke.proper_spinor_generators(genus(L1)))
1
```
"""
function proper_spinor_generators(G::ZZGenus)
  if denominator(scale(G)) != 1
    return proper_spinor_generators(rescale(G, denominator(scale(G))))
  end
  P = bad_primes(G)
  Delta, i = _automorphous_numbers(G)
  spin_gens = Set{elem_type(Delta)}()
  Q = ZZRingElem[]
  push!(spin_gens, 0*Delta[1])

  p = 1
  while length(spin_gens) < order(Delta)
    p = next_prime(p)
    if p in P
      continue
    end
    Delta_x = i(QQ(p))
    if Delta_x in spin_gens
      continue
    end
    push!(Q, p)
    push!(spin_gens, Delta_x)
  end
  return Q
end

################################################################################
#
# The mass formula
#
################################################################################

@doc raw"""
    _M_p(species, p) -> QQFieldElem

Return the diagonal factor `M_p` as a function of the species.
"""
function _M_p(species, _p)
  if species == 0
    return QQ(1)
  end
  p = QQ(_p)
  n = abs(species)
  s = Int(div(n + 1,2))
  mp = 2 * prod(1 - p^(-2*k) for k in 1:s-1; init = QQ(1))
  if n % 2 == 0
    mul!(mp, mp, ZZ(1) - sign(species) * p^(-s))
  end
  return inv(mp)
end

@doc raw"""
    _standard_mass_squared(G::ZZGenus) -> QQFieldElem

Return the standard mass of this genus.
It depends only on the dimension and determinant.
"""
function _standard_mass_squared(G::ZZGenus)
  n = dim(G)
  if n % 2 == 0
    s = div(n, 2)
  else
    s = div(n, 2) + 1
  end
  std = QQ(2)^2
  mul!(std, std, prod(_gamma_exact(j // 2) for j in 1:n; init = QQ(1))^2)
  mul!(std, std, prod(_zeta_exact(2*k) for k in 1:s-1; init = QQ(1))^2)
  if n % 2 == 0
    _D = ZZ(-1)^(s) * det(G)
    @assert is_integral(_D)
    D = ZZ(_D)
    mul!(std, std, _quadratic_L_function_squared(ZZ(s), D))
    d = fundamental_discriminant(D)
    # since quadratic_L_function__exact is different
    # from \zeta_D as defined by Conway && Sloane
    # we have to compensate
    # the missing Euler factors
    for sym in G._symbols
      p = sym._prime
      mul!(std, std, (1 - _kronecker_symbol(d, p)*QQ(p)^(-s))^2)
    end
  end
  return std
end

@doc raw"""
    mass(G::ZZGenus) -> QQFieldElem

Return the mass of this genus.

The genus must be definite.
Let `L_1, ... L_n` be a complete list of representatives
of the isometry classes in this genus.
Its mass is defined as $\sum_{i=1}^n \frac{1}{|O(L_i)|}$.
"""
function mass(G::ZZGenus)
  if denominator(scale(G)) != 1
    return mass(rescale(G, denominator(scale(G))))
  end
  pos, neg = signature_pair(G)
  @req pos * neg == 0 "The genus must be definite."
  if pos + neg == 1
    return QQ(1//2)
  end
  mass1 = _standard_mass_squared(G)
  mul!(mass1, mass1, prod(_mass_squared(sym) for sym in local_symbols(G); init = QQ(1)))
  mul!(mass1, mass1, inv(prod(_standard_mass(sym) for sym in local_symbols(G); init = QQ(1))^2))
  return sqrt(mass1)
end


@doc raw"""
    _mass_squared(G::ZZLocalGenus) -> QQFieldElem

Return the local mass `m_p` of this genus as defined by Conway.

See Equation (3) in [CS1988]_
"""
function _mass_squared(G::ZZLocalGenus)
  @req dim(G) > 1 "the dimension must be at least 2"
  p = prime(G)
  sym = symbol(G)
  #diagonal product

  # diagonal factors
  m_p = prod(_M_p(species, p) for species in _species_list(G); init = QQ(1))^2
  # cross terms
  r = length(sym)
  ct = 0
  for j in 1:r
    for i in 1:j
      ct += (sym[j][1] - sym[i][1]) * sym[i][2] * sym[j][2]
    end
  end
  mul!(m_p, m_p, p^ct)
  if p != 2
    return m_p
  end
  # type factors
  nII = ZZ(sum(s[2] for s in sym if s[4] == 0; init = 0))
  nI_I = ZZ(0)   # the total number of pairs of adjacent constituents f_q,
  # f_2q that are both of type I (odd)
  for k in 1:r-1
    if sym[k][4] == sym[k+1][4] == 1 && sym[k][1] + 1 == sym[k+1][1]
      add!(nI_I, ZZ(1))
    end
  end
  mul!(m_p, m_p, QQ(2)^(2*(nI_I - nII)))
  return m_p
end

@doc raw"""
    _standard_mass(G::ZZLocalGenus) -> QQFieldElem

Return the standard p-mass of this local genus.

See Equation (6) of [CS1988]_.
"""
function _standard_mass(G::ZZLocalGenus)
  n = dim(G)
  p = prime(G)
  s = div(n + 1, 2)
  std = 2*prod(1 - QQ(p)^(-2*k) for k in 1:s-1; init = QQ(1))
  if n % 2 == 0
    _D = ZZ(-1)^s * det(G)
    @assert is_integral(_D)
    D = ZZ(_D)
    epsilon = _kronecker_symbol(4 * D, p)
    mul!(std, std, (1 - epsilon*QQ(p)^(-s)))
  end
  return inv(std)
end

@doc raw"""
    _species_list(G::ZZLocalGenus) -> Vector{Int}

Return the species list.
See Table 1 in [CS1988]_.
"""
function _species_list(G::ZZLocalGenus)
  p = prime(G)
  species_list = Int[]
  sym = symbol(G)
  if p != 2
    for k in 1:length(sym)
      n = sym[k][2]
      d = sym[k][3]
      if n % 2 == 0 && d != _kronecker_symbol(-1, p)^(div(n, 2))
        species = -n
      else
        species = n
      end
      push!(species_list, species)
    end
    return species_list
  end
  #  p == 2
  # create a dense list of symbols
  symbols = Vector{Int}[]
  s = 1
  for k in 0:sym[end][1]
    if sym[s][1] == k
      push!(symbols, sym[s])
      s +=1
    else
      push!(symbols, Int[k, 0, 1, 0, 0])
    end
  end
  # avoid a case distinction
  sym = Vector{Int}[Int[-2, 0, 1, 0, 0], Int[-1, 0, 1, 0, 0]]
  append!(sym, symbols)
  push!(sym, Int[sym[end-1][1] + 1, 0, 1, 0, 0])
  push!(sym, Int[sym[end-1][1] + 2, 0, 1, 0, 0])
  for k in 2:length(sym)-1
    free = true
    if sym[k-1][4]==1 || sym[k+1][4]==1
      free = false
    end
    n = sym[k][2]
    o = sym[k][5]
    if _kronecker_symbol(sym[k][3], 2) == -1
      o = mod(o + 4, 8)
    end
    if sym[k][4] == 0 || n % 2 == 1
      t = div(n, 2)
    else
      t = div(n, 2) - 1
    end
    if free && (o == 0 || o == 1 || o == 7)
      species = 2*t
    elseif free && (o == 3 || o == 5 || o == 4)
      species = -2*t
    else
      species = 2*t + 1
    end
    push!(species_list, species)
  end
  return species_list
end

@doc raw"""
    _gamma_exact(n) -> QQFieldElem

Evaluate the exact value of the $\Gamma^2$ function at an integer or
half-integer argument. Ignoring factors of pi
"""
function _gamma_exact(_n)
  n = QQ(_n)
  if denominator(n) == 1
    @req (n > 0) "not in domain"
    return factorial(ZZ(n) - 1)
  end
  @req (denominator(n) == 2) "n must be in (1/2)ZZ"
  a = QQ(1)
  while n != 1//2
    if n < 0
      mul!(a, a, inv(n))
      add!(n, QQ(1))
    elseif n > 0
      sub!(n, n, QQ(1))
      mul!(a, a, n)
    end
  end
  return a
end

@doc raw"""
    _zeta_exact(n) -> QQFieldElem

Return the exact value of the Riemann Zeta function
ignoring factors of pi.

The argument must be a critical value, namely either positive even
or negative odd.

See for example [Iwa1972]_, p13, Special value of $\zeta(2k)$
REFERENCES:

- [Iwa1972]_
- [IR1990]_
- [Was1997]_
"""
function _zeta_exact(n)
  if n < 0
    return bernoulli(1-n)//(n-1)
  elseif n > 1
    if (n % 2 == 0)
      return (-1)^(div(n, 2)+1) * QQ(2)^(n-1) * bernoulli(n) // factorial(ZZ(n))
    else
      error("n must be a critical value (i.e. even > 0 or odd < 0)")
    end
  elseif n == 1
    error("Here is a pole")
  elseif n == 0
    return QQ(-1// 2)
  end
end

@doc raw"""
    _quadratic_L_function_squared(n, d) -> QQFieldElem

Return the square of the exact value of a quadratic twist of the Riemann Zeta
function by $\chi_d(x) = \left(\frac{d}{x}\right)$.
We take the square and ignore multiples of $\pi$ so that the output is rational.

The input `n` must be a critical value.

- [Iwa1972]_, pp 16-17, Special values of $L(1-n, \chi)$ and $L(n, \chi)$
- [IR1990]_
- [Was1997]_
"""
function _quadratic_L_function_squared(n, d)
  if n <= 0
    return _bernoulli_kronecker(1-n, d)^2//(n-1)^2
  end
  @req (n >= 1) "n must be a critical value (i.e. even > 0 or odd < 0)"
  # Compute the kind of critical values (p10)
  if _kronecker_symbol(fundamental_discriminant(d), -1) == 1
    delta = 0
  else
    delta = 1
  end
  # Compute the positive special values (p17)
  @req (mod(n - delta, 2) == 0) "not in domain"
  f = abs(fundamental_discriminant(d))
  if delta == 0
    GS = f
  else
    GS = -f
  end
  a = QQ(-1)^(2 + (n - delta))
  a *= (2//f)^(2*n)
  a *= GS     # Evaluate the Gauss sum here! =0
  a *= 1//(4 * (-1)^delta)
  a *= _bernoulli_kronecker(Int(n),d)^2//factorial(ZZ(n))^2
  return a
end

@doc raw"""
    rational_isometry_class(g::ZZLocalGenus) -> LocalQuadSpaceCls

Return the abstract isometry class of the quadratic space
$g \otimes \mathbb{Q}$.
"""
function rational_isometry_class(g::ZZLocalGenus)
  n = dim(g)
  h = hasse_invariant(g)
  d = det(g)
  p = prime(g)
  return local_quad_space_class(QQ, ZZIdl(p), n, d, h, 0)
end

@doc raw"""
    rational_isometry_class(g::ZZGenus) -> QuadSpaceCls

Return the abstract isometry class of the quadratic space
$g \otimes \mathbb{Q}$.
"""
function rational_isometry_class(g::ZZGenus)
  G = class_quad_type(QQ)(QQ)
  n = dim(g)
  LGS = Dict{ideal_type(order_type(QQ)),localclass_quad_type(QQ)}()
  for s in local_symbols(g)
    h = hasse_invariant(s)
    p = prime(s)
    d = det(s)
    gp = local_quad_space_class(QQ, ZZIdl(p), n, d, h, 0)
    LGS[ideal(ZZ, p)] = gp
  end
  G.LGS = LGS
  G.dim = dim(g)
  G.det = det(g)
  G.dim_rad = 0
  pos, neg = signature_pair(g)
  sig = Dict([(inf,(pos,0, neg))])
  G.signature_tuples = sig
  return G
end

################################################################################
#
# Representations
#
################################################################################

@doc raw"""
    represents(g1::ZZLocalGenus, g2::ZZLocalGenus) -> Bool

Return whether `g1` represents `g2`.

Based on O'Meara Integral Representations of Quadratic Forms Over Local Fields
Note that for `p == 2` there is a typo in O'Meara Theorem 3 (V).
The correct statement is
(V) $2^i(1+4\omega) \to \mathfrak{L}_{i+1}/\mathfrak{l}_{[i]}$.
"""
function represents(G1::ZZLocalGenus, G2::ZZLocalGenus)
  G1, G2 = G2, G1
  s = lcm(denominator(scale(G1)), denominator(scale(G2)))
  G1 = rescale(G1, s)
  G2 = rescale(G2, s)
	@req prime(G2) == prime(G1) "Associated primes must be the same"
  p = prime(G2)
  s1 = symbol(G1)
  s2 = symbol(G2)
  level = max(s1[end][1], s2[end][1])
  # notation
  function delta(pgenus::ZZLocalGenus, i)
    # O'Meara p.857
    if symbol(pgenus, i+1)[4] == 1
      return ZZ(2)^(i+1)
    end
    if symbol(pgenus, i+2)[4] == 1
      return ZZ(2)^(i+2)
    end
    return ZZ(0)
  end

  genus1 = G1
  genus2 = G2
  gen1 = ZZLocalGenus[]  # gen1[i+1] = \mathfrak{l}_i
  gen2 = ZZLocalGenus[]  # gen1[i+1] = \mathfrak{L}_i

  for scale in 0:(level+2)
    i = scale + 1
    g1 = [s for s in s1 if s[1]<=scale]
    g2 = [s for s in s2 if s[1]<=scale]
    push!(gen1, ZZLocalGenus(p, g1))
    push!(gen2, ZZLocalGenus(p, g2))
    if p!=2 && !represents(rational_isometry_class(gen2[i]),
                           rational_isometry_class(gen1[i]))
      return false
    end
  end
  if p != 2
    return true
  end

  # additional conditions for p==2
  for i in 1:(level+1)
    scale = i - 1
    d = QQ(det(gen1[i])*det(gen2[i]))
    # Lower Type following O'Meara Page 858
    # (7)

    if rank(gen1[i]) > rank(gen2[i])
      return false
    end
    # (8)
    if rank(gen1[i]) == rank(gen2[i])
      if mod(valuation(d, 2), 2) != 0
        return false
      end
    end
    # (9)
    if rank(gen1[i]) == rank(gen2[i])
      l = delta(genus1, scale)
      r = gcd(delta(genus2, scale), ZZ(2)^(scale + 2))
      if mod(l, r) != 0
        return false
      end
      l = delta(genus2, scale - 1)
      r = gcd(delta(genus1, scale - 1), ZZ(2)^(scale + 1))
      if mod(l, r) != 0
        return false
      end
    end
    v = valuation(d, 2)
    cond = (rank(gen1[i]) + 1 == rank(gen2[i])
            && rank(gen1[i]) > 0)
    # (10)
    if cond && mod(scale + 1 - v, 2) == 0
      l = delta(genus2, scale - 1)
      r = gcd(delta(genus1, scale - 1),ZZ(2)^(scale + 1))
      if mod(l, r) != 0
        return false
      end
    end

    # (11)
    if cond && (scale - v) % 2 == 0
      l = delta(genus1, scale)
      r = gcd(delta(genus2, scale),ZZ(2)^(scale + 2))
      if mod(l,r) != 0
        return false
      end
    end
  end

  gen2_round = ZZLocalGenus[]  # gen2_round[i-1] = \mathfrak{L}_{(i)}
  for scale in 0:(level + 2)
    g2 = [s for s in s2 if s[1]<scale || (s[1]==scale && s[4]==1)]
    push!(gen2_round, ZZLocalGenus(p, g2))
  end

  gen1_square = ZZLocalGenus[] # gen2_square[i-1] = \mathfrak{l}_{[i]}
  for scale in 0:level
    g1 = [s for s in s1 if s[1]<=scale || (s[1]==scale+1 && s[4]==0)]
    push!(gen1_square, ZZLocalGenus(p, g1))
  end

  FH = isometry_class(quadratic_space(QQ, QQ[0 1; 1 0]), p)
  for i in 1:(level+1)
    scale = i - 1
    # I
    d = delta(genus2, scale)
    L = rational_isometry_class(gen2_round[i+2])
    L -= rational_isometry_class(gen1_square[i])
    if !any(represents(L, u*d) for u in [1,3,5,7])
      return false
    end
    # II
    d = delta(genus1, scale)
    L = rational_isometry_class(gen2_round[i+2])
    L -= rational_isometry_class(gen1_square[i])
    if !any(represents(L, u*d) for u in [1,3,5,7])
      return false
    end

    # III
    S1 = rational_isometry_class(gen2_round[i+2])
    S2 = rational_isometry_class(gen1_square[i])
    if  S1 - S2 == FH
      d1 = delta(genus1, scale)
      d2 = delta(genus2, scale)
      if d1!=0 && d2!=0 && valuation(d1,2) > valuation(d2,2)
        return false
      end
    end
    # IV
    ti1 = isometry_class(quadratic_space(QQ, ZZ[ZZ(2)^scale;]), p)
    ti2 = isometry_class(quadratic_space(QQ, ZZ[5*ZZ(2)^scale;]), p)
    S = (ti1 + rational_isometry_class(gen2_round[i+1]))
    S -= rational_isometry_class(gen1[i])
    if !(represents(S, ti1) || represents(S,ti2))
      return false
    end
    # V
    # there is a typo in O'Meara
    # the reason is that
    # (ti1 + gen2_round[i+1])-gen1_square[i]
    # can have negative dimension
    # even if l = L .... && surely
    # L is represented by itself
    S = (ti1 + rational_isometry_class(gen2[i+1]))
    S= S - rational_isometry_class(gen1_square[i])
    if !(represents(S,ti1) || represents(S,ti2))
      return false
    end
  end
  return true
end

@doc raw"""
    represents(G1::ZZGenus, G2::ZZGenus) -> Bool

Return if `G1` represents `G2`. That is if some element in the genus of `G1`
represents some element in the genus of `G2`.
"""
function represents(G1::ZZGenus, G2::ZZGenus)
  p1, m1 = signature_pair(G1)
  p2, m2 = signature_pair(G2)
  if  p1<p2 || m1 < m2
    return false
  end

  primes = union!(Hecke.primes(G1), Hecke.primes(G2))

  for p in primes
    sp = local_symbol(G1, p)
    op = local_symbol(G2, p)
    if !represents(sp, op)
      return false
    end
  end
  return true
end

################################################################################
#
#     Embeddings
#
################################################################################

@doc raw"""
    embed(S::ZZLat, G::Genus, primitive::Bool=true) -> Bool, embedding

Return a (primitive) embedding of the integral lattice `S` into some lattice in the genus of `G`.

```jldoctest
julia> G = integer_genera((8,0), 1, even=true)[1];

julia> L, S, i = embed(root_lattice(:A,5), G);

```
"""
function embed(S::ZZLat, G::ZZGenus, primitive::Bool=true)
  @req scale(S) >= 1 && scale(G) >= 1 "L and G must be integral"
  @req signature_tuple(S)[2]==0 "S must be nondegenerate"
  if abs(det(G)) == 1
    pos, neg = signature_pair(G)
    return embed_in_unimodular(S, pos, neg; primitive, even = iseven(G))
  end
  raise(NotImplementedError("for now G needs to be even unimodular, but you can use Nikulin's theory to get a primitive embedding by 'hand' in the non-unimodular cases"))
end

@doc raw"""
    embed_in_unimodular(S::ZZLat, pos::Int, neg::Int, primitive=true, even=true) -> Bool, L, S', iS, iR

Return a (primitive) embedding of the integral lattice `S` into some
(even) unimodular lattice of signature `(pos, neg)`.

For now this works only for even lattices.

```jldoctest
julia> NS = direct_sum(integer_lattice(:U), rescale(root_lattice(:A, 16), -1))[1];

julia> LK3, iNS, i = embed_in_unimodular(NS, 3, 19);

julia> genus(LK3)
Genus symbol for integer lattices
Signatures: (3, 0, 19)
Local symbol:
  Local genus symbol at 2: 1^22

julia> iNS
Integer lattice of rank 18 and degree 22
with gram matrix
[0   1    0    0    0    0    0    0    0    0    0    0    0    0    0    0    0    0]
[1   0    0    0    0    0    0    0    0    0    0    0    0    0    0    0    0    0]
[0   0   -2    1    0    0    0    0    0    0    0    0    0    0    0    0    0    0]
[0   0    1   -2    1    0    0    0    0    0    0    0    0    0    0    0    0    0]
[0   0    0    1   -2    1    0    0    0    0    0    0    0    0    0    0    0    0]
[0   0    0    0    1   -2    1    0    0    0    0    0    0    0    0    0    0    0]
[0   0    0    0    0    1   -2    1    0    0    0    0    0    0    0    0    0    0]
[0   0    0    0    0    0    1   -2    1    0    0    0    0    0    0    0    0    0]
[0   0    0    0    0    0    0    1   -2    1    0    0    0    0    0    0    0    0]
[0   0    0    0    0    0    0    0    1   -2    1    0    0    0    0    0    0    0]
[0   0    0    0    0    0    0    0    0    1   -2    1    0    0    0    0    0    0]
[0   0    0    0    0    0    0    0    0    0    1   -2    1    0    0    0    0    0]
[0   0    0    0    0    0    0    0    0    0    0    1   -2    1    0    0    0    0]
[0   0    0    0    0    0    0    0    0    0    0    0    1   -2    1    0    0    0]
[0   0    0    0    0    0    0    0    0    0    0    0    0    1   -2    1    0    0]
[0   0    0    0    0    0    0    0    0    0    0    0    0    0    1   -2    1    0]
[0   0    0    0    0    0    0    0    0    0    0    0    0    0    0    1   -2    1]
[0   0    0    0    0    0    0    0    0    0    0    0    0    0    0    0    1   -2]

julia> is_primitive(LK3, iNS)
true
```
"""
function embed_in_unimodular(S::ZZLat, pos::IntegerUnion, neg::IntegerUnion; primitive=true, even=true)
  @vprintln :Lattice 1 "computing embedding in L_$(n)"
  pS, kS, nS = signature_tuple(S)
  @req kS == 0 "S must be non-degenerate"
  even || raise(NotImplementedError("for now we need the unimodular lattice to be even."))
  pR = pos - pS
  nR = neg - nS
  DS = discriminant_group(S)
  DR = rescale(DS, -1)  # discriminant group of R = S^\perp in L as predicted by Nikulin
  GR = genus(DR, (pR, nR)) # genus of R
  R = representative(GR)
  R = lll(R)  # make R a bit nicer
  R = integer_lattice(; gram=gram_matrix(R)) # clear the history of R

  SR, inj = direct_sum(S, R)
  iS, iR = inj
  V = ambient_space(SR)
  S = lattice(V, basis_matrix(S) * iS.matrix)
  R = lattice(V, basis_matrix(R) * iR.matrix)
  fl, glue = is_anti_isometric_with_anti_isometry(discriminant_group(S), discriminant_group(R))
  @assert fl
  L = overlattice(glue)
  @assert V === ambient_space(SR)
  @hassert :Lattice 1 abs(det(L)) ==1
  @hassert :Lattice 1 denominator(gram_matrix(L))==1
  @hassert :Lattice 1 !even || iseven(L)
  return L, S, iS
end

###############################################################################
#
# Primary/elementary genera
#
###############################################################################

@doc raw"""
    is_primary_with_prime(G::ZZGenus) -> Bool, ZZRingElem

Given a genus of $\mathbb Z$-lattices `G`, return whether it is primary,
that is whether the bilinear form is integral and the associated
discriminant form (see [`discriminant_group`](@ref)) is a `p`-group for some
prime number `p`. In case it is, `p` is also returned as second output.

Note that for unimodular genera, this function returns `(true, 1)`. If the
genus is not primary, the second return value is `-1` by default.
"""
function is_primary_with_prime(G::ZZGenus)
  @req is_integral(G) "G must be a genus of integral lattices"
  length(primes(G)) >= 3 && return false, ZZ(-1)

  sym = local_symbols(G)
  if length(sym) == 1 # symbol only at 2
    if sym[1]._symbol[end][1] != 0
      return true, ZZ(2)
    else
      return true, ZZ(1)
    end
  end

  if sym[1]._symbol[end][1] != 0
      return false, ZZ(-1)
  end

  return true, primes(G)[end]
end

@doc raw"""
    is_primary(G::ZZGenus, p::Union{Integer, ZZRingElem}) -> Bool

Given a genus of integral $\mathbb Z$-lattices `G` and a prime number `p`,
return whether `G` is `p`-primary, that is whether the associated discriminant
form (see [`discriminant_group`](@ref)) is a `p`-group.
"""
function is_primary(G::ZZGenus, p::Union{Integer, ZZRingElem})
  bool, q = is_primary_with_prime(G)
  return bool && q == p
end

@doc raw"""
    is_unimodular(G::ZZGenus) -> Bool

Given a genus of integral $\mathbb Z$-lattices `G`, return whether `G` is
unimodular, that is whether the associated discriminant form
(see [`discriminant_group`](@ref)) is trivial.
"""
is_unimodular(G::ZZGenus) = is_primary(G, 1)

@doc raw"""
    is_elementary_with_prime(G::ZZGenus) -> Bool, ZZRingElem

Given a genus of $\mathbb Z$-lattices `G`, return whether it is elementary,
that is whether the bilinear form is inegtral and the associated discriminant
form (see [`discriminant_group`](@ref)) is an elementary `p`-group for some
prime number `p`. In case it is, `p` is also returned as second output.

Note that for unimodular genera, this function returns `(true, 1)`. If the
genus is not elementary, the second return value is `-1` by default.
"""
function is_elementary_with_prime(G::ZZGenus)
  bool, p = is_primary_with_prime(G)
  bool || return bool, ZZ(-1)
  if p == 1
    return bool, p
  end
  symp = local_symbol(G, p)
  if symp._symbol[end][1] != 1
    return false, ZZ(-1)
  end
  return true, p
end

@doc raw"""
    is_elementary(G::ZZGenus, p::Union{Integer, ZZRingElem}) -> Bool

Given a genus of integral $\mathbb Z$-lattices `G` and a prime number `p`,
return whether `G` is `p`-elementary, that is whether its associated discriminant
form (see [`discriminant_group`](@ref)) is an elementary `p`-group.
"""
function is_elementary(G::ZZGenus, p::Union{Integer, ZZRingElem})
  bool, q = is_elementary_with_prime(G)
  return bool && q == p
end

###############################################################################
#
# Re-scaling
#
###############################################################################

# TODO: this could be done faster by working on symbols directly! It is
# straightforward when p != 2; for p == 2 one has to be careful...
@doc raw"""
    rescale(G::ZZLocalGenus, a::RationalUnion) -> ZZLocalGenus

Given a local genus symbol `G` of $\mathbb Z$-lattices, return the local genus
symbol of any representative of `G` rescaled by `a`.
"""
function rescale(G::ZZLocalGenus, a::RationalUnion)
  @req !iszero(a) "a must be non-zero"
  a = QQ(a)
  p = prime(G)
  m = gram_matrix(G)
  return genus(a*m, p)
end

@doc raw"""
    rescale(G::ZZGenus, a::RationalUnion) -> ZZGenus

Given a genus symbol `G` of $\mathbb Z$-lattices, return the genus
symbol of any representative of `G` rescaled by `a`.
"""
rescale(::ZZGenus, ::RationalUnion)

function rescale(G::ZZGenus, a::IntegerUnion)
  @req !iszero(a) "a must be non-zero"
  a = ZZ(a)
  if isdefined(G, :_representative)
    return genus(rescale(G._representative, a))
  end
  sig_pair = signature_pair(G)
  sig_pair = a < 0 ? reverse(sig_pair) : sig_pair
  pd = prime_divisors(a)
  union!(pd, primes(G))
  sort!(pd)
  sym = eltype(local_symbols(G))[]
  for p in pd
    s = rescale(local_symbol(G, p), a)
    ss = symbol(s)
    p != 2 && length(ss) == 1 && ss[1][1] == 0 && continue
    push!(sym, s)
  end
  return ZZGenus(sig_pair, sym)
end

function rescale(G::ZZGenus, a::RationalUnion)
  @req !iszero(a) "a must be non zero"
  a = QQ(a)
  if isdefined(G, :_representative)
    return genus(rescale(G._representative, a))
  end
  G = rescale(G, numerator(a))
  sig_pair = signature_pair(G)
  a = denominator(a)
  pd = prime_divisors(a)
  union!(pd, primes(G))
  sort!(pd)
  sym = eltype(local_symbols(G))[]
  for p in pd
    s = rescale(local_symbol(G, p), 1//a)
    ss = symbol(s)
    p != 2 && length(ss) == 1 && ss[1][1] == 0 && continue
    push!(sym, s)
  end
  return ZZGenus(sig_pair, sym)
end

