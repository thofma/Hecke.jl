export genus, rank, det, dim, prime, symbol, representative, signature,
       oddity, excess, level, genera, scale, norm, mass, orthogonal_sum,
       quadratic_space,hasse_invariant, genera, local_symbol, local_symbols,
       ZGenus, ZpGenus, representatives

@doc Markdown.doc"""
    ZpGenus

Local genus symbol over a p-adic ring.

The genus symbol of a component `p^m A` for odd prime `= p` is of the
form `(m,n,d)`, where

- `m` = valuation of the component
- `n` = rank of A
- `d = det(A) \in \{1,u\}` for a normalized quadratic non-residue `u`.

The genus symbol of a component `2^m A` is of the form `(m, n, s, d, o)`,
where

- `m` = valuation of the component
- `n` = rank of `A`
- `d` = det(A) in `\{1,3,5,7\}`
- `s` = 0 (or 1) if even (or odd)
- `o` = oddity of `A` (= 0 if s = 0) in `Z/8Z`
      = the trace of the diagonalization of `A`

The genus symbol is a list of such symbols (ordered by `m`) for each
of the Jordan blocks `A_1,...,A_t`.

Reference: [Co1999]_ Conway && Sloane 3rd edition, Chapter 15, Section 7.


    INPUT:

    - ``prime`` -- a prime number
    - ``symbol`` -- the list of invariants for Jordan blocks `A_t,...,A_t` given
      as a list of lists of integers

"""
mutable struct ZpGenus
  _prime::fmpz
  _symbol::Vector{Vector{Int}}

  function ZpGenus(prime, symbol, check=true)
    if check
      if prime == 2
        @assert all(length(g)==5 for g in symbol)
        @assert all(s[3] in [1,3,5,7] for s in symbol)
      else
        @assert all(length(g)==3 for g in symbol)
      end
    end
    g = new()
    g._prime = prime
    g._symbol = symbol
    return g
  end
end

@doc Markdown.doc"""
    ZGenus

A collection of local genus symbols (at primes)
and a signature pair. Together they represent the genus of a
non-degenerate Zlattice.
"""
mutable struct ZGenus
  _signature_pair::Tuple{Int, Int}
  _symbols::Vector{ZpGenus} # assumed to be sorted by their primes
  _representative::ZLat

  function ZGenus(signature_pair, symbols)
    G = new()
    G._signature_pair = signature_pair
    G._symbols = sort!(symbols, by = x->prime(x))
    return G
  end

  function ZGenus(signature_pair, symbols, representative::ZLat)
    G = new()
    G._signature_pair = signature_pair
    G._symbols = sort!(symbols, by = x->prime(x))
    G._representative = representative
    return G
  end
end

###########################################################
# Computation of genus symbols
###########################################################

@doc Markdown.doc"""
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

@doc Markdown.doc"""
    _split_odd(A::MatElem) -> (fmpz, fmpz_mat)

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

@doc Markdown.doc"""
    _trace_diag_mod_8(A::MatElem) -> fmpz

Return the trace of the diagonalised form of `A` of an integral
symmetric matrix which is diagonalizable `\mod 8`.  (Note that since
the Jordan decomposition into blocks of size `<=` 2 is not unique
here, this is not the same as saying that `A` is always diagonal in
any `2`-adic Jordan decomposition!)

INPUT:

- ``A`` -- symmetric matrix with coefficients in `\ZZ` which is odd in
  `\ZZ/2\ZZ` && has determinant not divisible by `8`.
"""
function _trace_diag_mod_8(A::MatElem)
  R = ResidueRing(ZZ, 8)
  A8 = change_base_ring(R, A)
  tr = R(0)
  while nrows(A8) > 0
    u, A8 = _split_odd(A8)
    tr += u
  end
  tr = lift(tr)
  return mod(tr, 8)
end

@doc Markdown.doc"""
    _p_adic_symbol(A::MatElem) -> Vector{Vector{Int64}}

Given a symmetric matrix `A` && prime `p`, return the Conway Sloane
genus symbol at `p` represented as a list of lists.

The genus symbol of a component `p^m f` is of the form ``(m,n, d)``,
where

- `m` = valuation of the component
- `n` = dimension of `f`
- `d = det(f)` in `{1,-1}`
"""
function _p_adic_symbol(A::MatElem, p, val)
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
    Fp = GF(p)
    A_p = change_base_ring(Fp, A)
    bp, B_p = left_kernel(A_p)
    rref!(B_p)
    B_p = B_p[1:bp, 1:end]
    if nrows(B_p) == 0
      e0 = _kronecker_symbol(lift(det(A_p)),p)
      n0 = nrows(A)
      return [ [m0, n0, e0] ]
    else
      C_p = _basis_complement(B_p)
      e0 = _kronecker_symbol(lift(det(C_p * A_p * transpose(C_p))), p)
      n0 = nrows(C_p)
      sym = [ [0, n0, e0] ]
    end
    r = nrows(B_p)
    B = map_entries(lift, B_p)
    C = map_entries(lift, C_p)
    # Construct the blocks for the Jordan decomposition [F,X;X,A_new]
    F = change_base_ring(QQ, C * A * transpose(C))
    U = F^-1
    d = denominator(U)
    R = ResidueRing(ZZ, p^(val + 3))
    u = R(d)^-1

    U = change_base_ring(ZZ, U * d *lift(u))

    X = C * A
    A = B * (A - transpose(X)*U*X) * transpose(B)
    return [vcat([s[1]+m0] , s[2:end]) for s in vcat(sym,_p_adic_symbol(A, p, val)) ]
end


@doc Markdown.doc"""
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
function _two_adic_symbol(A::MatElem, val)
  n = nrows(A)
  # deal with the empty matrix
  if n == 0
    return [[0, 0, 1, 0, 0]]
  end
  m0 = minimum([ valuation(c,2) for c in A if c!=0])
  q = ZZ(2)^m0
  A = divexact(A, q)
  A_2 = change_base_ring(GF(2), A)
  k2, B_2 = left_kernel(A_2)
  rref!(B_2)
  B_2 = B_2[1:k2,1:end]
  R_8 = ResidueRing(ZZ, 8)
  # deal with the matrix being non-degenerate mod 2.
  if k2 == 0
    n0 = nrows(A)
    d0 = mod(det(A),8)
    @assert d0 != 0    # SANITY CHECK: The mod 8 determinant shouldn't be zero.
    even, i = _iseven(A)    # Determine whether the matrix is even || odd.
    if even
      return [[m0, n0, d0, 0, 0]]
    else
      tr8 = _trace_diag_mod_8(A)  # Here we already know that A_8 is odd
                                  # && diagonalizable mod 8.
      return [[m0, n0, d0, 1, tr8]]
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
      sym = [[0, n0, d0, 0, 0]]
    else
      tr8 = _trace_diag_mod_8(A_new)
      sym = [[0, n0, d0, 1, tr8]]
    end
  end
  r = nrows(B_2)
  B = map_entries(lift, B_2)
  C = map_entries(lift, C_2)
  F = change_base_ring(QQ, C * A * transpose(C))
  U = F^-1
  d = denominator(U)
  R = ResidueRing(ZZ,2^(val + 3))
  u = lift(R(d)^-1)
  U = change_base_ring(ZZ,U * d * u)
  X = C * A

  A = B * (A - transpose(X)*U*X) * transpose(B)
  return [ vcat([s[1]+m0], s[2:end]) for s in vcat(sym, _two_adic_symbol(A, val)) ]
end


@doc Markdown.doc"""
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

#########################################################
# Constructors
#########################################################

@doc Markdown.doc"""
    genus(A::MatElem)

Return the genus of the integer lattice with gram matrix `A`.
"""
function genus(A::MatElem)
  @req ncols(A) == nrows(A) "must be a square matrix"
  return genus(Zlattice(gram=A))
end

@doc Markdown.doc"""
    genus(L::ZLat) -> ZGenus

Return the genus of this lattice.
"""
function genus(L::ZLat)
  A = gram_matrix(L)
  denom = denominator(A)
  @req denom==1 "for now only genera of integral lattices are supported"
  A = change_base_ring(ZZ, denom^2 * A)
  symbols = ZpGenus[]
  if ncols(A)>0
    el = lcm(diagonal(hnf(A)))
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
    push!(symbols, genus(A, p, val, offset=2*valuation(denom,p)))
  end
  DA = diagonal(rational_span(L))
  neg = Int(count(x<0 for x in DA))
  pos = Int(count(x>0 for x in DA))
  @req neg+pos == ncols(A) "quadratic form is degenerate"
  return ZGenus((pos, neg), symbols, L)
end


function genus(L::ZLat, p)
  return genus(gram_matrix(L), p)
end

function genus(A::fmpz_mat, p, val; offset=0)
  @assert base_ring(A)==ZZ
  p = ZZ(p)
  symbol = _p_adic_symbol(A, p, val)
  for i in 1:size(symbol)[1]
    symbol[i][1] = symbol[i][1] - offset
  end
  return ZpGenus(p, symbol)
end

function genus(A::MatElem, p)
  offset = 0
  if base_ring(A) == QQ
    d = denominator(A)
    val = valuation(d, p)
    A = change_base_ring(ZZ, A*divexact(d^2, p^val))
    offset = valuation(d, p)
  end
  val = valuation(det(A), p)
  if p == 2
    val += 3
  end
  return genus(A, p, val, offset=offset)
end

@doc Markdown.doc"""
    orthogonal_sum(S1::ZpGenus, S2::ZpGenus) -> ZpGenus

Return the local genus of the orthogonal direct sum of two representatives.
"""
function orthogonal_sum(S1::ZpGenus, S2::ZpGenus)
  if prime(S1) != prime(S2)
    throw(ValueError("the local genus symbols must be over the same prime"))
  end
  _sym1 = S1._symbol
  _sym2 = S2._symbol
  m = max(_sym1[end][1], _sym2[end][1])
  sym1 = Dict([[s[1], s] for s in _sym1])
  sym2 = Dict([[s[1], s] for s in _sym2])
  symbol = Vector{Int}[]
  for k in 0:m
    if prime(S1) == 2
      b = [k, 0, 1, 0, 0]
    else
      b = [k, 0, 1]
    end
    for sym in [sym1, sym2]
      if haskey(sym,k)
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
  if rank(S1) == rank(S2) == 0
    symbol = S1._symbol
  end
  return ZpGenus(prime(S1), symbol)
end

direct_sum(S1::ZpGenus, S2::ZpGenus) = orthogonal_sum(S1, S2)

@doc Markdown.doc"""
    orthogonal_sum(G1::ZGenus, G2::ZGenus) -> ZGenus

Return the genus of the orthogonal direct sum of ``G1`` and ``G2``.

The orthogonal direct sum is defined via representatives.
"""
function orthogonal_sum(G1::ZGenus, G2::ZGenus)
  p1, n1 = G1._signature_pair
  p2, n2 = G2._signature_pair
  signature_pair = (p1 + p2, n1 + n2)
  primes = [prime(s) for s in G1._symbols]
  append!(primes, [prime(s) for s in G2._symbols if !(prime(s) in primes)])
  sort(primes)
  local_symbols = []
  for p in primes
    sym_p = orthogonal_sum(local_symbol(G1, p), local_symbol(G2, p))
    push!(local_symbols, sym_p)
  end
  return ZGenus(signature_pair, local_symbols)
end

direct_sum(S1::ZGenus, S2::ZGenus) = orthogonal_sum(S1, S2)


##########################################################
# Enumeration of genus symbols
##########################################################

@doc Markdown.doc"""
    genera(sig_pair::Vector{Int}, determinant::Union{Int,fmpz};
           max_scale=nothing, even=false) -> Vector{ZGenus}

Return a list of all global genera with the given conditions.

Here a genus is called global if it is non-empty.

INPUT:

- ``sig_pair`` -- a pair of non-negative integers giving the signature
- ``determinant`` -- an integer; the sign is ignored
- ``max_scale`` -- (default: ``Nothing``) an integer; the maximum scale of a
      jordan block
- ``even`` -- boolean (default: ``false``)

OUTPUT:

A list of all (non-empty) global genera with the given conditions.
"""
function genera(sig_pair::Tuple{Int,Int}, determinant::Union{Int,fmpz};
                max_scale=nothing, even=false)
  @req all(s >= 0 for s in sig_pair) "the signature vector must be a pair of non negative integers."
  if max_scale == nothing
    _max_scale = determinant
  else
    _max_scale = FlintZZ(max_scale)
  end
  rank = sig_pair[1] + sig_pair[2]
  out = ZGenus[]
  local_symbols = Vector{ZpGenus}[]
  # every global genus has a 2-adic symbol
  if mod(determinant, 2) == 1
    push!(local_symbols, _local_genera(ZZ(2), rank, 0, 0, even))
  end
  # collect the p-adic symbols
  for p in prime_divisors(determinant)
    det_val = valuation(determinant, p)
    mscale_p = valuation(_max_scale, p)
    local_symbol_p = _local_genera(p, rank, det_val, mscale_p, even)
    push!(local_symbols,local_symbol_p)
  end
  # take the cartesian product of the collection of all possible
  # local genus symbols one for each prime
  # && check which combinations produce a global genus
  # TODO:
  # we are overcounting. Find a more
  # clever way to directly match the symbols for different primes.
  for g in cartesian_product_iterator(local_symbols,inplace=false)
    # create a Genus from a list of local symbols
    G = ZGenus(sig_pair, g)
    # discard the empty genera
    if _isglobal_genus(G)
      push!(out, G)
    end
  end
  # render the output deterministic for testing
  sort!(out, by=x -> [s._symbol for s in x._symbols])
  return out
end

@doc Markdown.doc"""
    _local_genera(p, rank, det_val, max_scale, even) -> Vector{ZpGenus}

Return all `p`-adic genera with the given conditions.

This is a helper function for `genera`.
No input checks are done.

INPUT:
- ``p`` -- a prime number
- ``rank`` -- the rank of this genus
- ``det_val`` -- valuation of the determinant at p
- ``max_scale`` -- an integer the maximal scale of a jordan block
- ``even`` -- ``bool``; is ignored if `p` is not `2`
    """
function _local_genera(p::fmpz, rank::Int, det_val::Int, max_scale::Int,
                       even::Bool)
  scales_rks = Vector{Vector{Int}}[] # contains possibilities for scales & ranks
  for rkseq in _integer_lists(rank, max_scale+1)
    # rank sequences
    # sum(rkseq) = rank
    # length(rkseq) = max_scale + 1
    # now assure that we get the right determinant
    d = 0
    pgensymbol = Vector{Int}[]
    for i in 0:max_scale
      d += i * rkseq[i+1]
      # blocks of rank 0 are omitted
      if rkseq[i+1] != 0
        push!(pgensymbol,[i, rkseq[i+1], 0])
      end
    end
    if d == det_val
      push!(scales_rks,pgensymbol)
    end
  end
  # add possible determinant square classes
  symbols = Vector{ZpGenus}()
  if p != 2
    for g in scales_rks
      n = length(g)
      for v in cartesian_product_iterator([[-1, 1] for i in 1:n], inplace=false)
        g1 = deepcopy(g)
        for k in 1:n
          g1[k][3] = v[k]
        end
        g1 = ZpGenus(p, g1)
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
        append!(b,[0, 0])
        push!(poss_blocks,_blocks(b, (even && b[1] == 0)))
      end
      for g1 in cartesian_product_iterator(poss_blocks,inplace=false)
        if _is2adic_genus(g1)
          g1 = ZpGenus(p, g1)
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

function _local_genera(p::Int, rank::Int, det_val::Int, max_scale::Int,
                       even::Bool)
  return _local_genera(ZZ(p), rank, det_val, max_scale, even)
end

@doc Markdown.doc"""
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
      for s in [(1,2), (5,6), (1,6), (5,2), (7,0), (3,4)]
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
    for det in [d, mod(d * (-3) , 8)]
      b1 = copy(b1)
      b1[3] = det
        push!(blocks, b1)
    end
    # odd case
    if !even_only
      for s in [(1,2), (5,6), (1,6), (5,2), (7,0), (3,4)]
        b1 = copy(b)
        b1[3] = mod(s[1]*(-1)^(rk//2 -1) , 8)
        b1[4] = 1
        b1[5] = s[2]
        push!(blocks, b1)
      end
      for s in [(1,4), (5,0)]
        b1 = copy(b)
        b1[3] = mod(s[1]*(-1)^(rk//2 - 2) , 8)
        b1[4] = 1
        b1[5] = s[2]
        push!(blocks, b1)
      end
    end
  elseif rk % 2 == 1 && !even_only
    # odd case
    for t in [1, 3, 5, 7]
      d = mod((-1)^div(rk, 2) * t , 8)
      for det in [d, mod(-3*d, 8)]
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

############################################################
# Existence conditions
############################################################

@doc Markdown.doc"""
    _isglobal_genus(G::ZGenus) -> Bool

Return if `S` is the symbol of of a global quadratic form || lattice.
"""
function _isglobal_genus(G::ZGenus)
  D = det(G)
  r, s = signature_pair(G)
  R = ResidueRing(ZZ, 8)
  oddi = R(r - s)
  for loc in G._symbols
    p = loc._prime
    sym = loc._symbol
    v = sum([ss[1] * ss[2] for ss in sym])
    a = divexact(D, p^v)
    b = prod([ss[3] for ss in sym])
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

@doc Markdown.doc"""
    _is2adic_genus(symbol::Vector{Vector{Int}})-> Bool

Given a `2`-adic local symbol check whether it is symbol of a `2`-adic form.
"""
function _is2adic_genus(S::ZpGenus)
  @req prime(S)==2 "the symbol must be 2-adic"
  return _is2adic_genus(symbol(S))
end

@doc Markdown.doc"""
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

#######################################################
# Equality
#######################################################

function Base.:(==)(G1::ZpGenus, G2::ZpGenus)
  # This follows p.381 Chapter 15.7 Theorem 10 in Conway Sloane's book
  @req prime(G1) == prime(G2) ("Symbols must be over the same prime "
                                *"to be comparable")
  sym1 = [g for g in symbol(G1) if g[2] != 0]
  sym2 = [g for g in symbol(G2) if g[2] != 0]
  if length(sym1) == 0 || length(sym2) == 0
    return sym1 == sym2
  end
  if G1._prime != 2
    return sym1 == sym2
  end
  n = length(sym1)
  # scales && ranks
  s1 = [g[1:2] for g in sym1]
  s2 = [g[1:2] for g in sym2]
  if s1!=s2
    return false
  end
  # parity
  s1 = [g[4] for g in sym1]
  s2 = [g[4] for g in sym2]
  if s1 != s2
    return false
  end
  push!(sym1,[sym1[end][1]+1,0,1,0,0])
  push!(sym2,[sym1[end][1]+1,0,1,0,0])
  prepend!(sym1,[[-1,0,1,0,0]])
  prepend!(sym1,[[-2,0,1,0,0]])
  prepend!(sym2,[[-1,0,1,0,0]])
  prepend!(sym2,[[-2,0,1,0,0]])
  n = length(sym1)
  # oddity && sign walking conditions
  det_differs = [i for i in 1:n if _kronecker_symbol(sym1[i][3], 2)
                  != _kronecker_symbol(sym2[i][3], 2)]
  odd = [sym1[i][1] for i in 1:n if sym1[i][4] == 1]
  for m in sym2[1][1]:sym2[n][1]
    # "for each integer m for which f_{2^m} has type II, we have..."
    if m in odd
      continue
    end
    # sum_{q<2^m}(t_q-t'_q)
    l = sum(fmpz[sym1[i][5]-sym2[i][5] for i in 1:n if sym1[i][1]<m])
    # 4 (min(a,m)+min(b,m)+...)
    # where 2^a, 2^b are the values of q for which e_q!=e'_q
    r = 4*sum(fmpz[min(ZZ(m), sym1[i][1]) for i in det_differs])
    if 0 != mod(l-r, 8)
      return false
    end
  end
  return true
end

function Base.:(==)(G1::ZGenus, G2::ZGenus)
  t = length(G1._symbols)
  if t != length(G2._symbols)
    return false
  end
  for i in 1:t
    if G1._symbols[i] != G2._symbols[i]
      return false
    end
  end
  return true
end

#############################################################
# Printing
#############################################################

function Base.show(io::IO, G::ZGenus)
  rep = "ZGenus\nSignature: $(G._signature_pair)"
  for s in G._symbols
    rep *= "\n$s"
  end
  print(io, rep)
end

function Base.show(io::IO, G::ZpGenus)
  p = G._prime
  CS_string = ""
  if p == 2
    for sym in G._symbol
      s, r, d, e, o = sym
      d = _kronecker_symbol(d, 2)
      if s>=0
        CS_string *= " $(p^s)^$(d * r)"
      else
        CS_string *="(1/$(p^-s))^$(d * r)"
      end
      if e == 1
        CS_string *= "_$o"
      end
    end
  else
    for sym in G._symbol
      s,r ,d = sym
      CS_string *= " $(p^s)^$(d * r)"
    end
  end
  rep = "Genus symbol at $p:  $CS_string"
  print(io, rstrip(rep))
end

##################################################################
# Invariants and properties
##################################################################

@doc Markdown.doc"""
    prime(S::ZpGenus) -> fmpz

Return the prime `p` of this `p`-adic genus.
"""
function prime(S::ZpGenus)
  return S._prime
end

function symbol(S::ZpGenus)
  return copy(S._symbol)
end


@doc Markdown.doc"""
    iseven(S::ZpGenus) -> Bool

Return if the underlying `p`-adic lattice is even.

If `p` is odd, every lattice is even.
"""
function iseven(S::ZpGenus)
  if prime(S) != 2 || rank(S) == 0
    return true
  end

  sym = S._symbol[1]
  return sym[1] > 0 || sym[4] == 0
end

@doc Markdown.doc"""
    symbol(S::ZpGenus, scale::Int) -> Vector{Vector{Int64}}

Return a copy of the underlying lists of integers
for the Jordan block of the given scale
"""
function symbol(S::ZpGenus, scale::Int)
  sym = S._symbol
  for s in sym
    if s[1] == scale
      return copy(s)
    end
  end
  if S._prime != 2
    return [scale,0,1]
  else
    return [scale, 0,1,0,0]
  end
end

@doc Markdown.doc"""
  hasse_invariant(S::ZpGenus) -> Int

Return the Hasse invariant of a representative.
If the representative is diagonal (a_1,...a_n)
Then the Hasse invariant is

$\prod_{i<j}(a_i,a_j)_p$.
"""
function hasse_invariant(S::ZpGenus)
  # Conway Sloane Chapter 15 5.3
  n = dim(S)
  d = det(S)
  f0 = [squarefree_part(numerator(d)*denominator(d))]
  append!(f0, [1 for i in 2:n])
  f0 = diagonal_matrix(f0)
  f0 = genus(f0, prime(S))
  if excess(S) == excess(f0)
    return 1
  else
    return -1
  end
end

@doc Markdown.doc"""
    det(S::ZpGenus) -> fmpz

Return an integer representing the determinant of this genus.
"""
function det(S::ZpGenus)
  p = S._prime
  e = prod(Int[s[3] for s in S._symbol])
  if p == 2
    e = e % 8
  elseif e==-1
    e = _min_nonsquare(p)
  end
  return e*prod(fmpz[ p^(s[1]*s[2]) for s in S._symbol ])
end


@doc Markdown.doc"""
    dim(S::ZpGenus) -> fmpz

Return the dimension of this genus.
"""
function dim(S::ZpGenus)
  return sum(Int[s[2] for s in S._symbol])
end

function rank(S::ZpGenus)
  return dim(S)
end

@doc Markdown.doc"""
    excess(S::ZpGenus) -> Nemo.fmpz_mod

Return the p-excess of the quadratic form whose Hessian
matrix is the symmetric matrix A.

When p = 2 the p-excess is
called the oddity.
The p-excess is allways even && is divisible by 4 if
p is congruent 1 mod 4.

REFERENCE:
Conway && Sloane Lattices && Codes, 3rd edition, pp 370-371.
"""
function excess(S::ZpGenus)
  R = ResidueRing(ZZ, 8)
  p = S._prime
  if S._prime == 2
    return dim(S) - oddity(S)
  end
  k = 0
  for s in S._symbol
    if isodd(s[1]) && s[3] == -1
      k += 1
    end
  end
  return R(sum(fmpz[s[2]*(p^s[1]-1) for s in S._symbol]) + 4*k)
end

@doc Markdown.doc"""
    signature(S::ZpGenus) -> Nemo.fmpz_mod

Return the p-signature of this p-adic form.
"""
function signature(S::ZpGenus)
  R = ResidueRing(ZZ, 8)
  if S._prime == 2
    return oddity(S)
  else
    return R(dim(S)) - excess(S)
  end
end

@doc Markdown.doc"""
    oddity(S::ZpGenus) -> Int

Return the oddity of this even form.
The oddity is also called the 2-signature
"""
function oddity(S::ZpGenus)
  R = ResidueRing(FlintZZ, 8)
  p = S._prime
  @req p == 2 "the oddity is only defined for p=2"
  k = 0
  for s in S._symbol
    if mod(s[1], 2) == 1 && s[3] in (3, 5)
      k += 1
    end
  end
  return R(sum(Int[s[5] for s in S._symbol]) + 4*k)
end

@doc Markdown.doc"""
    scale(S::ZpGenus) -> fmpz

Return the scale of this local genus.

Let `L` be a lattice with bilinear form `b`.
The scale of `(L,b)` is defined as the ideal
`b(L,L)`.
"""
function scale(S::ZpGenus)
  if rank(S) == 0
    return ZZ(0)
  end
  return S._prime^S._symbol[1][1]
end

@doc Markdown.doc"""
    norm(S::ZpGenus) -> fmpz

Return the norm of this local genus.

Let `L` be a lattice with bilinear form `b`.
The norm of `(L,b)` is defined as the ideal
generated by `\{b(x,x) | x \in L\}`.
"""
function norm(S::ZpGenus)
  if rank(S) == 0
    return ZZ(0)
  end
  p = prime(S)
  if p == 2
    fq = S._symbol[1]
    return S._prime^(fq[1] + 1 - fq[4])
  else
    return scale(S)
  end
end
@doc Markdown.doc"""
    level(S::ZpGenus) -> fmpz

Return the maximal scale of a jordan component.
"""
function level(S::ZpGenus)
  if rank(S) == 0
    return ZZ(1)
  end
  return prime(S)^S._symbol[end][1]
end

@doc Markdown.doc"""
    iseven(G::ZGenus) -> Bool

Return if this genus is even.
"""
function iseven(G::ZGenus)
  if rank(G) == 0
    return true
  end
  return iseven(local_symbol(G, 2))
end


@doc Markdown.doc"""
    signature(G::ZGenus) -> Int

Return the signature of this genus.

The signature is `p - n` where `p` is the number of positive eigenvalues
and `n` the number of negative eigenvalues.
"""
function signature(G::ZGenus)
  p, n = G._signature_pair
  return p - n
end

@doc Markdown.doc"""
    signature_pair(G::ZGenus) -> Tuple{Int,Int}

Return the signature_pair of this genus.

The signature is `[p, n]` where `p` is the number of positive eigenvalues
and `n` the number of negative eigenvalues.
"""
function signature_pair(G::ZGenus)
  return G._signature_pair
end

@doc Markdown.doc"""
    det(G::ZGenus)

Return the determinant of this genus.
"""
function det(G::ZGenus)
  p, n = G._signature_pair
  return ZZ(-1)^n*prod(prime(g)^sum(Int[s[1]*s[2] for s in g._symbol])
                       for g in G._symbols)
end

@doc Markdown.doc"""
    dim(G::ZGenus) -> Int

Return the dimension of this genus.
"""
function dim(G::ZGenus)
  return sum(G._signature_pair)
end

rank(G::ZGenus) = dim(G)

@doc Markdown.doc"""
    local_symbols(G::ZGenus) -> Vecotr{ZpGens}

Return a copy of the local symbols.
"""
function local_symbols(G::ZGenus)
  return deepcopy(G._symbols)
end

@doc Markdown.doc"""
    local_symbol(G::ZGenus, p) -> ZpGenus

Return the local symbol at `p`.
"""
function local_symbol(G::ZGenus, p)
  p = ZZ(p)
  for sym in G._symbols
    if p == prime(sym)
      return deepcopy(sym)
    end
  end
  @assert p!=2
  sym_p = [[0, rank(G), _kronecker_symbol(det(G),p)]]
  return ZpGenus(p, sym_p)
end

@doc Markdown.doc"""
    level(G::ZGenus) -> fmpz

Return the level of this genus.

This is the denominator of the inverse gram matrix
of a representative.
"""
function level(G::ZGenus)
  return prod(level(sym) for sym in G._symbols)
end

@doc Markdown.doc"""
    scale(G::ZGenus) -> fmpz

Return the scale of this genus.

Let `L` be a lattice with bilinear form `b`.
The scale of `(L,b)` is defined as the ideal
`b(L,L)`.
"""
function scale(G::ZGenus)
  return prod([scale(s) for s in G._symbols])
end

@doc Markdown.doc"""
    norm(G::ZGenus) -> fmpz

Return the norm of this genus.

Let `L` be a lattice with bilinear form `b`.
The norm of `(L,b)` is defined as the ideal
generated by `\{b(x,x) | x \in L\}`.
"""
function norm(G::ZGenus)
  return prod([norm(s) for s in G._symbols])
end

##########################################################
# Representative & discriminant group
##########################################################

@doc Markdown.doc"""
    quadratic_space(G::ZGenus) -> QuadSpace{FlintRationalField, fmpq_mat}

Return the quadratic space defined by this genus.
"""
function quadratic_space(G::ZGenus)
  dimension = dim(G)
  if dimension == 0
    qf = zero_matrix(QQ, 0, 0)
    return quadratic_space(QQ, qf)
  end
  determinant = det(G)
  prime_neg_hasse = [prime(s) for s in G._symbols if hasse_invariant(s)==-1]
  neg = G._signature_pair[2]
  qf =_quadratic_form_with_invariants(dimension, determinant, prime_neg_hasse,
                                      neg)
  return quadratic_space(QQ, qf)
end

rational_representative(G::ZGenus) = quadratic_space(G)

@doc Markdown.doc"""
    discriminant_group(G::ZGenus) -> TorQuadMod

Return the discriminant form associated to this genus.
"""
function discriminant_group(G::ZGenus)
  qL = fmpq_mat[]
  for gs in G._symbols
    p = gs._prime
    for block in gs._symbol
      q = _gram_from_jordan_block(p, block, true)
      push!(qL, q)
    end
  end
  q = diagonal_matrix(qL)
  return TorQuadMod(q)
end

@doc Markdown.doc"""
    representative(G::ZGenus) -> ZLat

Compute a representative of this genus && cache it.
"""
function representative(G::ZGenus)
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

@doc Markdown.doc"""
    is_definite(G::ZGenus) -> Bool

Return if this genus is definite.
"""
is_definite(G::ZGenus) = any(x==0 for x in signature_pair(G))

@doc Markdown.doc"""
    representatives(G::ZGenus) -> Vector{ZLat}

Return a list of representatives of the isometry classes in this genus.
"""
function representatives(G::ZGenus)
  L = representative(G)
  rep = genus_representatives(L)
  @hassert :Lattice 2 !is_definite(G) || mass(G) == sum(fmpq[1//automorphism_group_order(S) for S in rep])
  return rep
end

@doc Markdown.doc"""
    gram_matrix(S::ZpGenus) -> MatElem

Return a gram matrix of some representative of this local genus.
"""
function gram_matrix(S::ZpGenus)
  G = fmpq_mat[]
  p = prime(S)
  for block in S._symbol
    push!(G, _gram_from_jordan_block(p, block))
  end
  G = diagonal_matrix(G)
  @hassert :Lattice 1  S==genus(G, p)
  return change_base_ring(QQ, G)
end

@doc Markdown.doc"""
    representative(S::ZpGenus) -> MatElem

Return an integer lattice which represents this local genus.
"""
function representative(S::ZpGenus)
  return Zlattice(gram=gram_matrix(S))
end


@doc Markdown.doc"""
    _gram_from_jordan_block(p::fmpz, block, discr_form=false) -> MatElem

Return the gram matrix of this jordan block.

This is a helper for `discriminant_form` && `representative`.
No input checks.

INPUT:

- ``p`` -- a prime number

- ``block`` -- a list of 3 integers || 5 integers if `p` is `2`

- ``discr_form`` -- Bool (default: ``false``); if ``true`` invert the scales
  to obtain a gram matrix for the discriminant form instead.
"""
function _gram_from_jordan_block(p::fmpz, block, discr_form=false)
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
        qL = fmpq_mat[U for i in 1:div(rk, 2)]
      else
        qL = fmpq_mat[U for i in 1:(div(rk, 2) - 1)]
        push!(qL, V)
      end
    elseif o == 1
      if rk % 2 == 1
        qL = fmpq_mat[U for i in 1:max(0, div(rk - 3, 2))]
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
        qL = fmpq_mat[U for i in 1:max(0, div(rk - 4, 2))]
        if (det , t) == (1, 0)
          append!(qL, fmpq_mat[U, 1 * W, 7 * W])
        elseif (det , t) == (1, 2)
          append!(qL, fmpq_mat[U, 1 * W, 1 * W])
        elseif (det , t) == (1, 4)
          append!(qL , fmpq_mat[V, 1 * W, 3 * W])
        elseif (det , t) == (1, 6)
          append!(qL, fmpq_mat[U, 7 * W, 7 * W])
        elseif (det , t) == (-1, 0)
          append!(qL, fmpq_mat[V, 1 * W, 7 * W])
        elseif (det , t) == (-1, 2)
          append!(qL, fmpq_mat[U, 3 * W, 7 * W])
        elseif (det , t) == (-1, 4)
          append!(qL, fmpq_mat[U, 1 * W, 3 * W])
        elseif (det , t) == (-1, 6)
          append!(qL, fmpq_mat[U, 1 * W, 5 * W])
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
      q = q * (1//2^level)
    else
      q = q * 2^level
    end
  elseif p != 2 && discr_form
    q = identity_matrix(QQ, rk)
    d = 2^(rk % 2)
    if _kronecker_symbol(d, p) != det
      u = _min_nonsquare(p)
      q[1,1] = u
    end
    q = q * (2 // p^level)
  end
  if p != 2 && !discr_form
    q = identity_matrix(QQ, rk)
    if det != 1
      u = _min_nonsquare(p)
      q[1,1] = u
    end
    q = q * p^level
  end
  return q
end

##################################################
# The mass formula
##################################################
@doc Markdown.doc"""
    _M_p(species, p) -> fmpq

Return the diagonal factor `M_p` as a function of the species.
"""
function _M_p(species, p)
  if species == 0
    return QQ(1)
  end
  p = QQ(p)
  n = abs(species)
  s = Int(div(n + 1,2))
  mp = 2 * prod(fmpq[1 - p^(-2*k) for k in 1:s-1])
  if n % 2 == 0
    mp *= ZZ(1) - sign(species) * p^(-s)
  end
  return QQ(1) // mp
end

@doc Markdown.doc"""
    _standard_mass_squared(G::ZGenus) -> fmpq

Return the standard mass of this genus.
It depends only on the dimension and determinant.
"""
function _standard_mass_squared(G::ZGenus)
  n = dim(G)
  if n % 2 == 0
    s = div(n, 2)
  else
    s = div(n, 2) + 1
  end
  std = QQ(2)^2
  std *= prod(fmpq[_gamma_exact(j // 2) for j in 1:n])^2
  std *= prod(fmpq[_zeta_exact(2*k) for k in 1:s-1])^2
  if n % 2 == 0
    D = ZZ(-1)^(s) * det(G)
    std *= _quadratic_L_function_squared(ZZ(s), D)
    d = fundamental_discriminant(D)
    # since quadratic_L_function__exact is different
    # from \zeta_D as defined by Conway && Sloane
    # we have to compensate
    # the missing Euler factors
    for sym in G._symbols
      p = sym._prime
      std *= (1 - _kronecker_symbol(d, p)*QQ(p)^(-s))^2
    end
  end
  return std
end

@doc Markdown.doc"""
    mass(G::ZGenus) -> fmpq

Return the mass of this genus.

The genus must be definite.
Let `L_1, ... L_n` be a complete list of representatives
of the isometry classes in this genus.
Its mass is defined as $\sum_{i=1}^n \frac{1}{|O(L_i)|}$.
"""
function mass(G::ZGenus)
  pos, neg = G._signature_pair
  @req pos * neg == 0 "the genus must be definite."
  if pos + neg == 1
    return QQ(1//2)
  end
  mass1 = _standard_mass_squared(G)
  mass1 *= prod(fmpq[_mass_squared(sym) for sym in G._symbols])
  mass1 //= prod(fmpq[_standard_mass(sym) for sym in G._symbols])^2
  return sqrt(mass1)
end


@doc Markdown.doc"""
    _mass_squared(G::ZpGenus) -> fmpq

Return the local mass `m_p` of this genus as defined by Conway.

See Equation (3) in [CS1988]_
"""
function _mass_squared(G::ZpGenus)
  @req dim(G) > 1 "the dimension must be at least 2"
  p = G._prime
  sym = G._symbol
  #diagonal product

  # diagonal factors
  m_p = prod(_M_p(species, p) for species in _species_list(G))^2
  # cross terms
  r = length(sym)
  ct = 0
  for j in 1:r
    for i in 1:j
        ct += (sym[j][1] - sym[i][1]) * sym[i][2] * sym[j][2]
    end
  end
  m_p *= p^ct
  if p != 2
    return m_p
  end
  # type factors
  nII = sum(fmpz[fq[2] for fq in sym if fq[4] == 0])
  nI_I = ZZ(0)   # the total number of pairs of adjacent constituents f_q,
  # f_2q that are both of type I (odd)
  for k in 1:r-1
    if sym[k][4] == sym[k+1][4] == 1 && sym[k][1] + 1 == sym[k+1][1]
      nI_I += ZZ(1)
    end
  end
  return m_p * QQ(2)^(2*(nI_I - nII))
end

@doc Markdown.doc"""
    _standard_mass(G::ZpGenus) -> fmpq

Return the standard p-mass of this local genus.

See Equation (6) of [CS1988]_.
"""
function _standard_mass(G::ZpGenus)
  n = dim(G)
  p = G._prime
  s = div(n + 1, 2)
  std = 2*prod(fmpq[1 - QQ(p)^(-2*k) for k in 1:s-1])
  if n % 2 == 0
    D = ZZ(-1)^s * det(G)
    epsilon = _kronecker_symbol(4*D, p)
    std *= (1 - epsilon*QQ(p)^(-s))
  end
  return QQ(1) // std
end

@doc Markdown.doc"""
    _species_list(G::ZpGenus) -> Vector{Int}

Return the species list.
See Table 1 in [CS1988]_.
"""
function _species_list(G::ZpGenus)
  p = prime(G)
  species_list = Int[]
  sym = G._symbol
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
      push!(symbols,[k, 0, 1, 0, 0])
    end
  end
  # avoid a case distinction
  sym = [[-2, 0, 1, 0, 0],[-1, 0, 1, 0, 0]]
  append!(sym, symbols)
  push!(sym, [sym[end-1][1] + 1, 0, 1, 0, 0])
  push!(sym, [sym[end-1][1] + 2, 0, 1, 0, 0])
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




@doc Markdown.doc"""
    _gamma_exact(n) -> fmpq

Evaluate the exact value of the `\Gamma^2` function at an integer or
half-integer argument. Ignoring factors of pi
"""
function _gamma_exact(n)
  n = QQ(n)
  if denominator(n) == 1
    @req (n > 0) "not in domain"
    return factorial(ZZ(n) - 1)
  end
  @req (denominator(n) == 2) "n must be in (1/2)ZZ"
  a = QQ(1)
  while n != 1//2
    if n < 0
      a //= n
      n += 1
    elseif n > 0
      n += -1
      a *= n
    end
  end
  return a
end

@doc Markdown.doc"""
    _zeta_exact(n) -> fmpq

Return the exact value of the Riemann Zeta function
ignoring factors of pi.

The argument must be a critical value, namely either positive even
or negative odd.

See for example [Iwa1972]_, p13, Special value of `\zeta(2k)`
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

@doc Markdown.doc"""
    _quadratic_L_function_squared(n, d) -> fmpq

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
  a = ZZ(-1)^(2 + (n - delta))
  a *= (2//f)^(2*n)
  a *= GS     # Evaluate the Gauss sum here! =0
  a *= 1//(4 * (-1)^delta)
  a *= _bernoulli_kronecker(Int(n),d)^2//factorial(ZZ(n))^2
  return a
end


@doc Markdown.doc"""
    rational_isometry_class(g::ZpGenus) -> LocalQuadSpaceCls

Return the abstract isometry class of the quadratic space
$g \otimes \mathbb{Q}$.
"""
function rational_isometry_class(g::ZpGenus)
  K = QQ
  n = dim(g)
  h = hasse_invariant(g)
  d = det(g)
  p = prime(g)
  return local_quad_space_class(K, ZZIdl(p), n, d, h, 0)
end

@doc Markdown.doc"""
    rational_isometry_class(g::ZGenus) -> QuadSpaceCls

Return the abstract isometry class of the quadratic space
$g \otimes \mathbb{Q}$.
"""
function rational_isometry_class(g::ZGenus)
  K = QQ
  G = class_quad_type(K)(K)
  n = dim(g)
  LGS = Dict{ideal_type(order_type(K)),localclass_quad_type(K) }()
  for s in local_symbols(g)
    h = hasse_invariant(s)
    p = prime(s)
    d = det(s)
    gp = local_quad_space_class(K, ZZIdl(p), n, d, h, 0)
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
# Representations
################################################################################

@doc Markdown.doc"""
    represents(g1::ZpGenus, g2::ZpGenus) -> Bool

Return if `g1` represents `g2`.

Based on O'Meara Integral Representations of Quadratic Forms Over Local Fields
Note that for `p == 2` there is a typo in O'Meara Theorem 3 (V).
The correct statement is
(V) $2^i(1+4\omega) \to \mathfrak{L}_{i+1}/\mathfrak{l}_{[i]}$.
"""
function represents(G1::ZpGenus, G2::ZpGenus)
  G1, G2 = G2, G1
	@req prime(G2) == prime(G1) "different primes"
  p = prime(G2)
  s1 = symbol(G1)
  s2 = symbol(G2)
  level = max(s1[end][1],s2[end][1])
  # notation
  function delta(pgenus::ZpGenus, i)
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
  gen1 = ZpGenus[]  # gen1[i+1] = \mathfrak{l}_i
  gen2 = ZpGenus[]  # gen1[i+1] = \mathfrak{L}_i

  for scale in 0:(level+2)
    i = scale + 1
    g1 = [s for s in s1 if s[1]<=scale]
    g2 = [s for s in s2 if s[1]<=scale]
    push!(gen1, ZpGenus(p, g1))
    push!(gen2, ZpGenus(p, g2))
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

  gen2_round = ZpGenus[]  # gen2_round[i-1] = \mathfrak{L}_{(i)}
  for scale in 0:(level + 2)
      g2 = [s for s in s2 if s[1]<scale || (s[1]==scale && s[4]==1)]
      push!(gen2_round, ZpGenus(p, g2))
  end

  gen1_square = ZpGenus[] # gen2_square[i-1] = \mathfrak{l}_{[i]}
  for scale in 0:level
      g1 = [s for s in s1 if s[1]<=scale || (s[1]==scale+1 && s[4]==0)]
      push!(gen1_square, ZpGenus(p, g1))
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
    # L is represented by itsself
    S = (ti1 + rational_isometry_class(gen2[i+1]))
    S= S - rational_isometry_class(gen1_square[i])
    if !(represents(S,ti1) || represents(S,ti2))
      return false
    end
  end
  return true
end

@doc Markdown.doc"""
    represents(G1::ZGenus, G2::ZGenus) -> Bool

Return if `G1` represents `G2`. That is if some element in the genus of `G1`
represents some element in the genus of `G2`.
"""
function represents(G1::ZGenus, G2::ZGenus)
  p1, m1 = signature_pair(G1)
  p2, m2 = signature_pair(G2)
  if  p1<p2 || m1 < m2
    return false
  end

  primes = [prime(s) for s in local_symbols(G1)]
  for s in local_symbols(G2)
    p = prime(s)
    if !(p in primes)
      push!(primes, p )
    end
  end

  for p in primes
    sp = local_symbol(G1, p)
    op = local_symbol(G2, p)
    if !represents(sp, op)
      return false
    end
  end
  return true
end

