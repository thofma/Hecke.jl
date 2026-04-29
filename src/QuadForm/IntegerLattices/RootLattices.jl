################################################################################
#
#  Root lattice constructor
#
################################################################################

@doc raw"""
    root_lattice(R::Symbol, n::Int, s::RationalUnion = 1) -> ZZLat

Return the root lattice ``L`` of type `R` given by `:A`, `:D` or `:E` with
parameter `n`.

The type `:I` with parameter `n = 1` is also allowed and denotes the odd
unimodular lattice of rank 1.

The nonzero rational number `s`, which is ``1`` by default, is a scaling factor: if
`s` is different from ``1``, then return the rescaled lattice ``L(s)``.

# Examples
```jldoctest
julia> root_lattice(:E, 8)
Integer lattice of rank 8 and degree 8
with gram matrix
[ 2   -1    0    0    0    0    0    0]
[-1    2   -1    0    0    0    0    0]
[ 0   -1    2   -1    0    0    0   -1]
[ 0    0   -1    2   -1    0    0    0]
[ 0    0    0   -1    2   -1    0    0]
[ 0    0    0    0   -1    2   -1    0]
[ 0    0    0    0    0   -1    2    0]
[ 0    0   -1    0    0    0    0    2]

julia> root_lattice(:I, 1)
Integer lattice of rank 1 and degree 1
with gram matrix
[1]

julia> root_lattice(:D, 4, -1)
Integer lattice of rank 4 and degree 4
with gram matrix
[-2    0    1    0]
[ 0   -2    1    0]
[ 1    1   -2    1]
[ 0    0    1   -2]
```
"""
function root_lattice(R::Symbol, n::Int, s::RationalUnion = 1)
  @req !iszero(s) "Scaling factor must be nonzero"
  if R === :A
    G = _root_lattice_A(n)
  elseif R === :E
    G = _root_lattice_E(n)
  elseif R === :D
    G = _root_lattice_D(n)
  elseif R === :I
    @req n == 1 "Parameter ($n) for odd root lattice (type $R) must be 1"
    G = QQ[1;]
  else
    error("Type (:$R) must be :A, :D, :E or :I")
  end
  if !isone(s)
    mul!(G, G, s)
  end
  return integer_lattice(; gram=G)
end

@doc raw"""
    root_lattice(R::Vector{Tuple{Symbol,Int}}) -> ZZLat

Return the root lattice of type `R` (see [`root_lattice`](@ref)).

#Example
```jldoctest
julia> root_lattice([(:A,2),(:A,1)])
Integer lattice of rank 3 and degree 3
with gram matrix
[ 2   -1   0]
[-1    2   0]
[ 0    0   2]

```
"""
function root_lattice(R::Vector{Tuple{Symbol,Int}})
  S = QQMatrix[gram_matrix(root_lattice(i[1], i[2])) for i in R]
  return integer_lattice(; gram=block_diagonal_matrix(S))
end

# WARNING: If the ordering of the basis vectors is changed
# several other function need to be changed as well
# A non exhaustive list: _weyl_vector, _highest_root, find_permutaton_and_ADE_type
# _weyl_group, ....
function _root_lattice_A(n::Int)
  @req n > 0 "Parameter ($n) for root lattice of type :A must be positive"
  z = zero_matrix(QQ, n, n)
  for i in 1:n
    z[i, i] = 2
    if i > 1
      z[i, i - 1] = -1
    end
    if i < n
      z[i, i + 1] = -1
    end
  end
  return z
end

# WARNING: If the ordering of the basis vectors is changed
# several other function need to be changed as well
function _root_lattice_D(n::Int)
  @req n >= 2 "Parameter ($n) for root lattices of type :D must be greater or equal to 2"
  if n == 2
    G = matrix(QQ, [2 0 ;0 2])
  elseif n == 3
    return _root_lattice_A(n)
  else
    G = zero_matrix(QQ, n, n)
    G[1,3] = G[3,1] = -1
    for i in 1:n
      G[i,i] = 2
      if 2 <= i <= n-1
        G[i,i+1] = G[i+1,i] = -1
      end
    end
  end
  return G
end

# WARNING: If the ordering of the basis vectors is changed
# several other function need to be changed as well
function _root_lattice_E(n::Int)
  @req n in [6,7,8] "Parameter ($n) for lattice of type :E must be 6, 7 or 8"
  if n == 6
    G = [2 -1 0 0 0 0;
        -1 2 -1 0 0 0;
        0 -1 2 -1 0 -1;
        0 0 -1 2 -1 0;
        0 0 0 -1 2 0;
        0 0 -1 0 0 2]
  elseif n == 7
    G = [2 -1 0 0 0 0 0;
        -1 2 -1 0 0 0 0;
        0 -1 2 -1 0 0 -1;
        0 0 -1 2 -1 0 0;
        0 0 0 -1 2 -1 0;
        0 0 0 0 -1 2 0;
        0 0 -1 0 0 0 2]
  else
    G = [2 -1 0 0 0 0 0 0;
        -1 2 -1 0 0 0 0 0;
        0 -1 2 -1 0 0 0 -1;
        0 0 -1 2 -1 0 0 0;
        0 0 0 -1 2 -1 0 0;
        0 0 0 0 -1 2 -1 0;
        0 0 0 0 0 -1 2 0;
        0 0 -1 0 0 0 0 2]
  end
  return matrix(QQ, G)
end

@doc raw"""
    root_symbols(n::Int) -> Vector{Vector{Tuple{Symbol, Int}}}

Return the list of all ADE root symbols, up to permutation,
whose combined rank is ``n``.

# Examples
```jldoctest
julia> root_symbols(3)
3-element Vector{Vector{Tuple{Symbol, Int64}}}:
 [(:A, 1), (:A, 1), (:A, 1)]
 [(:A, 2), (:A, 1)]
 [(:A, 3)]

```
"""
function root_symbols(n::Int)
  result = Vector{Tuple{Symbol, Int}}[]
  for p in AllParts(n)
    tmp = Vector{Tuple{Symbol, Int}}[]
    for i in p
      symb = Tuple{Symbol, Int}[]
      push!(symb, (:A, i))
      if i >= 4
        push!(symb, (:D, i))
      end
      if i in 6:8
        push!(symb, (:E, i))
      end
      push!(tmp, symb)
    end
    for i in cartesian_product_iterator(tmp; inplace=false)
      push!(result, i)
    end
  end
  return sort!(result)
end

"""
    root_lattices(n::Int) -> Vector{ZZLat}

Return the list of all even root lattices, up to isomorphism, of rank ``n``.

# Examples
```jldoctest
julia> rls = root_lattices(5)
9-element Vector{ZZLat}:
 Integer lattice of rank 5 and degree 5
 Integer lattice of rank 5 and degree 5
 Integer lattice of rank 5 and degree 5
 Integer lattice of rank 5 and degree 5
 Integer lattice of rank 5 and degree 5
 Integer lattice of rank 5 and degree 5
 Integer lattice of rank 5 and degree 5
 Integer lattice of rank 5 and degree 5
 Integer lattice of rank 5 and degree 5

julia> all(L -> L == root_sublattice(L), rls)
true
```
"""
function root_lattices(n::Int)
  result = ZZLat[]
  for p in AllParts(n)
    tmp = Vector{QQMatrix}[]
    for i in p
      lat = QQMatrix[]
      push!(lat, Hecke._root_lattice_A(i))
      if i >= 4
        push!(lat, Hecke._root_lattice_D(i))
      end
      if i in 6:8
        push!(lat, Hecke._root_lattice_E(i))
      end
      push!(tmp, lat)
    end
    for i in cartesian_product_iterator(tmp; inplace=true)
      g = diagonal_matrix(i)
      push!(result, integer_lattice(; gram=g))
    end
  end
  return result
end

@doc raw"""
    extended_ade(ADE::Symbol, n::Int)

Return the dual intersection matrix of an extended ade Dynkin diagram
as well as the isotropic vector (with positive coefficients in the roots).
"""
function extended_ade(ADE::Symbol, n::Int)
  R = change_base_ring(ZZ,gram_matrix(root_lattice(ADE,n)))
  G = block_diagonal_matrix([ZZ[2;],R])
  if ADE == :E && n == 8
    G[1,n] = -1
    G[n,1] = -1
  end
  if ADE == :E && n == 7
    G[1,2] = -1
    G[2,1] = -1
  end
  if ADE == :E && n == 6
    G[1,n+1] = -1
    G[n+1,1] = -1
  end
  if ADE == :A && n > 1
    G[1,2] = -1
    G[2,1] = -1
    G[1,n+1] = -1
    G[n+1,1] = -1
  end
  if ADE == :A && n == 1
    G[1,2]= -2
    G[2,1] = -2
  end
  if ADE == :D
    @assert n >= 4
    G[1,n] = -1
    G[n,1] = -1
  end
  @assert rank(G) == n
  return -G, kernel(G; side = :left)
end


################################################################################
#
#  Reflections and Weyl group
#
################################################################################

@doc raw"""
    reflection(gram::QQMatrix, v::QQMatrix) -> QQMatrix

Return the matrix representation of the orthogonal reflection in the row vector `v`.
"""
function reflection(gram::MatElem, v::MatElem)
  return _reflection(gram, v)
end

function _reflection(gram::MatElem, v::MatElem)
  n = ncols(gram)
  gram_v = gram*transpose(v)
  c = (v * gram_v)[1,1]
  ref = zero_matrix(base_ring(gram), n, n)
  # special cases for roots
  if c == 2
    for k in 1:n
      ref[k:k,:] = neg!(gram_v[k,1]*v)
      ref[k,k] += 1
    end
  elseif c == 1
    for k in 1:n
      ref[k:k,:] = neg!(2*gram_v[k,1]*v)
      ref[k,k] += 1
    end
  elseif c == -2
    for k in 1:n
      ref[k:k,:] = gram_v[k,1]*v
      ref[k,k] += 1
    end
  elseif c == -1
    for k in 1:n
      ref[k:k,:] = 2*gram_v[k,1]*v
      ref[k,k] += 1
    end
  else
    for k in 1:n
      ref[k:k,:] = neg!(divexact(2*gram_v[k,1], c)*v)
      ref[k,k] += 1
    end
  end

  return ref
end

################################################################################
#
#  Properties of root lattices
#
################################################################################
@doc raw"""
    coxeter_number(ADE::Symbol, n) -> Int

Return the Coxeter number of the corresponding ADE root lattice.

If ``L`` is a root lattice and ``R`` its set of roots, then the Coxeter number ``h``
is ``|R|/n`` where `n` is the rank of ``L``.

# Examples
```jldoctest
julia> coxeter_number(:D, 4)
6

```
"""
function coxeter_number(ADE::Symbol, n)
  if ADE == :A
    return n+1
  elseif ADE == :D
    return 2*(n-1)
  elseif ADE == :E && n == 6
    return 12
  elseif ADE == :E && n == 7
    return 18
  elseif ADE == :E && n == 8
    return 30
  end
end

@doc raw"""
    highest_root(ADE::Symbol, n) -> ZZMatrix

Return coordinates of the highest root of `root_lattice(ADE, n)`.

# Examples
```jldoctest
julia> highest_root(:E, 6)
[1   2   3   2   1   2]
```
"""
function highest_root(ADE::Symbol, n)
  if ADE == :A
    w = [1 for i in 1:n]
  elseif ADE == :D
    w = vcat([1,1],[2 for i in 3:n-1])
    w = vcat(w,[1])
  elseif ADE == :E && n == 6
    w = [1,2,3,2,1,2]
  elseif ADE == :E && n == 7
    w = [2,3,4,3,2,1,2]
  elseif ADE == :E && n == 8
    w = [2,4,6,5,4,3,2,3]
  end
  w = matrix(ZZ, 1, n, w)
  g = gram_matrix(root_lattice(ADE,n))
  @hassert :Lattice 2 all(0<=i for i in collect(w*g))
  @hassert :Lattice 2 (w*g*transpose(w))[1,1]==2
  return w
end

function _weyl_vector(R::ZZLat)
  weyl = matrix(ZZ,1,rank(R),ones(1,rank(R)))*inv(gram_matrix(R))
  return weyl*basis_matrix(R)
end

function _weyl_group_order(s::Symbol, n::IntegerUnion)
  n = ZZ(n)
  if s == :A
    ord = factorial(n+1)
  elseif s == :B
    @assert n>=2
    ord = ZZ(2)^n * factorial(n)
  elseif s == :C
    @assert n>=3
    ord = ZZ(2)^n * factorial(n)
  elseif s == :D
    @assert n>=4
    ord = ZZ(2)^(n-1) * factorial(n)
  elseif s == :E
    @assert 8>=n>=6
    if n == 6
      ord = 51840
    elseif n == 7
      ord = 2903040
    elseif n == 8
      ord = 696729600
    end
  elseif s == :F
    @assert n==4
    ord = 1152
  elseif s == :G
    @assert n==2
    ord = 12
  elseif s == :I
    @assert n==1
    ord = 2
  else
    error("invalid root system")
  end
  return ord
end


################################################################################
#
#  Root sublattice
#
################################################################################

@doc raw"""
    root_sublattice(L::ZZLat; length = [1, 2]) -> ZZLat

Return the sublattice spanned by the roots of length specified by `length`,
which by default are all roots of length at most $2$, and which must be
a subset of `[1, 2]` with unique entries.

# Examples
```jldoctest
julia> L = integer_lattice(gram = ZZ[1 0 0; 0 2 0; 0 0 3]);

julia> basis_matrix(root_sublattice(L))
[1   0   0]
[0   1   0]

julia> basis_matrix(root_sublattice(L; length = [2]))
[0   1   0]

julia> basis_matrix(root_sublattice(L; length = [1]))
[1   0   0]
```
"""
function root_sublattice(L::ZZLat; length::Vector{Int} = [1, 2], check::Bool=true)
  V = ambient_space(L)
  @req !check || is_integral(L) "L must be integral"
  @req !check || is_definite(L) "L must be definite"
  @req issubset(length, [1, 2]) "Root lengths must be in [1, 2]"
  if is_negative_entry(gram_matrix(L),1,1)#is_negative_definite(L)
    L = rescale(L,-1; cached=false)
  end
  # it is a bit awkward, because short_vectors(L, lb, ub) is slower than
  # short_vectors(L, ub)
  if Base.length(length) == 2
    sv = short_vectors(L, 2; check=false)
  else
    if length[1] == 1
      sv = short_vectors(L, 1; check=false)
    else
      sv = short_vectors(L, 2, 2; check=false)
    end
  end
  if Base.length(sv) == 0
    BZ = zero_matrix(ZZ, 0, rank(L))
  else
    BZ = _row_span!(first.(sv))
  end
  BQ = BZ*basis_matrix(L)
  return lattice(V, BQ; check=false, isbasis=true)
end


################################################################################
#
#  Root lattice recognition
#
################################################################################

@doc raw"""
    root_lattice_recognition(L::ZZLat)

Return the ADE type of the root sublattice of `L`.

The root sublattice is the lattice spanned by the vectors of squared length
$1$ and $2$.  The odd lattice of rank 1 and determinant $1$ is denoted by
`(:I, 1)`.

Input:

`L` -- a definite and integral $\mathbb{Z}$-lattice.

Output:

Two lists, the first one containing the ADE types
and the second one the irreducible root sublattices.

For more recognizable gram matrices use [`root_lattice_recognition_fundamental`](@ref).

# Examples

```jldoctest
julia> L = integer_lattice(; gram=ZZ[4  0 0  0 3  0 3  0;
                                     0 16 8 12 2 12 6 10;
                                     0  8 8  6 2  8 4  5;
                                     0 12 6 10 2  9 5  8;
                                     3  2 2  2 4  2 4  2;
                                     0 12 8  9 2 12 6  9;
                                     3  6 4  5 4  6 6  5;
                                     0 10 5  8 2  9 5  8])
Integer lattice of rank 8 and degree 8
with gram matrix
[4    0   0    0   3    0   3    0]
[0   16   8   12   2   12   6   10]
[0    8   8    6   2    8   4    5]
[0   12   6   10   2    9   5    8]
[3    2   2    2   4    2   4    2]
[0   12   8    9   2   12   6    9]
[3    6   4    5   4    6   6    5]
[0   10   5    8   2    9   5    8]

julia> R = root_lattice_recognition(L)
([(:A, 1), (:D, 6)], ZZLat[Integer lattice of rank 1 and degree 8, Integer lattice of rank 6 and degree 8])

julia> L = integer_lattice(; gram = QQ[1 0 0  0;
                                       0 9 3  3;
                                       0 3 2  1;
                                       0 3 1 11])
Integer lattice of rank 4 and degree 4
with gram matrix
[1   0   0    0]
[0   9   3    3]
[0   3   2    1]
[0   3   1   11]

julia> root_lattice_recognition(L)
([(:A, 1), (:I, 1)], ZZLat[Integer lattice of rank 1 and degree 4, Integer lattice of rank 1 and degree 4])
```
"""
function root_lattice_recognition(L::ZZLat; check::Bool=true)
  R, ADEs, comp = root_lattice_recognition_fundamental(L)
  return ADEs, comp
end

@doc raw"""
    root_lattice_recognition_fundamental(L::ZZLat)

Return the ADE type of the root sublattice of `L`
as well as the corresponding irreducible root sublattices
with basis given by a fundamental root system.

The type `(:I, 1)` corresponds to the odd unimodular
root lattice of rank 1.

Input:

`L` -- a definite and integral $\mathbb Z$-lattice.

Output:

- the root sublattice, with basis given by a fundamental root system
- the ADE types
- a Vector consisting of the irreducible root sublattices.

# Examples

```jldoctest
julia> L = integer_lattice(gram=ZZ[4  0 0  0 3  0 3  0;
                            0 16 8 12 2 12 6 10;
                            0  8 8  6 2  8 4  5;
                            0 12 6 10 2  9 5  8;
                            3  2 2  2 4  2 4  2;
                            0 12 8  9 2 12 6  9;
                            3  6 4  5 4  6 6  5;
                            0 10 5  8 2  9 5  8])
Integer lattice of rank 8 and degree 8
with gram matrix
[4    0   0    0   3    0   3    0]
[0   16   8   12   2   12   6   10]
[0    8   8    6   2    8   4    5]
[0   12   6   10   2    9   5    8]
[3    2   2    2   4    2   4    2]
[0   12   8    9   2   12   6    9]
[3    6   4    5   4    6   6    5]
[0   10   5    8   2    9   5    8]

julia> R = root_lattice_recognition_fundamental(L);

julia> gram_matrix(R[1])
[2    0    0    0    0    0    0]
[0    2    0   -1    0    0    0]
[0    0    2   -1    0    0    0]
[0   -1   -1    2   -1    0    0]
[0    0    0   -1    2   -1    0]
[0    0    0    0   -1    2   -1]
[0    0    0    0    0   -1    2]

```
"""
function root_lattice_recognition_fundamental(L::ZZLat; check::Bool=true)
  ADE, basis_matrices_wrt_L = _root_lattice_recognition_fundamental(L)
  B = basis_matrix(L)
  ambient_bases = QQMatrix[b*B for b in basis_matrices_wrt_L]
  V = ambient_space(L)
  C = lattice(V, reduce(vcat,ambient_bases; init=zero_matrix(QQ,0,degree(L))))
  components = ZZLat[lattice(V,b) for b in ambient_bases]
  return C, ADE, components
end


# For sv a set of roots compute the fundamental roots
# where a root is positive iff its first nonzero coefficient is positive.
# Modular version:
# - v1,...,vn are are linear independent if and only if
#   [ v_1 | ... | v_n] has full rank, which is equivalent to the determinant d
#   of maximal minor being non-zero but if 2 * d < p, then d = 0 is equivalent
#   to d = 0 mod p
# - thus we can test this mod p, if p is large enough
# - we only need p to be large enough for the vectors that we are currently looking at,
#   so we keep track of the entry size of the vectors we are considering and increase
#   the bound for p either if we (a) add a vector; or (b) encounter a with larger entry size
function _fundamental_roots!(sv::Vector{S}, p::T = next_prime(1 << (8 * sizeof(Int) - 2))) where {S, T}
  # choose a large prime < typemax(Int)
  if isempty(sv)
    return sv
  end
  _canonicalize!.(sv)
  sort!(sv)
  n = length(first(sv))
  B = zero_matrix(ZZ, 0, n)
  #=
  J = _find_minimal_indices(sv)
  B = zero_matrix(ZZ, length(J), n)
  reverse!(J)
  for i in 1:length(J)
    v = sv[J[i]]
    for j in 1:n
      B[i,j] = v[j]
    end
  end
  reverse!(J)
  # deleteat!(sv, J) #this is not good when we go to naive, then some roots are missing
  =#
  tmp = zero_matrix(ZZ, 1, n)
  fundamental = S[]
  n = length(sv[1])
  F = Hecke.Native.GF(p)
  M = zero_matrix(F, n + 1, n)
  # M[1:length(J),:] = B
  # rref!(M)
  tmp = ZZ()
  currank = nrows(B)
  r = currank + 1
  entryboundlog = 0
  detbound = ZZ(0)
  pivs = Int[]
  pure = Bool[]
  dirty = true
  update_bound = true
  for (i, v) in enumerate(sv)
    _ventryboundlog = _bound_entry(v)
    if _ventryboundlog > entryboundlog
      entryboundlog = _ventryboundlog
      update_bound = true
    end

    if update_bound
      r = currank + 1
      # Hadamard bound is r^(r/2) * B^r
      set!(detbound, r)
      detbound = pow!(detbound, detbound, div(r, 2) + 1)
      # p must be larger than 2 * detbound, so we multiply by an additional 2
      @ccall libflint.fmpz_mul_2exp(detbound::Ref{ZZRingElem}, detbound::Ref{ZZRingElem}, (entryboundlog + 1)::Int)::Cvoid
      update_bound = false
      if p <= detbound
        # return _fundamental_roots_new(sv, next_prime(ZZ(p)^2))
        # is too expensive, since we would have to write a fast version for
        # _reduce_modulo_rref for FpMatrix, but this is a lot of work
        #
        # So just call the "old" version
        return _fundamental_roots_naive!(sv)
      end
    end

    for i in 1:n
      s = F(v[i])
      @inbounds M[currank + 1, i] = s #v[i]
    end
    fl = _reduce_modulo_rref(M, currank, pivs, pure, dirty)
    if fl
      dirty = false
      continue
    end
    rref!(M)
    push!(fundamental, v)
    currank += 1
    if currank == n
      # will probably never happen, but cheap to test
      break
    end
    dirty = true
    resize!(pivs, currank)
    resize!(pure, currank)
    update_bound = true
  end
  return fundamental
end

# return the root types of the root sublattice of L
# and the basis matrices with respect to the basis of L
function _root_lattice_recognition_fundamental(L::ZZLat, fundamental_roots::Vector{ZZMatrix})
  G, d = _integral_split_gram(L)
  @assert isone(d)
  comp = _connected_components_graph!(fundamental_roots, G)
  types = Tuple{Symbol,Int}[]
  basis_matrices = ZZMatrix[]
  for c in comp
    g = c*G*transpose(c)
    ADE, perm = find_permutaton_and_ADE_type(g)
    push!(types, (ADE, nrows(c)))
    push!(basis_matrices, c[perm,:])
  end
  sp = sortperm(types; lt=(a,b) -> a[1] < b[1] || a[1] == b[1] && a[2] < b[2])
  return types[sp], basis_matrices[sp]
end

function _root_lattice_recognition_fundamental(L::ZZLat; do_lll::Bool=true)
  G, d = _integral_split_gram(L)
  if nrows(G)==0
    return Tuple{Symbol,Int}[],ZZLat[]
  end
  d > 1 && error("lattice not integral")
  if G[1,1]<0
    G = -G
  end
  diag = diagonal(G)
  mi = minimum(diag)
  ma = maximum(diag)
  lll_flag = !get_attribute(L, :is_lll_reduced, false) && do_lll && ma>6
  if lll_flag
    G, T = lll_gram_with_transform(G)
  end
  _sv1 = _short_vectors_gram_nolll_integral(FinckePohstInt, G, 0, 2, nothing, ZZ(1), Int)
  if !any(isone(i[2]) for i in _sv1)
    _short_vec = first.(_sv1)
  else
    sv1 = [i[1] for i in _sv1 if isone(i[2])]
    sv1_mat = [matrix(ZZ, 1, rank(L), i) for i in sv1]
    sv1_space = reduce(vcat, sv1_mat; init=zero_matrix(ZZ,0,rank(L)))
    K = kernel(G*transpose(sv1_space); side=:left)
    GK = K*G*transpose(K)
    L1perp = integer_lattice(gram=GK; cached=false)
    a = _root_lattice_recognition_fundamental(L1perp)
    return vcat([(:I, 1) for i in 1:length(sv1)], a[1]), vcat(sv1_mat, [i*K for i in a[2]])
  end
  fundamental_roots = ZZMatrix[matrix(ZZ, 1, rank(L), i) for i in _fundamental_roots!(_short_vec)]
  if lll_flag
    fundamental_roots = ZZMatrix[i*T for i in fundamental_roots]
  end
  return _root_lattice_recognition_fundamental(L, fundamental_roots)
end

@doc raw"""
    ADE_type(G::MatrixElem) -> Tuple{Symbol,Int64}

Return the type of the irreducible root lattice
with gram matrix `G`.

See also [`root_lattice_recognition`](@ref).

# Examples
```jldoctest
julia> Hecke.ADE_type(gram_matrix(root_lattice(:A,3)))
(:A, 3)
```
"""
function ADE_type(G::MatrixElem)
  r = rank(G)
  d = abs(det(G))
  if r == 1 && d == 1
    return (:I, 1)
  end
  if r == 8 && d==1
    return (:E, 8)
  end
  if r == 7 && d == 2
    return (:E, 7)
  end
  if r == 6 && d ==3
    return (:E, 6)
  end
  if d == r + 1
    return (:A, r)
  end
  if d == 4
    return (:D, r)
  end
  error("Not a definite root lattice")
end

# Given the gram matrix of an ADE fundamental root system
# Return A D or E and the permutation I with
# g[I,I] being the "standard" numbering of an ADE graph as in root_lattice
# if we ever change the standard ordering this code will stop working
function find_permutaton_and_ADE_type(H::MatrixElem)
  if nrows(H)==1
   @assert !is_zero_entry(H,1,1)
   return :A, [1]
  end
  r = nrows(H)
  isoftypeAn = true
  isoftypeEn = false
  exceptional_number = 0
  if 6 ≤ r ≤ 8
    isoftypeEn = true
  end
  path = zeros(Int, 2*r-1)
  path[r] = 1
  position = r
  neighbor = zeros(Int, 3)
  i = 2
  z = 1
  while i ≤ r
    if !is_zero_entry(H,i,1)
      neighbor[z] = i
      z += 1
    end
    i += 1
  end
  pivot1 = neighbor[1]
  pivot2 = neighbor[2]
  last_visited1 = 1
  last_visited2 = 1
  if neighbor[2] == 0
    neighborneighborcount = 0
    tmpnumber = neighbor[1]
    i = 1
    while i ≤ r
      if !is_zero_entry(H,i,tmpnumber)
        neighborneighborcount += 1
      end
      i += 1
    end
    if neighborneighborcount == 4
      isoftypeAn = false
      exceptional_number = 1
      path[r] = tmpnumber
      i = 1
      z = 1
      while i ≤ r
        if !is_zero_entry(H,i,tmpnumber)
          if i ≠ tmpnumber
            neighbor[z] = i
            z += 1
          end
        end
        i += 1
      end
      if neighbor[3] == 1
        pivot1 = neighbor[1]
        pivot2 = neighbor[2]
      elseif neighbor[2] == 1
        pivot1 = neighbor[1]
        pivot2 = neighbor[3]
      else
        pivot1 = neighbor[3]
        pivot2 = neighbor[2]
      end
      neighbor[3] = 0
      last_visited1 = tmpnumber
      last_visited2 = tmpnumber
    end
  end
  if neighbor[3] ≠ 0
    isoftypeAn = false
    exceptional_neighbor_index = 0
    for j in 1:3
      tmpnumber = neighbor[j]
      neighborneighborcount = 0
      i = 1
      while i ≤ r
        if !is_zero_entry(H,i,tmpnumber)
          neighborneighborcount += 1
        end
        i += 1
      end
      if neighborneighborcount == 2
        exceptional_neighbor_index = j
        break
      end
    end
    exceptional_number = neighbor[exceptional_neighbor_index]
    if exceptional_neighbor_index == 1
      pivot1 = neighbor[3]
    elseif exceptional_neighbor_index == 2
      pivot2 = neighbor[3]
    end
    neighbor[3] = 0
  end
  while true
    position -= 1
    path[position] = pivot1
    neighbor[1] = 0
    neighbor[2] = 0
    i = 1
    z = 1
    while i ≤ r
      if !is_zero_entry(H, i, pivot1)
        if i ≠ pivot1
          neighbor[z] = i
          z += 1
        end
      end
      i += 1
    end
    if neighbor[2] == 0
      break
    end
    if neighbor[3] ≠ 0
      isoftypeAn = false
      neighborneighborcount = 0
      tmpnumberisneighbor1 = (neighbor[1] == last_visited1)
      tmpnumber = tmpnumberisneighbor1 ? neighbor[2] : neighbor[1]
      i = 1
      while i ≤ r
        if !is_zero_entry(H,i,tmpnumber)
          neighborneighborcount += 1
        end
        i += 1
      end
      if neighborneighborcount == 2
        exceptional_number = tmpnumber
      else
        if tmpnumberisneighbor1
          exceptional_number = neighbor[3]
        else
          exceptional_number = (neighbor[2] == last_visited1) ? neighbor[3] : neighbor[2]
        end
      end
      if neighbor[1] == last_visited1
        last_visited1 = pivot1
        if neighbor[2] == exceptional_number
          pivot1 = neighbor[3]
        else
          pivot1 = neighbor[2]
        end
      elseif neighbor[2] == last_visited1
        last_visited1 = pivot1
        if neighbor[1] == exceptional_number
          pivot1 = neighbor[3]
        else
          pivot1 = neighbor[1]
        end
      else
        last_visited1 = pivot1
        if neighbor[1] == exceptional_number
          pivot1 = neighbor[2]
        else
          pivot1 = neighbor[1]
        end
      end
      neighbor[3] = 0
    else
      if neighbor[1] == last_visited1
        last_visited1 = pivot1
        pivot1 = neighbor[2]
      else
        last_visited1 = pivot1
        pivot1 = neighbor[1]
      end
    end
  end
  if pivot2 ≠ 0
    position = r
    while true
      position += 1
      path[position] = pivot2
      neighbor[1] = 0
      neighbor[2] = 0
      i = 1
      z = 1
      while i ≤ r
        if !is_zero_entry(H, i, pivot2)
          if i ≠ pivot2
            neighbor[z] = i
            z += 1
          end
        end
        i += 1
      end
      if neighbor[2] == 0
        break
      end
      if neighbor[3] ≠ 0
        isoftypeAn = false
        neighborneighborcount = 0
        tmpnumberisneighbor1 = (neighbor[1] == last_visited2)
        tmpnumber = tmpnumberisneighbor1 ? neighbor[2] : neighbor[1]
        i = 1
        while i ≤ r
          if !is_zero_entry(H,i,tmpnumber)
            neighborneighborcount += 1
          end
          i += 1
        end
        if neighborneighborcount == 2
          exceptional_number = tmpnumber
        else
          if tmpnumberisneighbor1
            exceptional_number = neighbor[3]
          else
            exceptional_number = (neighbor[2] == last_visited2) ? neighbor[3] : neighbor[2]
          end
        end
        if neighbor[1] == last_visited2
          last_visited2 = pivot2
          if neighbor[2] == exceptional_number
            pivot2 = neighbor[3]
          else
            pivot2 = neighbor[2]
          end
        elseif neighbor[2] == last_visited2
          last_visited2 = pivot2
          if neighbor[1] == exceptional_number
            pivot2 = neighbor[3]
          else
            pivot2 = neighbor[1]
          end
        else
          last_visited2 = pivot2
          if neighbor[1] == exceptional_number
            pivot2 = neighbor[2]
          else
            pivot2 = neighbor[1]
          end
        end
        neighbor[3] = 0
      else
        if neighbor[1] == last_visited2
          last_visited2 = pivot2
          pivot2 = neighbor[2]
        else
          last_visited2 = pivot2
          pivot2 = neighbor[1]
        end
      end
    end
  end
  path = path[findfirst(!isequal(0),path):end]
  path = path[1:findfirst(isequal(0),path)-1]
  if isoftypeAn
    return :A, path
  elseif isoftypeEn
    if !(is_zero_entry(H, path[3], exceptional_number) && is_zero_entry(H, path[end-2], exceptional_number))
      if is_zero_entry(H, path[end-2], exceptional_number)
        push!(path, exceptional_number)
      else
        pushfirst!(path, exceptional_number)
        reverse!(path)
      end
      return :E, path
    end
  end
  if is_zero_entry(H, path[2], exceptional_number)
    push!(path, exceptional_number)
    reverse!(path)
  else
    pushfirst!(path, exceptional_number)
  end
  return :D, path
end

################################################################################
#
#  Linear Algebra helpers
#
################################################################################
# For all i
# replace x[i] by -x[i] if its first non-zero coefficient is negative.
function _canonicalize_with_data!(x::Union{Vector, LinearAlgebra.Adjoint})
  length(x)==0 && return x, false
  i = 1
  flag = false
  while i<length(x) && iszero(x[i])
    i = i+1
  end
  if is_negative(x[i])
    flag = true
    x.= neg!.(x)
  end
  return x, flag
end

_canonicalize!(x::Union{Vector, LinearAlgebra.Adjoint}) = _canonicalize_with_data!(x)[1]

function _canonicalize!(x::MatElem)
  for i in eachindex(x)
    if !is_zero_entry(x, i[1], i[2])
      if is_negative(x[i])
        neg!(x)
      end
      break
    end
  end
  return x
end

function _find_minimal_indices(V::Vector{Vector{S}})::Vector{Int} where {S}
  level_dict = Dict{Int, Vector{Tuple{S, Int}}}()
  for (j, v) in enumerate(V)
    i = findfirst(!iszero, v)
    @assert v[i] > 0
    push!(get!(level_dict, i, Tuple{S,Int}[]), (v[i], j))
  end
  result = Int[]
  for pairs in values(level_dict)
    mi, idx = findmin(first, pairs)
    push!(result, pairs[idx][2])
  end
  sort!(result)
  return result
end

# For sv a set of roots compute the fundamental roots
# where a root is positive iff its first nonzero coefficient is positive.
function _fundamental_roots_naive!(sv::Vector{S}) where {S}
  fundamental = S[]
  if isempty(sv)
    return fundamental
  end
  _canonicalize!.(sv)
  sort!(sv)
  J = _find_minimal_indices(sv)
  n = length(first(sv))
  B = zero_matrix(ZZ, length(J), n)
  reverse!(J)
  for i in 1:length(J)
    v = sv[J[i]]
    push!(fundamental, v)
    for j in 1:n
      B[i,j] = v[j]
    end
  end
  reverse!(J)
  deleteat!(sv, J)
  tmp = zero_matrix(ZZ, 1, n)
  for v in sv
    for i in 1:n
      tmp[1, i] = v[i]
    end
    reduce_mod_hnf_ur!(tmp, B)
    if iszero(tmp)
      continue
    else
      B = vcat(B, tmp)
      hnf!(B)
      push!(fundamental, v)
    end
  end
  return fundamental
end

function _bound_entry(v::Vector{S}) where {S}
  s = zero(Int)
  for x in v
    s = max(s, nbits(x))
  end
  # so largest entry <= 2^s
  if s == 1
    # this can only be possible if all entries are in {-1,0, 1}, so bounded by 2^0
    return 0
  end
  return s
end

# Assumes that B = A[1:r, :]  is rref
# reduces A[r + 1:r + 1] modulo B
# pivs = pivot elements of each row
# pure = pure[i] == true means that A[i, :] is the pivs[i]-th unit vector
# dirty = true means that pivs and pure have to be recomputed
function _reduce_modulo_rref(A::fpMatrix, r, pivs::Vector, pure::Vector, dirty::Bool = true)
  c = ncols(A)
  l = r + 1
  have_pivs = !dirty
  _zero = zero(base_ring(A))
  for i in 1:r
    if have_pivs
      ind = @inbounds pivs[i]
      purerow = @inbounds pure[i]
    else
      ind = 1
      while ind <= c && is_zero(@inbounds A[i, ind])
        ind += 1
      end
      pivs[i] = ind
      # check if pure
      purerow = true
      for j in ind+1:c
        if !is_zero(@inbounds A[i, j])
          purerow = false
          break
        end
      end
      @inbounds pure[i] = purerow
    end
    w1ind = @inbounds A[l, ind]
    if iszero(w1ind)
      continue
    end
    if purerow
      @inbounds A[l, ind] = _zero
      continue
    end
    mult = divexact(w1ind, @inbounds A[i, ind])
    @inbounds A[l, ind] = _zero
    for k = ind+1:c
      x = @inbounds A[i, k]
      if !iszero(c)
        @inbounds A[l, k] -= mult * x
      end
    end
  end
  return is_zero_row(A, l)
end

function _reduce_modulo_rref(A::FpMatrix, r, pivs, pure, dirty::Bool = true)
  rref!(A)
  return is_zero_row(A, r + 1)
end
