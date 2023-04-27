################################################################################
#
#  Auto- and isomorphism computation of lattices
#
################################################################################

# This is (with permission) a port of the program ISOM and AUTO by Bernd
# Souvignier which implemented an algorithm published in
# W. PLESKEN, B. SOUVIGNIER, Computing Isometries of Lattices,
# Journal of Symbolic Computation, Volume 24, Issues 3-4, September 1997,
# Pages 327-334, ISSN 0747-7171, 10.1006/jsco.1996.0130.
# (https://www.sciencedirect.com/science/article/pii/S0747717196901303)

function VectorList(vectors::Vector{S}, lengths::Vector{Vector{T}},
                    use_dict::Bool = true) where {S, T}

  V = VectorList{S, T}()
  if use_dict
    V.lookup = Dict{S, Int}(vectors[i] => i for i in 1:length(vectors))
    V.lengths = lengths
    V.vectors = vectors
    V.use_dict = true
  else
    p = sortperm(vectors)
    permute!(vectors, p)       # apply the permutation to V
    permute!(lengths, p)       # apply the permutation to lengths
    V.use_dict = false
    V.vectors = vectors
    V.lengths = lengths
  end

  return V
end

length(V::VectorList) = length(V.vectors)

Base.issorted(V::VectorList) = V.issorted

getindex(V::VectorList, i::Int) = i > 0 ? V.vectors[i] : -V.vectors[-i]

function is_normalized(w::ZZMatrix)
  for k in 1:ncols(w)
    if !iszero(w[1, k])
      return w[1, k] > 0
    end
  end
end

function is_normalized(w::Vector{Int})
  for k in 1:length(w)
    if !iszero(w[k])
      return w[k] > 0
    end
  end
end

function neg!(w::Vector{Int})
  w .*= -1
end

function neg!(w::ZZMatrix)
  ccall((:fmpz_mat_neg, libflint), Cvoid, (Ref{ZZMatrix}, Ref{ZZMatrix}), w, w)
  return w
end

function find_point(w, V::VectorList)
  fl, k = has_point(w, V)
  @assert fl
  return k
end
#  positive = is_normalized(w)
#
#  if positive
#    k = V.lookup[w]
#    #k = findfirst(isequal(w), V.vectors)
#    #@assert k !== nothing
#    #@assert V[k] == w
#    #return k
#    return k
#  end
#
#  neg!(w)
#  #k = findfirst(isequal(w), V.vectors)
#  #@assert k !== nothing
#  k = V.lookup[w]
#  neg!(w)
#  @assert V[-k] == w
#  return -k
#end

function has_point(w, V::VectorList)
  positive = is_normalized(w)

  if positive
    k = get(V.lookup, w, 0)
    if k == 0
      return false, 0
    else
      @assert V[k] == w
      return true, k
    end
  end

  neg!(w)
  #k = findfirst(isequal(w), V.vectors)
  #@assert k !== nothing
  k = get(V.lookup, w, 0)
  neg!(w)
  if k == 0
    return false, 0
  else
    @assert V[-k] == w
    return true, -k
  end
end

function _find_point(w::ZZMatrix, V::VectorList{ZZMatrix, T}) where T
  positive = false
  for k in 1:length(w)
    if !iszero(w[1, k])
      positive = w[1, k] > 0
      break
    end
  end
  if positive
    if issorted(V)
      k = searchsortedfirst(V.vectors, w)
    else
      k = findfirst(isequal(w), V.vectors)
    end
    @assert k !== nothing
    return k
  else
    mw = -w
    if issorted(V)
      k = searchsortedfirst(V.vectos, mw)
    else
      k = findfirst(isequal(mw), V.vectors)
    end
    @assert k !== nothing
    return -k
  end
end

function Base.show(io::IO, C::ZLatAutoCtx)
  print(io, "Automorphism context for ", C.G)
end

dim(C::ZLatAutoCtx) = C.dim

function AbstractAlgebra.is_symmetric(M::MatElem)
  for i in 1:nrows(M)
    for j in i:ncols(M)
      if M[i, j] != M[j, i]
        return false
      end
    end
  end
  return true
end

function init(C::ZLatAutoCtx, auto::Bool = true, bound::ZZRingElem = ZZRingElem(-1), use_dict::Bool = true)
  # Compute the necessary short vectors

  r = length(C.G)

  n = nrows(C.G[1])

  if bound == -1
    bound = maximum(diagonal(C.G[1]))
    C.max = bound
  end

  @assert bound > 0

  @vprint :Lattice 1 "Computing short vectors of length $bound\n"

  @vtime :Lattice 1 V = _short_vectors_gram_integral(Vector, C.G[1], bound)

  vectors = Vector{ZZMatrix}(undef, length(V))

  lengths = Vector{Vector{ZZRingElem}}(undef, length(V))

  tmp = zero_matrix(FlintZZ, 1, n)

  for i in 1:length(V)
    # First canonicalize them
    cand = V[i]
    v = cand[1]
    k = 1
    while iszero(v[k])
      k += 1
    end
    if v[k] < 0
      v .*= -1
    end

    vfmpz = matrix(FlintZZ, 1, n, v)

    w = Vector{ZZRingElem}(undef, r)
    w[1] = numerator(cand[2])
    for k in 2:r
      w[2] = _norm(vfmpz, C.G[k], tmp)
    end

    lengths[i] = w
    vectors[i] = vfmpz
  end

  V = VectorList(vectors, lengths, use_dict)

  for i in 1:length(C.G)
    C.is_symmetric[i] = is_symmetric(C.G[i])
  end

  @assert C.is_symmetric[1]

  C.V = V

  # Compute the fingerprint
  @vprint :Lattice 1 "Computing fingerprint: "
  if auto
    @vtime :Lattice 1 fingerprint(C)
    @vprint :Lattice 1 "$(C.fp_diagonal)\n"
  end

  if auto
    # Find the standard basis vectors
    C.std_basis = Vector{Int}(undef, dim(C))
    z = zero_matrix(FlintZZ, 1, dim(C))
    for i in 1:dim(C)
      z[1, C.per[i]] = 1
      k = find_point(z, C.V)
      C.std_basis[i] = k
      z[1, C.per[i]] = 0
    end
  end

  #

  C.v = Vector{ZZMatrix}(undef, length(C.G))

  for i in 1:length(C.G)
    A = zero_matrix(FlintZZ, length(C.V), dim(C))
    for j in 1:length(C.V)
      for k in 1:dim(C)
        A[j, k] = _dot_product_with_row(C.V[j], C.G[i], k)
      end
    end
    C.v[i] = A
  end

  if false
    for i in 1:length(C.G)
      for j in 1:length(C.V)
        for k in 1:length(C.V)
          @assert _dot_product(C.V[j], C.v[i], k) == (C.V[j] * C.G[i] * transpose(C.V[k]))[1, 1]
        end
      end
    end
  end

  C.g = Vector{Vector{ZZMatrix}}(undef, dim(C))
  for i in 1:dim(C)
    C.g[i] = ZZMatrix[]
  end
  C.ng = zeros(Int, dim(C))
  C.nsg = zeros(Int, dim(C))
  C.orders = Vector{Int}(undef, dim(C))

  # -Id is always an automorphism
  C.g[1] = ZZMatrix[-identity_matrix(FlintZZ, dim(C))]
  C.ng[1] = 1

  # Calculate orbit lengths

  nH = 0

  for i in 1:dim(C)
    nH += C.ng[i]
  end

  H = Vector{ZZMatrix}(undef, nH)

  if auto
    for i in 1:dim(C)
      if C.ng[i] > 0
        nH = 0
        for j in i:dim(C)
          for k in 1:C.ng[j]
            nH += 1
            H[nH] = C.g[j][k]
          end
        end
        #@assert _orbitlen_naive(C.std_basis[i], C.fp_diagonal[i], H, nH, C.V) == _orbitlen(C.std_basis[i], C.fp_diagonal[i], H, nH, C.V)
        C.orders[i] = _orbitlen(C.std_basis[i], C.fp_diagonal[i], H, nH, C.V, C)
      else
        C.orders[i] = 1
      end
    end
  end

  return C
end

# The following functions tries to initialize a ZLatAutoCtx with entries in Int.
# The return value is flag, Csmall
function try_init_small(C::ZLatAutoCtx, auto::Bool = true, bound::ZZRingElem = ZZRingElem(-1), use_dict::Bool = true)
  # Compute the necessary short vectors
  @vprint :Lattice 1 "Computing short vectors of length $max\n"
  automorphism_mode = bound == ZZRingElem(-1)

  Csmall = ZLatAutoCtx{Int, Matrix{Int}, Vector{Int}}()

  if bound == -1
    bound = maximum(diagonal(C.G[1]))
    if fits(Int, bound)
      Csmall.max = Int(bound)
    else
      return false, Csmall
    end
  else
    Csmall.max = -1
  end
  @assert bound > 0

  @vtime :Lattice 1 V = _short_vectors_gram_integral(Vector, C.G[1], bound, Int)

  vectors = Vector{Vector{Int}}(undef, length(V))

  lengths = Vector{Vector{Int}}(undef, length(V))

  r = length(C.G)

  Gsmall = Matrix{Int}[Matrix{Int}(g) for g in C.G]

  Gsmall_nbits = 0
  for k in 1:r
    Gsmall_nbits = max(Gsmall_nbits, maximum(nbits, Gsmall[k]))
  end

  n = nrows(C.G[1])

  Gsmall_nbits = Gsmall_nbits + 1 # for the sign

  vectors_nbits = 0

  nrows_nbits = nbits(size(Gsmall[1], 1))

  bitbound = Int == Int64 ? 64 : 32

  abs_maxbits_vectors = Int == Int64 ? 30 : 15

  tmp = Vector{Int}(undef, n)

  for i in 1:length(V)
    # First canonicalize them
    cand = V[i]
    v = cand[1]
    vectors_nbits = max(vectors_nbits, maximum(nbits, v) + 1)
    k = 1

    while iszero(v[k])
      k += 1
    end

    if v[k] < 0
      v .*= -1
    end

    if vectors_nbits > abs_maxbits_vectors
      return false, Csmall
    end

    if Gsmall_nbits + vectors_nbits + nrows_nbits + 1 > bitbound
      return false, Csmall
    end

    _v = Vector{Int}(undef, n)

    for i in 1:n
      _v[i] = v[i]
    end

    w = Vector{Int}(undef, r)
    w[1] = Int(numerator(cand[2]))
    for k in 2:r
      w[k] = _norm(_v, Gsmall[k], tmp)
    end

    lengths[i] = w
    vectors[i] = _v
  end

  V = VectorList(vectors, lengths, use_dict)


  Csmall.V = V

  Csmall.prime = next_prime(2^(vectors_nbits + 1) + 1)

  Csmall.G = Matrix{Int}[Matrix{Int}(g) for g in C.G]
  Csmall.Gtr = Matrix{Int}[transpose(g) for g in Gsmall]
  Csmall.dim = n
  Csmall.is_symmetric = C.is_symmetric
  Csmall.operate_tmp = zeros(Int, n)

  @assert C.is_symmetric[1]

  # Compute the fingerprint
  if automorphism_mode
    @vprint :Lattice 1 "Computing fingerprint: "
    @vtime :Lattice 1 fingerprint(Csmall)
    @vprint :Lattice 1 "$(Csmall.fp_diagonal)\n"
  end

  if automorphism_mode
    # Find the standard basis vectors
    Csmall.std_basis = Vector{Int}(undef, dim(Csmall))
    z = zeros(Int, dim(Csmall))
    for i in 1:dim(Csmall)
      z[Csmall.per[i]] = 1
      k = find_point(z, V)
      Csmall.std_basis[i] = k
      z[Csmall.per[i]] = 0
    end
  end

  #

  Csmall.v = Vector{Matrix{Int}}(undef, length(C.G))

  # Here needs to be another overflow check
  @inbounds for i in 1:length(Csmall.G)
    A = zeros(Int, length(Csmall.V.vectors), dim(C))
    for j in 1:length(Csmall.V.vectors)
      for k in 1:dim(Csmall)
        A[j, k] = _dot_product_with_row(Csmall.V.vectors[j], Csmall.G[i], k)
      end
    end
    Csmall.v[i] = A
  end

  if false
    for i in 1:length(Csmall.G)
      for j in 1:length(Csmall.V.vectors)
        for k in 1:length(Csmall.V.vectors)
          @assert  _dot_product_with_row(Csmall.V.vectors[j], Csmall.v[i], k) == dot(reshape(Csmall.V[j], (1, dim(C))) * Csmall.G[i], Csmall.V[k])
        end
      end
    end
  end

  Csmall.g = Vector{Vector{Matrix{Int}}}(undef, dim(C))
  for i in 1:dim(Csmall)
    Csmall.g[i] = Matrix{Int}[]
  end
  Csmall.ng = zeros(Int, dim(Csmall))
  Csmall.nsg = zeros(Int, dim(Csmall))
  Csmall.orders = Vector{Int}(undef, dim(Csmall))

  # -Id is always an automorphism
  mid = zeros(Int, dim(Csmall), dim(Csmall))
  for i in 1:dim(Csmall)
    mid[i, i] = -1
  end
  Csmall.g[1] = Matrix{Int}[mid]
  Csmall.ng[1] = 1

  # Calculate orbit lengths

  nH = 0

  for i in 1:dim(Csmall)
    nH += Csmall.ng[i]
  end

  H = Vector{Matrix{Int}}(undef, nH)

  if automorphism_mode
    for i in 1:dim(Csmall)
      if Csmall.ng[i] > 0
        nH = 0
        for j in i:dim(Csmall)
          for k in 1:Csmall.ng[j]
            nH += 1
            H[nH] = Csmall.g[j][k]
          end
        end
        #@assert _orbitlen_naive(Csmall.std_basis[i], Csmall.fp_diagonal[i], H, nH, Csmall.V) == _orbitlen(Csmall.std_basis[i], Csmall.fp_diagonal[i], H, nH, Csmall.V)
        Csmall.orders[i] = _orbitlen(Csmall.std_basis[i], Csmall.fp_diagonal[i], H, nH, Csmall.V, Csmall)
      else
        Csmall.orders[i] = 1
      end
    end
  end

  return true, Csmall
end

#function compute_scpcomb(C::ZAutLatCtx, depth::Int)
#  comb = Vector{SCPComp}(undef, dim(C))
#  for i in 1:dim(C)
#  end
#end


#	if (flags.DEPTH > 0)
#	{
#		if ((comb = (scpcomb*)malloc(dim * sizeof(scpcomb))) == 0)
#			exit (1);
#		for (i = 0; i < dim; ++i)
#		{
#/* compute the list of scalar product combinations and the corresponding
#   vector sums */
#			scpvecs(&comb[i].list, &sumveclist, i, fp.e, flags.DEPTH, V, F);
#/* compute a basis for the lattice that is generated by the vector sums and
#   a transformation matrix that expresses the basis in terms of the
#   vector sums */
#			base(&comb[i], &sumvecbase, sumveclist, F.A[0], dim);
#			if (flags.PRINT == 1)
#/* if the -P option is given, print the rank of the lattice generated by the
#   vector sums on level i on AUTO.tmp */
#			{
#				outfile = fopen("AUTO.tmp", "a");
#				fprintf(outfile, "comb[%d].rank = %d\n", i, comb[i].rank);
#				fclose(outfile);
#			}
#/* compute the coefficients of the vector sums in terms of the basis */
#			coef(&comb[i], sumvecbase, sumveclist, F.A[0], dim);
#			for (j = 0; j <= comb[i].list.n; ++j)
#				free(sumveclist[j]);
#			free(sumveclist);
#/* compute the scalar products of the base-vectors */
#			scpforms(&comb[i], sumvecbase, F);
#			for (j = 0; j < comb[i].rank; ++j)
#				free(sumvecbase[j]);
#			free(sumvecbase);
#		}
#	}

function compute_short_vectors(C::ZLatAutoCtx{Int, Matrix{Int}, Vector{Int}}, max = ZZRingElem(-1))
  #V = enumerate_using_gram(G, R(max))

  if max == -1
    max = maximum(C.G[1][i, i] for i in 1:dim(C))
  end

  @vprint :Lattice 1 "Computing short vectors of actual length $max\n"
  V = _short_vectors_gram_integral(Vector, C.G[1], max)
  return V
end

function compute_short_vectors(C::ZLatAutoCtx, max::ZZRingElem = ZZRingElem(-1))
  #V = enumerate_using_gram(G, R(max))

  if max == -1
    max = maximum(C.G[1][i, i] for i in 1:dim(C))
  end
  @vprint :Lattice 1 "Computing short vectors of actual length $max\n"
  V = _short_vectors_gram_integral(Vector, C.G[1], max)
  n = ncols(C.G[1])
  C.V = Vector{ZZMatrix}(undef, length(V))
  C.V_length = Vector{Vector{ZZRingElem}}(undef, length(V))
  for i in 1:length(V)
    z = Vector{ZZRingElem}(undef, length(C.G))
    z[1] = V[i][2]
    m = matrix(FlintZZ, 1, n, V[i][1])
    mt = transpose(m)
    for k in 2:length(C.G)
      z[k] = (m * C.G[k] * mt)[1, 1]
    end
    C.V[i] = m
    C.V_length[i] = z
  end
  #@show length(C.V)
  C.max = max
  return C
end

function _get_vectors_of_length(G::Union{ZZMatrix, FakeFmpqMat}, max::ZZRingElem)
  C = enum_ctx_from_gram(G)
  enum_ctx_start(C, max)
  res = Tuple{ZZMatrix, ZZRingElem}[]
  while enum_ctx_next(C)
    push!(res, (deepcopy(C.x), (C.x * G * transpose(C.x))[1, 1]))
    push!(res, (-deepcopy(C.x), (C.x * G * transpose(C.x))[1, 1]))
  end
  return res
end

function _get_vectors_of_length(G::ZLat, max::ZZRingElem)
  return _get_vectors_of_length(FakeFmpqMat(gram_matrix(G)), max)
end

function possible(C::ZLatAutoCtx, per, I, J)
  V = C.V.vectors
  W = C.V.lengths
  F = C.G
  Ftr = C.Gtr
  n = length(W)
  f = length(F)
  _issymmetric = C.is_symmetric
  return possible(V, W, F, Ftr, _issymmetric, n, f, per, I, J)
end

function possible(V, W, F, Ftr, _issymmetric, n, f, per, I, J)
  count = 0

  tmp1 = zero(eltype(V[1]))
  tmp2 = zero(eltype(V[1]))

  for j in 1:n
    Wj = W[j]
    Vj = V[j]
    good_scalar = true
    good_length = true
    @inbounds for k in 1:f
      if Wj[k] != F[k][J, J]
        good_length = false
        break
      end
    end

    if !good_length
      continue
    end

    @inbounds for k in 1:f
      for i in 1:I
        if !(_dot_product_with_column!(tmp1, Vj, F[k], per[i], tmp2) == F[k][J, per[i]]) ||
              (!_issymmetric[k] && _dot_product_with_row!(tmp1, Vj, F[k], per[i], tmp2) != F[k][per[i], J])
          good_scalar = false
          break
        end
      end

      if !good_scalar
        break
      end
    end

    if good_length && good_scalar
      count = count + 1
    end

    if !good_length
      continue
    end

    # length is correct

    good_scalar = true

    @inbounds for k in 1:f
      for i in 1:I
        if !(_dot_product_with_column!(tmp1, Vj, F[k], per[i], tmp2) == -F[k][J, per[i]]) ||
              (!_issymmetric[k] && _dot_product_with_row!(tmp1, Vj, F[k], per[i], tmp2) != -F[k][per[i], J])
          good_scalar = false
          break
        end

      end

      if !good_scalar
        break
      end
    end

    if good_scalar
      count = count + 1
    end
  end
  return count
end

#function _dot_product(V::Vector, M, i)
#  z = zero(base_ring(V))
#  for j in 1:length(V)
#    z = z + V[j] * M[i, j]
#  end
#  return z
#end
#
#function _dot_product(V::ZZMatrix, M, i)
#  z = zero(base_ring(V))
#  for j in 1:length(V)
#    z = z + V[1, j] * M[i, j]
#  end
#  return z
#end

# a permutation per for the
#	order of the basis-vectors is chosen
#	such that in every step the number of
#	possible continuations is minimal,
#	for j from per[i] to per[dim-1] the
#	value f[i][j] in the fingerprint f is
#	the number of vectors, which have the
#	same scalar product with the
#	basis-vectors per[0]...per[i-1] as the
#	basis-vector j and the same length as
#	this vector with respect to all
#	invariant forms

function fingerprint(C::ZLatAutoCtx)
  V = C.V
  n = dim(C)
  k = length(C.G)
  per = Vector{Int}(undef, n)
  for i in 1:n
    per[i] = i
  end

  fp = zeros(Int, n, n)

  # fp[1, i] = # vectors v such that v has same length as b_i for all forms
  @inbounds for i in 1:n
    for j in 1:length(V)
      good = true
      cvl = @inbounds V.lengths[j]
      for l in 1:k
        if cvl[l] != C.G[l][i, i]
          good = false
          break
        end
      end

      if good
        fp[1, i] += 2 # the negative vector also has the correct length
      end
    end
  end

  @inbounds for i in 1:(n - 1)
    # Find the minimal non-zero entry in the i-th row
    mini = i
    for j in (i+1):n
      if fp[i, per[j]] < fp[i, per[mini]]
        mini = j
      end
    end

    per[mini], per[i] = per[i], per[mini]

    # Set entries below the minimal entry to zero
    for j in (i + 1):n
      fp[j, per[i]] = 0
    end

    # Now compute row i + 1

    for j in (i + 1):n
      fp[i + 1, per[j]] = possible(C, per, i, per[j])
    end
  end

  # Extract the diagonal

  res = Vector{Int}(undef, n)

  @inbounds for i in 1:n
    res[i] = fp[i, per[i]]
  end

  C.fp = fp

  C.fp_diagonal = res

  C.per = per

  return per, fp, res
end

# computes min(#O, orblen), where O is the orbit of pt under the first nG matrices in G
function _orbitlen(point::Int, orblen::Int, G::Vector{T}, nG, V, C) where {T}
  n = length(V)
  orb = ones(Int, orblen)
  orb[1] = point
  flag = zeros(Bool, 2*n + 1)
  flag[point + n + 1] = true
  # if flag[i + n+1] = 1, -n <= i <= n, then the point i is already in the orbit
  #flag = zero_Flv(2*n + 1)+n+1;
  #orb  = zero_Flv(orblen);
  #orb[1] = pt;
  #flag[pt] = 1;
  len = 1
  cnd = 1
  #@show G, nG
  while cnd <= len && len < orblen
    i = 1
    while i <= nG && len < orblen
      imag = _operate(orb[cnd], G[i], V, C.operate_tmp)
      if !flag[imag + n + 1]
        # the image is a new point in the orbit
        len += 1
        orb[len] = imag
        flag[imag + n + 1] = true
      end
      i += 1
    end
    cnd += 1
  end
  return len
end


function _operate(point, A::Matrix{Int}, V)
  return _operate(point, A, V, zeros(Int, size(A, 2)), sorted)
end

function _operate(point, A::ZZMatrix, V)
  return _operate(point, A, V, zero_matrix(FlintZZ, 1, ncols(A)))
end

Base.replace!(::typeof(-), m::ZZMatrix) = -m

function _operate(point, A, V, tmp)
# 	V.v is a sorted list of length V.n of vectors
#				of dimension V.dim, the number of V.v[nr]*A in
#				the list is returned, where a negative number
#				indicates the negative of a vector
  tmp = _vec_times_matrix!(tmp, V[point], A)
  #w = V[abs(point)] * A
  #if point < 0
  #  if tmp isa ZZMatrix
  #    for i in 1:ncols(tmp)
  #      tmp[1, i] = -tmp[1, i]
  #    end
  #  else
  #    tmp .*= -1 # tmp = -tmp
  #  end
  #end
  k = find_point(tmp, V)
  #@assert V[k] == tmp
  return k
end

function _find_point(w::Vector{Int}, V)
  positive = false
  for k in 1:length(w)
    if !iszero(w[k])
      positive = w[k] > 0
      break
    end
  end
  if positive
    if sorted
      k = searchsortedfirst(V, w)
    else
      k = findfirst(isequal(w), V)
    end
    @assert k !== nothing
    return k
  else
    w .*= -1 # w = -w
    if sorted
      k = searchsortedfirst(V, w)
    else
      k = findfirst(isequal(w), V)
    end
    @assert k !== nothing
    w .*= -1 # w = -w
    return -k
  end
end

function _find_point(w::ZZMatrix, V)
  positive = false
  for k in 1:length(w)
    if !iszero(w[1, k])
      positive = w[1, k] > 0
      break
    end
  end
  if positive
    if sorted
      k = searchsortedfirst(V, w)
    else
      k = findfirst(isequal(w), V)
    end
    @assert k !== nothing
    return k
  else
    mw = -w
    if sorted
      k = searchsortedfirst(V, mw)
    else
      k = findfirst(isequal(mw), V)
    end
    @assert k !== nothing
    return -k
  end
end

function _orbitlen_naive(point::Int, orblen::Int, G::Vector{ZZMatrix}, nG::Int, V)
  working_list = Int[point]
  orbit = Int[point]
  while !isempty(working_list)
    current_point = pop!(working_list)
    for i in 1:nG
      if current_point < 0
        new_point_coord = -V[abs(current_point)] * G[i]
      else
        new_point_coord = V[current_point] * G[i]
      end
      new_point = find_point(new_point_coord, V)
      if !(new_point in orbit)
        push!(orbit, new_point)
        push!(working_list, new_point)
      end
    end
  end
  return min(orblen, length(orbit))
end

function auto(C::ZLatAutoCtx{S, T, U}) where {S, T, U}
  dim = Hecke.dim(C)

  candidates = Vector{Vector{Int}}(undef, dim) # candidate list for the image of the i-th basis vector

  for i in 1:dim
    candidates[i] = zeros(Int, C.fp_diagonal[i])
  end

  x = Vector{Int}(undef, dim)
  bad = Vector{Int}(undef, 2 * length(C.V))

  sta = 1
  for step in sta:dim
    @vprint :Lattice 1 "Entering step $step\n"
    nH = 0
    for i in step:dim
      nH += C.ng[i]
    end
    #@show nH
    H = Vector{T}(undef, nH)
    nH = 0
    @inbounds for i in step:dim
      for j in 1:C.ng[i]
        nH += 1
        #@show C.g[i]
        H[nH] = C.g[i][j]
      end
    end
    @inbounds for i in 1:2*length(C.V)
      bad[i] = 0
    end
    nbad = 0
    @inbounds for i in 1:(step - 1)
      x[i] = C.std_basis[i]
    end
    #@show C.fp_diagonal[step]
    #@show candidates
    if C.fp_diagonal[step] > 1
      nC = cand(candidates[step], step, x, C, 0)#comb)
    else # there is only one candidates
      candidates[step] = Int[C.std_basis[step]]
      nC = 1
    end
    #@show nC
    #@show candidates
    orb = orbit(C.std_basis[step], 1, H, nH, C.V, C)
    C.orders[step] = length(orb)
    # delete the orbit of the step-th basis vector from the candidates
    #nC = delete(candidates[step], nC, orb, C.orders[step])
    setdiff!(candidates[step], orb)
    nC = length(candidates[step])
    #@show step, nC
    while nC > 0 && ((im = candidates[step][1]) != 0)
      @vprint :Lattice 1 "Step $(step), number of candidates left $(nC)\n"
      #@show im
      found = 0
      # try C.V[im] as the image of the step-th basis vector
      x[step] = im
      if step < dim
        #@show candidates
        if cand(candidates[step + 1], step + 1, x, C, 0) == C.fp_diagonal[step + 1]
          #@show candidates
          #@show "right before aut"
          #@show step + 1, x
          found = aut(step + 1, x, candidates, C, 0)#comb)
        else
          found = 0
        end
      else
        found = 1
      end

      #@show found

      if found == 0
        # x[1],...,x[step] cannot be continued
        oc = orbit(im, 1, H, nH, C.V, C)
        # delete the orbit of im from the candidates for x[step]
        #
        # This could go very bad ...
        candidates[step] = setdiff!(candidates[step], oc)
        nC = length(candidates[step])
        #nC = delete(candidates[step], nC, oc, noc)
        #empty!(oc)
        nbad += 1
        bad[nbad] = im
      else
        #@show x, step
        # a new generator has been found
        C.ng[step] += 1
        # append the new generator to C.>g[step]
        #@show "================================"
        ##@show C.g, step
        Gstep = resize!(C.g[step], C.ng[step])
        ##@show C.g, step
        matgen(x, dim, C.per, C.V)
        Gstep[C.ng[step]] = matgen(x, dim, C.per, C.V)
        C.g[step] = Gstep
        nH += 1
        H = Vector{T}(undef, nH)
        nH = 0
        @inbounds for i in step:dim
          for j in 1:C.ng[i]
            nH += 1
            H[nH] = C.g[i][j]
          end
        end
        # compute the new orbit of std_basis[step]
        orb = orbit(C.std_basis[step], 1, H, nH, C.V, C)
        C.orders[step] = length(orb)
        # delete the orbit from the candidates for x[step]
        setdiff!(candidates[step], orb)
        nC = length(candidates[step])
        #nC = delete(candidates[step], nC, orb, C.orders[step])
        # compute the new orbit of the vectors, which could be continued to an automorphism
        oc = orbit(bad, nbad, H, nH, C.V, C)
        # delete the orbit from the candidates
        setdiff!(candidates[step], oc)
        nC = length(candidates[step])
        #nC = delete(candidates[step], nC, oc, noc)
        #empty!(oc)
      end
    end
    if step == sta
      # test, whether on step flags.STAB some generators may be omitted
      tries = C.nsg[step]
      while tries <= C.ng[step]
      #for tries in C.nsg[step]:C.ng[step]
        nH = 0
        for j in 1:(tries-1)
          nH += 1
          H[nH] = C.g[step][j]
        end
        for j in (tries + 1):(C.ng[step]-1)
          nH += 1
          H[nH] = C.g[step][j]
        end
        for i in (step + 1):dim
          for j in 1:C.ng[i]
            nH += 1
            H[nH] = C.g[i][j]
            if false #_orbitlen(C.std_basis[step], C.orders[step], H, nH, C.V) == C.orders[step]
              # /* the generator g[step][tries] can be omitted */
              C.ng[step] -= 1
              for i in tries:(C.ng[step] - 1)
                C.g[step][i] = C.g[step][i + 1]
              end
              tries -= 1
            end
          end
        end
        tries += 1
      end
    end
    if step < dim && C.orders[step] > 1
     # /* calculate stabilizer elements fixing the basis-vectors
     #    C.std_basis[1]...fp.e[step] */
      stab(step, C)
    end
  end
  return _get_generators(C)
end

function _get_generators(C::ZLatAutoCtx{S, T, U}) where {S, T, U}
  # Extract generators

  gens = T[]

  orde = prod(ZZRingElem.(C.orders))

  for i in 1:dim(C)
    for j in (C.nsg[i] + 1):C.ng[i]
      push!(gens, C.g[i][j])
    end
  end

  return gens, orde
end

function aut(step, x, candidates, C, comb)
  dim = Hecke.dim(C)
  found = 0
  x[step + 1:length(x)] .= 0
  while candidates[step][1] != 0 && found == 0
    if step < dim
      x[step] = candidates[step][1]
      #/* check, whether x[1]...x[step] is a partial automorphism and compute the candidates for x[step + 1]
			if (cand(candidates[step + 1], step + 1, x, C, comb) == C.fp_diagonal[step + 1])
        found = aut(step + 1, x, candidates, C, comb)
      end
      if found == 1
        return found
      end
      orb = Int[x[step]]
      # delete the chosen vector from the list of candidates
      #delete(candidates[step], C.fp_diagonal[step], orb, 1)
      k = findfirst(isequal(x[step]), candidates[step])
      #setdiff!(candidates[step], orb)
      # This should be made faster to not always go to the end
      # Actually I should copy the delete function
      #@show candidates[step], k
      for i in (k + 1):length(candidates[step])
        candidates[step][i - 1] = candidates[step][i]
      end
      candidates[step][end] = 0
      #@show candidates[step]
    else
      x[dim] = candidates[dim][1]
      found = 1
    end
  end
  return found
end

function cand(candidates, I, x, C::ZLatAutoCtx{S, T, U}, comb) where {S, T, U}
  #@show candidates, I, x, C, comb
  DEP = 0 # this is bs
  dim = Hecke.dim(C)
  len = length(C.G) * DEP
  vec = Vector{S}(undef, dim)
  vec2 = Vector{S}(undef, dim)
  scpvec = Vector{Int}(undef, len)
  if I >= 2 && DEP > 0
    com = comb[I - 1]
    rank = com.rank
    n = com.list.n
    # xvec is the list of vector sums which are computed with respect to the partial basis in x
    xvec = Vector{Vector{ZZRingElem}}(undef, n + 1)
    for i in 1:(n + 1)
      xvec[i] = Vector{ZZRingElem}(undef, dim)
      for j in 1:dim
        xvec[i][j] = zero(ZZRingElem)
      end
    end
#/* xbase should be a basis for the lattice generated by the vectors in xvec,
#   it is obtained via the transformation matrix comb[I-1].trans */
    #xbase = zero_matrix(FlintZZ, rank, dim)
    #Fxbase = zero_matrix(FlintZZ, rank, dim)
  end
  # candidates is the list for the candidates
  #@show C.fp_diagonal[I], length(candidates)
  for i in 1:C.fp_diagonal[I]
    candidates[i] = 0
  end


  nr = 0
  fail = 0
  @inbounds for j in 1:length(C.V)
    if fail != 0
      break
    end
    Vvj = C.V[j]
    okp = 0
    okm = 0
    for k in 1:len
      scpvek[k] = 0
    end
    #@show C.V[j]
    for i in 1:length(C.G)
      _issym = C.is_symmetric[i]
      Cvi = C.v[i]
      #@show Cvi

    # vec is the vector of scalar products of V.v[j] with the first I base vectors
    #   x[1]...x[I]

      for k in 1:(I - 1)
        #@show x[k]
        xk = x[k]
        if xk > 0
          #vec[k] = _dot_product(Vvj, C.G[i], C.V[xk])
          vec[k] = _dot_product_with_row(Vvj, C.v[i], xk)
          #@assert _tutut == vec[k]
          if !_issym
            #vec2[k] = _dot_product(C.V[xk], C.G[i], Vvj)
            vec2[k] = _dot_product_with_row(C.V[xk], C.v[i], j)
            #@assert vec2[k] == _tutut2
          end
        else
          #vec[k] = -_dot_product(Vvj, C.G[i], C.V[-xk])
          vec[k] = -_dot_product_with_row(Vvj, C.v[i], -xk)
          #@assert _tutut == vec[k]

          if !_issym
            #vec2[k] = -_dot_product(C.V[-xk], C.G[i], Vvj)
            vec2[k] = -_dot_product_with_row(C.V[-xk], C.v[i], j)
            #@assert vec2[k] == _tutut2
          end
        end
      end

      good = true
      for k in 1:(I - 1)
        if vec[k] != C.G[i][C.per[I], C.per[k]] || (!_issym && vec2[k] != C.G[i][C.per[k], C.per[I]])
          good = false
          break
        end
      end

      #@show "pos", Vvj, good

      if good && C.V.lengths[j][i] == C.G[i][C.per[I], C.per[I]]
        # C.V[j] is a candidate for x[I] with respec to the form C.G[i]
        okp += 1
      end

      good = true
      for k in 1:(I - 1)
        if vec[k] != -C.G[i][C.per[I], C.per[k]] || (!_issym && vec2[k] != -C.G[i][C.per[k], C.per[I]])
          good = false
          break
        end
      end

      #@show "neg", Vvj, good

      if good && C.V.lengths[j][i] == C.G[i][C.per[I], C.per[I]]
        # C.V[j] is a candidate for x[I] with respec to the form C.G[i]
        #@show "here"
        okm += 1
      end

      if okp < i && okm < i
        break
      end

      #if I >= 2 && DEP > 0
      #  for k in I-1:-1:1
      #    if k <= I - 1 - DEP
      #      continue
      #    end
      #    scpvec[(i - 1) * DEP + I - k] = vec[k]
      #  end
      #end
    end

    #if I >= 2 && DEP > 0
    #  # check whether the scalar product combination scpvec is contained in the list comb[I - 1].list
    #  if all(iszero, scpvec)
    #    num = 0
    #  else
    #    num = find_vector(scpvec, com.list)
    #    sign = num > 0 ? 1 : -1
    #    num = sign * num
    #  end

    #  if num > n
    #    # scpvec is not found, hence x[1],...,x[I - 1] is not a partial automorphism
    #    fail = 1
    #  elseif num > 0
    #    # scpvec is found and the vector is added to the corresponding vector sum
    #    xnum = xvec[num]
    #    for k in 1:dim
    #      xnum[k] += sign * Vvj[k]
    #    end
    #  end
    #end

    if okp == length(C.G)
      # V.v[j] is a candidate for x[I]
      if nr < C.fp_diagonal[I]
        nr += 1
        candidates[nr] = j
      else
        # there are too many candidates
        fail = 1
      end
    end

    #@show nr

    #@show okm == length(C.G)

    if okm == length(C.G)
      # -V.v[j] is a candidate for x[I]
      if nr < C.fp_diagonal[I]
        nr += 1
        candidates[nr] = -j
      else
        # there are too many candidates
        fail = 1
      end
    end

    #@show nr
  end

  #@show fail

  if fail == 1
    nr = 0
  end

  if nr == C.fp_diagonal[I] && I >= 2 && DEP > 0
    # compute the basis of the lattice generated by the vectors in xvec via the transformation matrix comb[I - 1].trans
    for i in 1:rank
      comtri = com.trans[i]
      for j in 1:dim
        xbij = FlintZZ(0)
        for k in 1:(n+1)
          xbij += comtri[k] * xvec[k][j]
        end
        xbase[i, j] = xbij
      end
    end
  end

  if nr == C.fp_diagonal[I] && I >= 2 && DEP > 0
    for i in 1:length(C.G)
      if !(nr > 0)
        break
      end
      for j in 1:rank
        for k in 1:dim
          Fxbase[j, k] = _dot_product(xbase[j], C.A[i], k)
        end
      end
      for j in 1:rank
        if !(nr > 0)
          break
        end
        for k in 1:j
          if !(nr > 0)
            break
          end
          if _dot_product(xbase[j], Fxbase[k]) != com.F[i][j][k]
            # scalar product is wrong
            nr = 0
          end
        end
      end
    end
  end

  if nr == C.fp_diagonal[I] && I >= 2 && DEP > 0
    for i in 1:(n + 1)
      if !(nr > 0)
        break
      end
    end
    comcoi = com.coeff[i]
    for j in 1:dim
      vj = zero(ZZRingElem)
      for k in 1:rank
        vj += comcoi[k] * xbase[k][j]
      end
      if vj != xvec[i][j]
        # entry wrong
        nr = 0
        break
      end
    end
  end
  return nr
end

function orbit(pt, npt, G, nG, V, C::ZLatAutoCtx{S, T, U}) where {S, T, U}
  # Assumes that V is sorted
  orb = Vector{Int}(undef, npt)
  n = length(V)
  flag = zeros(Bool, 2*n + 1)
  #/* if flag[i + length(V)] is true, then the point i is already in the orbit */
  for i in 1:npt
    orb[i] = pt[i]
    flag[pt[i] + n + 1] = true
  end
  norb = npt
  cnd = 1
  while cnd <= norb
    for i in 1:nG
      im = _operate(orb[cnd], G[i], V, C.operate_tmp)
      if !flag[im + n + 1]
        # this is a new point
        norb += 1
        push!(orb, im)
        flag[im + n + 1] = true
      end
    end
    cnd += 1
  end
  return orb
end

function stab(I, C::ZLatAutoCtx{SS, T, U}) where {SS, T, U}
  V = C.V
#     	computes the orbit of fp.e[I] under the
#				generators in G->g[I]...G->g[n-1] and elements
#				stabilizing fp.e[I],
#				has some heuristic break conditions,
#				the generators in G->g[i] stabilize
#				fp.e[0]...fp.e[i-1] but not fp.e[i],
#				G->ng[i] is the number of generators in G->g[i],
#				the first G->nsg[i] of which are elements which
#				are obtained as stabilizer elements in
#				<G->g[0],...,G->g[i-1]>, G->ord[i] is the orbit
#				length of fp.e[i] under
#				<G->g[i],...,G->g[n-1]>	*****/
#group	*G;
#fpstruct fp;
#veclist	V;
#{
#	int	*orb, len, cnd, tmplen;
#	int	**w, *flag, ***H, ***Hj, **S, **tmp, ***Ggj;
#	int	i, j, k, l, dim, im, nH, nHj, fail;
#	int	Maxfail, Rest;
#
#/* some heuristic break conditions for the computation of stabilizer elements:
#   it would be too expensive to calculate all the stabilizer generators, which
#   are obtained from the orbit, since this is highly redundant,
#   on the other hand every new generator which enlarges the group is much
#   cheaper than one obtained from the backtrack,
#   after Maxfail subsequent stabilizer elements, that do not enlarge the group,
#   Rest more elements are calculated even if they leave the group unchanged,
#   since it turned out that this is often useful in the following steps,
#   increasing the parameters will possibly decrease the number of generators
#   for the group, but will increase the running time,
#   there is no magic behind this heuristic, tuning might be appropriate */
  dim = Hecke.dim(C)
  n = length(V)
  Rest = 0
  for i in I:dim
    if C.fp_diagonal[i] > 1 && C.orders[i] < C.fp_diagonal[i]
      Rest += 1
    end
  end

  Maxfail = Rest

  for i in 1:dim
    if C.fp_diagonal[i] > 1
      Maxfail += 1
    end
  end

  nH = 0
  for i in I:dim
    nH += C.ng[i]
  end

  Hj = Vector{T}(undef, nH + 1)
  H = Vector{T}(undef, nH)

#/* H are the generators of the group in which the stabilizer is computed */

  k = 0
  for i in I:dim
    for j in 1:C.ng[i]
      k += 1
      H[k] = C.g[i][j]
    end
  end

  w = Vector{Vector{Int}}(undef, 2 * n + 1)
  orb = zeros(Int, 2 * n)
  flag = zeros(Bool, 2 * n + 1)


#/* in w[V.n+i] an element is stored that maps fp.e[I] on v[i] */
#/* orb contains the orbit of fp.e[I] */
#/* if flag[i + V.n] = 1, then the point i is already in the orbit */
#/* S is a matrix to hold a stabilizer element temporarily */

  #@show I
  orb[1] = C.std_basis[I]
  flag[orb[1] + n + 1] = true
  #@show orb[1] + n + 1
  w[orb[1] + n + 1] = Int[ C.std_basis[i] for i in 1:dim]
  cnd = 1
  len = 1
  fail = 0

  while cnd <= len && fail < Maxfail + Rest
    for i in 1:nH
      if fail > Maxfail + Rest
        break
      end

      if fail >= Maxfail
      #/* there have already been Maxfail successive failures, now a random generator
      #   is applied to a random point of the orbit to get Rest more stabilizer
      #   elements */
        cnd = rand(1:len)
        i = rand(1:nH)
      end
      #@show orb, flag
      #@show cnd
      im = _operate(orb[cnd], H[i], V, C.operate_tmp)
      #@show im
      #@show w
      if !flag[im + n + 1]
#/* a new element is found, appended to the orbit and an element mapping
#   fp.e[I] to im is stored in w[im+V.n] */
        len += 1
        #@show orb, len
        orb[len] = im
        flag[im + n + 1] = true
        #@show w[orb[cnd] + n + 1]
        #@show H[i]
        #@show Int[_operate(w[orb[cnd] + n + 1][j], H[i], V) for j in 1:dim]
        w[im + n + 1] = Int[_operate(w[orb[cnd] + n + 1][j], H[i], V, C.operate_tmp) for j in 1:dim]
      else
#/* the image was already in the orbit */
        j = I
        while j <= dim
          if _operate(w[orb[cnd] + n + 1][j], H[i], V, C.operate_tmp) == w[im + n + 1][j]
            break
          end
          j += 1
        end
#/* j is the first index where the images of the old and the new element
#   mapping e[I] on im differ */
        if j <= dim && (C.orders[j] < C.fp_diagonal[j]  || fail >= Maxfail)
#/* new stabilizer element S = w[orb[cnd]+V.n] * H[i] * (w[im+V.n])^-1 */
          S = stabil(w[orb[cnd] + n + 1], w[im + n + 1], C.per, H[i], V, C)
          #@show S
          Hj[1] = S
          nHj = 1
          for k in j:dim
            for l in 1:C.ng[k]
              nHj += 1
              Hj[nHj] = C.g[k][l]
            end
          end
          tmplen = _orbitlen(C.std_basis[j], C.fp_diagonal[j], Hj, nHj, V, C)
          if tmplen > C.orders[j] || fail >= Maxfail
#/* the new stabilizer element S either enlarges the orbit of e[j]
#   or it is one of the additional elements after MAXFAIL failures */
            C.orders[j] = tmplen
            C.ng[j] = C.ng[j] + 1
            C.nsg[j] = C.nsg[j] + 1
            #@show C.g[j]
            #@show C.nsg[j]
            insert!(C.g[j], C.nsg[j], S)
#/* the new generator is inserted as stabilizer element nr. nsg[j]-1 */
            nH += 1
            push!(H, S)
            if fail < Maxfail
              fail = 0
            else
              fail += 1
            end
            resize!(Hj, nH + 1)
#/* the new generator is appended to H */
#/* the number of failures is reset to 0 */
          else
#/* the new stabilizer element S does not enlarge the orbit of e[j] */
            fail += 1
          end
        else
          if j <= dim && fail < Maxfail || (j == dim && fail >= Maxfail)
            fail += 1
          end
        end
      #/* if S is the identity and fail < Maxfail, nothing is done */
      end
    end
    if fail < Maxfail
      cnd += 1
    end
  end
end

#void stabil(S, x1, x2, per, G, V)	/*****	x1 corresponds to an element X1
#						mapping some vector e on p1,
#						x2 to an element X2 mapping e on
#						p2 and G is a generator mapping
#						p1 on p2, then S = X1*G*X2^-1
#						stabilizes e	*****/
function stabil(x1, x2, per, G, V, C)
  dim = length(x1)
  XG = zero_matrix(FlintZZ, dim, dim)
  X2 = zero_matrix(FlintZZ, dim, dim)
  x = Vector{Int}(undef, dim)
  for i in 1:dim
    x[i] = _operate(x1[i], G, V, C.operate_tmp) # ZZRingElem case
  end

  XG = matgen(x, dim, per, V)
  X2 = matgen(x2, dim, per, V)

  b, S = can_solve_with_solution(X2, XG, side = :left)
  return S
end

function stabil(x1, x2, per, G::Matrix{Int}, V, C)
  #@show x1, x2
  dim = length(x1)
  x = Vector{Int}(undef, dim)
  for i in 1:dim
    x[i] = _operate(x1[i], G, V, C.operate_tmp)
  end

  XG = matgen(x, dim, per, V)
  X2 = matgen(x2, dim, per, V)

  @hassert :Lattice 1 begin XGG = deepcopy(XG); X22 = deepcopy(X2); true end
  SS = zeros(Int, dim, dim)
  _psolve(SS, X2, XG, dim, C.prime)
  @hassert :Lattice 1 SS * X22 == XGG

  return SS
end

ZZMatrix(M::Matrix{Int}) = matrix(FlintZZ, M)

zero_matrix(::Type{Int}, r, c) = zeros(Int, r, c)

base_ring(::Vector{Int}) = Int

function _one(::Type{Matrix{Int}}, n::Int)
  z = zeros(Int, n, n)
  for i in 1:n
    z[i, i] = 1
  end
  return z
end

_one(::Type{ZZMatrix}, n::Int) = identity_matrix(FlintZZ, n)

_zero(::Type{Matrix{Int}}, n::Int, m::Int) = zeros(Int, n, m)

_zero(::Type{ZZMatrix}, n::Int, m::Int) = zero_matrix(FlintZZ, n, m)

function matgen(x, dim, per, v)
#/*****	generates the matrix X which has as row
#					per[i] the vector nr. x[i] from the
#					list v	*****
  X = zero_matrix(base_ring(v[1]), dim, dim)
  #@show x
  for i in 1:dim
    xi = x[i]
    if x[i] > 0
      for j in 1:dim
        X[per[i], j] = v[xi][j]
      end
    else
      for j in 1:dim
        X[per[i], j] = -v[-xi][j]
      end
    end
  end
  return X
end

# Isomorphism computation

function _try_iso_setup_small(Gi, Go)
  Ci = ZLatAutoCtx(Gi)
  fl, Cismall = try_init_small(Ci, false)
  if fl
    Co = ZLatAutoCtx(Go)
    fl2, Cosmall = try_init_small(Co, true, ZZRingElem(Cismall.max))
    if fl2
      return true, Cismall, Cosmall
    end
  end

  return false, Cismall, Cismall
end

function _iso_setup(Gi, Go)
  Ci = ZLatAutoCtx(Gi)
  Co = ZLatAutoCtx(Go)
  init(Ci, true)
  init(Co, false, Ci.max)
  return Ci, Co
end

function isometry(Ci::ZLatAutoCtx{SS, T, U}, Co::ZLatAutoCtx{SS, T, U}) where {SS, T, U}
  d = dim(Co)
  C = Vector{Vector{Int}}(undef, d)
  # I could actually also test the minimum
  if length(Ci.V) != length(Co.V)
    return false, _zero(T, 0, 0)
  end
  for i in 1:d
    C[i] = zeros(Int, Ci.fp_diagonal[i])
  end
  x = zeros(Int, d)
  # compute the candidates for x[0]
  H = Vector{T}(undef, sum(length(gg) for gg in Co.g))
  k = 1
  for i in 1:length(Co.g)
    for j in 1:length(Co.g[i])
      H[k] = Co.g[i][j]
      k += 1
    end
  end
  isocand(C[1], 1, x, Ci, Co)

  found = iso(1, x, C, Ci, Co, H)
  if found
    ISO = matgen(x, d, Ci.per, Co.V)
    for k in 1:length(Ci.G)
      ISO * Co.G[k] * ISO' == Ci.G[k]
    end
    return true, ISO
  else
    return false, _zero(T, 0, 0)
  end
end

function iso(step, x, C, Ci, Co, G)
  d = dim(Ci)
  found = false
  @vprint :Lattice "Testing $(length(C[step])) many candidates\n"
  while !isempty(C[step]) && C[step][1] != 0 && !found
    @vprint :Lattice "Doing step $step\n"
    if step < d
      # choose the image of the base vector nr. step
      x[step] = C[step][1]
        # check whether x[1]..x[step]
      nbc = isocand(C[step + 1], step + 1, x, Ci, Co)
      if nbc == Ci.fp_diagonal[step + 1]
        # go deeper in the recursion
        Maxfail = 0
        # determine the heuristic value of Maxfail for the break condition in isostab
        for i in 1:step
          if Ci.fp_diagonal[i] > 1
            Maxfail += 1
          end
        end
        for i in (step + 1):d
          if Ci.fp_diagonal[i] > 1
            Maxfail += 2
          end
        end
        H = isostab(x[step], G, Co, Maxfail)
        found = iso(step + 1, x, C, Ci, Co, H)
      end
      if found
        return found
      end
      # This is horrible
      # this is remove orb from C[step], and then adding 0's at the end to make
      # it again as big as in the beginning. This can be done more efficiently.
      nc = length(C[step])
      orb = orbit(x[step], 1, G, length(G), Co.V, Co)
      no = length(orb)
      setdiff!(C[step], orb)
      newnc = length(C[step])
      resize!(C[step], nc)
      for i in newnc + 1:nc
        C[step][i] = 0
      end
    else
      x[d] = C[d][1]
      found = true
    end
  end
  return found
end

function isostab(pt, G, C::ZLatAutoCtx{S, T, U}, Maxfail) where {S, T, U}
# computes the orbit of V.v[pt]
# under the generators
#	G[0],...,G[nG-1] and elements
#	stabilizing V.v[pt], which are
#	stored in H, returns the number
#	of generators in H
# a heuristic break condition for the computation of stabilizer elements:
# it would be too expensive to calculate all the stabilizer generators, which
# are obtained from the orbit, since this is highly redundant,
# on the other hand every new generator which enlarges the group reduces the
# number of orbits and hence the number of candidates to be tested,
# after Maxfail subsequent stabilizer elements, that do not enlarge the group,
# the procedure stops,
# increasing Maxfail will possibly decrease the number of tests,
# but will increase the running time of the stabilizer computation
# there is no magic behind the heuristic, tuning might be appropriate */
#
  nG = length(G)
  d = dim(C)
#/* H are the generators of the stabilizer of C.V[pt] */
  V = C.V
  H = Vector{T}(undef, 1)
  nH = 0
  n = length(C.V)
  w = Vector{T}(undef, 2 * n + 2)
  orb = zeros(Int, 2 * n)
  orblen = 1
  flag = zeros(Bool, 2*n + 1)
#/* if flag[i + n + 1] = 1, then the point i is already in the orbit */
  orb[1] = pt
  flag[orb[1] + n + 1] = 1
#/* w[pt+V.n] is the Identity */
  w[orb[1] + n + 1] = _one(T, d)
  cnd = 1
  len = 1
  fail = 0
#/* fail is the number of successive failures */
  #A = zero_matrix(FlintZZ, d, d)
  #B = zero_matrix(FlintZZ, d, d)
  while (cnd <= len && fail < Maxfail)
    for i in 1:nG
      if fail >= Maxfail
        break
      end
      #@show G, i
      #@show orb[cnd]
      im = _operate(orb[cnd], G[i], V, C.operate_tmp)
      #@show im
      if !flag[im + n  + 1]
#/* a new element is found, appended to the orbit and an element mapping
        len += 1
        orb[len] = im
        flag[im + n + 1] = true
        w[im + n + 1] = w[orb[cnd] + n + 1] * G[i]
#   V.v[pt] to im is stored in w[im+V.n] */
      else
#/* the image was already in the orbit */
        B = w[orb[cnd] + n + 1] * G[i]
        #@show B
        #@show w[im + n + 1]
#/* check, whether the old and the new element mapping pt on im differ */
        if B != w[im + n + 1]
#/* new stabilizer element H[nH] = w[orb[cnd]+V.n] * G[i] * (w[im+V.n])^-1 */
          H[nH + 1] = w[orb[cnd] + n + 1] * G[i] * inv(w[im + n + 1])
          #	psolve((*H)[nH], A, B, dim, V.prime);
          rpt = rand(1:(n + 1))
          templen = _orbitlen(rpt, 2*n, H, nH + 1, V)
          while templen < orblen
#/* the orbit of this vector is shorter than a previous one, hence choose a new
#   random vector */
            rpt = rand(1:(n + 1))
            tmplen = _orbitlen(rpt, 2*n, H, nH + 1, V)
          end
          if tmplen > orblen
#/* the new stabilizer element H[nH] enlarges the group generated by H */
            orblen = tmplen
            nH += 1
            resize!(H, nH)
            fail = 0
          else
            fail += 1
          end
        end
        # if H[nH]is the identity, nothing is done
      end
    end
    cnd += 1
  end
  resize!(H, nH)
  return H
end

function isocand(CI, I, x, Ci::ZLatAutoCtx{S, T, U}, Co) where {S, T, U}
  d = dim(Ci)
  n = length(Ci.V)
  @assert n == length(Co.V)
  # Do something with bacher polynomials ...
  vec = Vector{S}(undef, d)
  vec2 = Vector{S}(undef, d)
  for i in 1:Ci.fp_diagonal[I]
    CI[i] = 0
  end
  nr = 0
  fail = false
  for j in 1:n
    if fail
      break
    end
    Vvj = Co.V[j]
    okp = 0
    okm = 0
    # do something with scpvec
    for i in 1:length(Co.G)
      # GiI = Ci.G[i][Ci.per[I]] this is the Ci.per[I]-th row of Ci.G[i]
      Fvi = Co.v[i]
      # vec is the vector of scalar products of Co.v[j] with the first I base vectors
      # x[1]...x[I-1]
      for k in 1:(I - 1)
        xk = x[k]
        # TODO: Check for symmetry as in the cand function
        # TODO: Use dot_product_with_row
        if xk > 0
          vec[k] = _dot_product(Vvj, Co.G[i], Co.V[xk])
          vec2[k] = _dot_product(Co.V[xk], Co.G[i], Vvj)
          #vec[k] = _dot_product(Vvj, Fvi, -xk)
        else
          vec[k] = -_dot_product(Vvj, Co.G[i], Co.V[-xk])
          vec2[k] = -_dot_product(Co.V[-xk], Co.G[i], Vvj)
          #vec[k] = -(Vvj * Co.G[i] * Co.V[-xk]')[1, 1]
          #vec2[k] = -(Co.V[-xk] * Co.G[i] * Vvj')[1, 1]
          #vec[k] = -_dot_product(Vvj, Fvi, -xk)
        end
      end
      good = true
      for k in 1:(I - 1)
        if vec[k] != Ci.G[i][Ci.per[I], Ci.per[k]] || vec2[k] != Ci.G[i][Ci.per[k], Ci.per[I]]
          good = false
          break
        end
      end
      if good && Co.V.lengths[j][i] == Ci.G[i][Ci.per[I], Ci.per[I]]
        okp += 1
      end
      good = true
      for k in 1:(I - 1)
        if vec[k] != -Ci.G[i][Ci.per[I], Ci.per[k]] || vec2[k] != -Ci.G[i][Ci.per[k], Ci.per[I]]

          good = false
          break
        end
      end
      if good && Co.V.lengths[j][i] == Ci.G[i][Ci.per[I], Ci.per[I]]
        okm += 1
      end
      # do something with scpvec
    end
    # do something with scpvec and DEP
    if okp == length(Ci.G)
      if nr < Ci.fp_diagonal[I]
        nr += 1
        CI[nr] = j
      else
        fail = true
      end
    end
    if okm == length(Ci.G)
      if nr < Ci.fp_diagonal[I]
        nr += 1
        CI[nr] = -j
      else
        fail = true
      end
    end
  end
  if fail
    nr = 0
  end

  #if nr == Ci.fp_diagonal[I] # DEP
  # update the blabla
  return nr
end

function assert_auto(C, order)
  G, o = _get_generators(C)
  if o != order
    error("Order $o. Expected $order")
  end

  for g in G
    for U in C.G
      if g * U * g' != U
        error("Not an isometry.\nElement:\n $g\nGram matrix:\n$U")
      end
    end
  end
  return true
end

################################################################################
#
#  Rewrite
#
################################################################################

################################################################################
#
#  Computational kernels
#
################################################################################

function _dot_product_with_column!(t::ZZRingElem, v::ZZMatrix, A::ZZMatrix, k::Int, tmp::ZZRingElem)
  mul!(t, v[1, 1], A[1, k])
  for i in 2:ncols(v)
    mul!(tmp, v[1, i], A[i, k])
    addeq!(t, tmp)
  end
  return t
end

function _dot_product_with_column(v::ZZMatrix, A::ZZMatrix, k::Int, tmp::ZZRingElem = zero(FlintZZ))
  t = zero(FlintZZ)
  t = _dot_product_with_column!(t, v, A, k, tmp)
  return t
end

function _dot_product_with_row!(t::ZZRingElem, v::ZZMatrix, A::ZZMatrix, k::Int, tmp::ZZRingElem)
  mul!(t, v[1, 1], A[k, 1])
  for i in 2:ncols(v)
    mul!(tmp, v[1, i], A[k, i])
    addeq!(t, tmp)
  end
  return t
end

function _dot_product_with_row(v::ZZMatrix, A::ZZMatrix, k::Int, tmp::ZZRingElem = zero(FlintZZ))
  t = zero(FlintZZ)
  t = _dot_product_with_row!(t, v, A, k, tmp)
  return t
end

function _dot_product_with_column!(t::Int, v::Vector{Int}, A::Matrix{Int}, k::Int, tmp::Int)
  @inbounds t = v[1] * A[1, k]
  @inbounds for i in 2:length(v)
    t = t + v[i] * A[i, k]
  end
  return t
end

function _dot_product_with_column(v::Vector{Int}, A::Matrix{Int}, k::Int, tmp::Int = zero(Int))
  t = zero(Int)
  t = _dot_product_with_column!(t, v, A, k, tmp)
  #@show size(A)
  #@assert (reshape(v, (1, length(v))) * A[1:size(A, 1), k:k])[1, 1] == t
  return t
end

function _dot_product_with_row!(t::Int, v::Vector{Int}, A::Matrix{Int}, k::Int, tmp::Int)
  @inbounds t = v[1] * A[k, 1]
  @inbounds for i in 2:length(v)
    t = t + v[i] * A[k, i]
  end
  return t
end

function _dot_product_with_row(v::Vector{Int}, A::Matrix{Int}, k::Int, tmp::Int = zero(Int))
  t = zero(Int)
  return _dot_product_with_row!(t, v, A, k, tmp)
end

# Generic vector times matrix

_vec_times_matrix!(w, v, A) = mul!(w, v, A)

_vec_times_matrix(v::Vector{Int}, A) = _vec_times_matrix!(zeros(Int, size(A, 2)), v , A)

function _vec_times_matrix!(w::Vector{Int}, v::Vector{Int}, A::Matrix{Int})
  c = size(A, 2)
  r = size(A, 1)
  for i in 1:c
    @inbounds w[i] = v[1] * A[1, i]
    for j in 2:r
      @inbounds w[i] += v[j] * A[j, i]
    end
  end
  #@assert reshape(w, 1, length(w)) == reshape(v, 1, length(v)) * A
  return w
end

function _dot_product(v::Vector{Int}, M::Matrix{Int}, w::Vector{Int})
  z = M * w
  zz = dot(v, z)
  #@assert zz == (reshape(v, 1, length(v)) * M * w)[1, 1]
  return zz
end

function _norm(v::Vector{Int}, M::Matrix{Int}, tmp::Vector{Int} = Vector{Int}(undef, length(v)))
  LinearAlgebra.mul!(tmp, M, v)
  return dot(v, tmp)
end

function _norm(v::ZZMatrix, M::ZZMatrix, tmp::ZZMatrix = zero_matrix(FlintZZ, 1, ncols(v)))
  mul!(tmp, v, M)
  return (v * transpose(tmp))[1, 1]
end

function _dot_product(v::ZZMatrix, M::ZZMatrix, w::ZZMatrix)
  return (v * M * transpose(w))[1, 1]
end

#

function _pgauss(r, A, B, n, p)
  ainv = invmod(A[r, r], p)
  for j in (r + 1):n
    if A[r, j] % p != 0
      f = A[r, j] * ainv % p
      for i in (r+1):n
        A[i, j] = (A[i, j] - f * A[i, r]) % p
      end
      for i in 1:n
        B[i, j] = (B[i, j] - f * B[i, r]) % p
      end
      A[r, j] = 0
    end
  end
end

function _psolve(X, A, B, n, p)
  for i in 1:(n - 1)
    j = i
    while A[i, j] % p == 0 && j <= n
      j += 1
    end
    if j == n + 1
      error("Not possible")
    end

    if j != i
      for k in i:n
        A[k, i], A[k, j] = A[k, j], A[k, i]
      end
      for k in 1:n
        B[k, i], B[k, j] = B[k, j], B[k, i]
      end
    end
    _pgauss(i, A, B, n, p)
  end
  for i in 1:n
    for j in n:-1:1
      sum = 0
      for k in n:-1:(j+1)
        sum = (sum + X[i, k] * A[k, j]) % p
      end
      ainv = invmod(A[j, j], p)
      X[i, j] = ((B[i, j] - sum) * ainv) % p
      c = 2 * X[i, j]
      if 2*c > p
        X[i, j] -= p
      elseif c <= -p
        X[i, j] += p
      end
    end
  end
end

###########################################
#
#  isless for ZZMatrix (vectors)
#
##########################################

function _isless(x::ZZMatrix, y::ZZMatrix)
  i = 0
  c = ncols(x)
  while i < c
    i += 1
    if x[i] == y[i]
      continue
    else
      return x[i] < y[i]
    end
  end
  return false
end

# should do this more C style
max_nbits(v::ZZMatrix) = maximum([nbits(v[1, i]) for i in 1:ncols(v)])

# Some tests that I need to add:
#
# G = matrix(FlintZZ, 8, 8, [4, -2, 0, 0, 0, 0, 0, 1, -2, 2, -1, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2])
#
# C = Hecke.ZLatAutoCtx([G]); Hecke.compute_short_vectors(C);
#
# Hecke.fingerprint(C)
# reduce(hcat, [C.fp[:, i] for i in 1:8][C.per]) == [240 240 2160 240 240 240 240 240; 0 56 126 126 126 126 126 126; 0 0 27 27 72 72 72 72; 0 0 0 10 40 16 40 40; 0 0 0 0 8 8 24 24; 0 0 0 0 0 4 6 12; 0 0 0 0 0 0 3 6; 0 0 0 0 0 0 0 2]
