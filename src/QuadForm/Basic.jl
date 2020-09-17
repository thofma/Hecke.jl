export ambient_space, rank, gram_matrix, inner_product, involution,
       islocal_square, isequivalent, isrationally_equivalent, quadratic_space,
       hermitian_space, diagonal, invariants, hasse_invariant, witt_invariant, orthogonal_basis, fixed_field

################################################################################
#
#  Basic invariants
#
################################################################################

@doc Markdown.doc"""
    isquadratic(V::AbsSpace) -> Bool

Returns whether $V$ is quadratic.
"""
isquadratic(V::AbsSpace)

@doc Markdown.doc"""
    ishermitian(V::AbsSpace) -> Bool

Returns whether $V$ is hermitian.
"""
ishermitian(V::AbsSpace)

@doc Markdown.doc"""
    rank(V::AbsSpace) -> Int

Return the rank of the space `V`.
"""
rank(L::AbsSpace) = nrows(L.gram)

@doc Markdown.doc"""
    dim(V::AbsSpace) -> Int

Return the dimension of the space `V`.
"""
dim(V::AbsSpace) = rank(V)

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace) -> MatElem

Return the Gram matrix of `V`.
"""
gram_matrix(V::AbsSpace) = V.gram

# Once we have quaternion spaces the following makes more sense

@doc Markdown.doc"""
    base_ring(V::AbsSpace) -> NumField

Return the base field of `V`.
"""
base_ring(V::AbsSpace) = _base_algebra(V)

@doc Markdown.doc"""
    fixed_field(V::AbsSpace) -> NumField

Return the fixed field of `V`.
"""
fixed_field(::AbsSpace)

@doc Markdown.doc"""
    involution(V::AbsSpace) -> NumField

Return the involution of `V`.
"""
involution(V::AbsSpace)

# Maybe cache this

@doc Markdown.doc"""
    isregular(V::AbsSpace) -> Bool

Return whether `V` is regular, that is, if the Gram matrix
has full rank.
"""
function isregular(V::AbsSpace)
  G = gram_matrix(V)
  return rank(G) == nrows(G)
end

################################################################################
#
#  Determinant and discriminant
#
################################################################################

function det(V::AbsSpace)
  d = det(gram_matrix(V))
  return fixed_field(V)(d)
end

@doc Markdown.doc"""
    det(V::AbsSpace) -> FieldElem

Returns the determinant of the space `V` as an element of the fixed field.
"""
det(::AbsSpace)

@doc Markdown.doc"""
    discriminant(V::AbsSpace) -> FieldElem

Returns the discriminant of the space `V` as an element of the fixed field.
"""
function discriminant(V::AbsSpace)
  d = det(V)
  n = mod(rank(V), 4)
  if n == 0 || n == 1
    return d
  else
    return -d
  end
end

function _discriminant(G)
  d = det(G)
  n = nrows(G)
  if mod(n, 4) == 0 || mod(n, 4) == 1
    return d
  else
    return -d
  end
end

################################################################################
#
#  Computing inner products
#
################################################################################

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace, M::MatElem) -> MatElem

Returns the gram matrix of the rows of `M`.
"""
function gram_matrix(V::AbsSpace{T}, M::MatElem{S}) where {S, T}
  if S === elem_type(T)
    return M * gram_matrix(V) * transpose(_map(M, involution(V)))
  else
    Mc = change_base_ring(base_ring(V), M)
    return Mc * gram_matrix(V) * transpose(_map(Mc, involution(V)))
  end
end

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace, S::Vector{Vector}) -> MatElem

Returns the gram matrix of the sequence `S`.
"""
function gram_matrix(V::AbsSpace{T}, S::Vector{Vector{U}}) where {T, U}
  m = zero_matrix(base_ring(V), length(S), rank(V))
  for i in 1:length(S)
    if length(S[i]) != rank(V)
      throw(error("Vectors must be of length $(rank(V))"))
    end
    for j in 1:rank(V)
      m[i, j] = S[i][j]
    end
  end
  return gram_matrix(V, m)
end

@doc Markdown.doc"""
    inner_product(V::AbsSpace, v::Vector, w::Vector) -> FieldElem

Returns the inner product of `v` and `w` with respect to `V`.
"""
inner_product(V::AbsSpace, v::Vector, w::Vector)

################################################################################
#
#  Diagonalization
#
################################################################################

@doc Markdown.doc"""
    orthogonal_basis(V::AbsSpace) -> MatElem

Returns a matrix `M`, such that the rows of `M` form an orthgonal basis of `V`.
"""
function orthogonal_basis(V::AbsSpace)
  _, B = _gram_schmidt(gram_matrix(V), involution(V))
  return B
end

@doc Markdown.doc"""
    diagonal(V::AbsSpace) -> Vector{FieldElem}

Returns a vector of elements $a_1,\dotsc,a_n$ such that `V` is isometric to
the diagonal space $\langle a_1,\dotsc,a_n \rangle$.

The elements will be contained in the fixed field of `V`.
"""
diagonal(V::AbsSpace)

################################################################################
#
#  Gram-Schmidt
#
################################################################################

# Clean this up
function _gram_schmidt(M::MatElem, a, nondeg = true)
  F = deepcopy(M)
  K = base_ring(F)
  n = nrows(F)
  S = identity_matrix(K, n)
  okk = isdiagonal(F)
  if !okk
    for i in 1:n
      if iszero(F[i,i])
        T = identity_matrix(K, n)
        ok = 0
        for j in (i + 1):n
          if !iszero(F[j, j])
            ok = j
            break
          end
        end
        #ok = findfirst(j -> !iszero(F[j, j]), (i + 1):n)
        if ok != 0 # ok !== nothing
          #j = ok + i # findfirst gives the index
          j = ok
          T[i,i] = 0
          T[j,j] = 0
          T[i,j] = 1
          T[j,i] = 1
        else
          ok = 0
          for j in (i + 1):n
            if !iszero(F[i, j])
              ok = j
              break
            end
          end
          if ok == 0
            if nondeg
              error("Matrix is not of full rank")
            end
          else
            j = ok
            T[i, j] = 1 // (2 * F[j, i])
          end
        end
        S = T * S
        F = T * F * transpose(_map(T, a))
      end
      T = identity_matrix(K, n)
      for j in (i + 1):n
        T[j, i] = divexact(-F[j, i], F[i, i])
      end
      F = T * F * transpose(_map(T, a))
      S = T * S
    end
    @assert isdiagonal(F)
  end
  return F, S
end

################################################################################
#
#  Local equivalence
#
################################################################################

@doc Markdown.doc"""
    isequivalent(L::AbsSpace, M::AbsSpace, p::Union{InfPlc, NfOrdIdl}) -> Bool

Returns whether `L` and `M` are equivalent over the completion at `p`.
"""
isequivalent(L::AbsSpace, M::AbsSpace, p)

################################################################################
#
#  Definitness
#
################################################################################

# Returns 0 if V is not definite
# Returns an element a != 0 such that a * canonical_basis of V has
# positive Gram matrix
function _isdefinite(V::AbsSpace)
  K = fixed_field(V)
  R = maximal_order(K)
  if !istotally_real(K) || (ishermitian(V) && !istotally_complex(K))
    return zero(K)
  end
  D = diagonal(V)
  signs_to_consider = Tuple{InfPlc, Int}[]
  for v in real_places(K)
    S = Int[sign(d, v) for d in D]
    if length(unique(S)) != 1
      return zero(K)
    else
      push!(signs_to_consider, (v, S[1]))
    end
  end
  if length(signs_to_consider) == 1
    return K(signs_to_consider[1][2])
  else
    return element_with_signs(K, signs_to_consider)
  end
end

function ispositive_definite(V::AbsSpace)
  E = base_ring(V)
  if isquadratic(V)
    K = E
  else
    K = base_field(E)
  end
  if !istotally_real(K)
    return false
  end
  D = diagonal(V)
  for d in D
    if !istotally_positive(d)
      return false
    end
  end
  return true
end

function isnegative_definite(V::AbsSpace)
  E = base_ring(V)
  if isquadratic(V)
    K = E
  else
    K = base_field(E)
  end

  if !istotally_real(K)
    return false
  end
  D = diagonal(V)
  for d in D
    if !istotally_positive(-d)
      return false
    end
  end
  return true
end

function isdefinite(V::AbsSpace)
  return ispositive_definite(V) || isnegative_definite(V)
end

################################################################################
#
#  Isotropic
#
################################################################################

isisotropic(V::AbsSpace, p::InfPlc) = _isisotropic(V, p)

function _isisotropic(D::Vector{fmpq}, p::PosInf)
  n = length(D)
  if n <= 1
    return false
  end
  E = parent(D[1])
  d = reduce(*, D, init = one(E))
  if d == 0
    return true
  elseif n <= 1
    return false
  else
    return length(unique!(fmpq[sign(d) for d in D])) == 2
  end
end

function _isisotropic(D::Vector, p::InfPlc)
  n = length(D)
  if n <= 1
    return false
  end
  E = parent(D[1])
  d = reduce(*, D, init = one(E))
  if d == 0
    return true
  elseif n <= 1
    return false
  elseif iscomplex(p)
    return true
  else
    return length(unique!(Int[sign(d, p) for d in D])) == 2
  end
end

function _isisotropic(V::AbsSpace, p::InfPlc)
  n = rank(V)
  d = det(V)
  E = base_ring(V)
  if d == 0
    return true
  elseif n <= 1
    return false
  elseif iscomplex(p)
    return true
  else
    D = diagonal(V)
    return length(unique!(Int[sign(d, p) for d in D])) == 2
  end
end

################################################################################
#
#  Helper functions (sort them later)
#
################################################################################

function image(f::NfRelToNfRelMor{T, T}, I::NfRelOrdIdl{T, S}) where {T, S}
  #f has to be an automorphism!!!!
  O = order(I)
  @assert ismaximal(O) # Otherwise the order might change
  K = nf(O)

  B = absolute_basis(I)

  if I.is_prime == 1
    lp = prime_decomposition(O, minimum(I))
    for (Q, e) in lp
      if I.splitting_type[2] == e
        if all(b -> f(b) in Q, B)
          return Q
        end
      end
    end
  end

  pb = pseudo_basis(I)
  pm = basis_pmatrix(I)

  m = zero(matrix(pm))

  c = coefficient_ideals(pm)

  for i in 1:length(pb)
    cc = coordinates(O(f(pb[i][1])))
    for j in 1:length(cc)
      m[i, j] = cc[j]
    end
  end

  J = ideal(O, pseudo_matrix(m, c))

  if isdefined(I, :minimum)
    J.minimum = I.minimum
  end

  J.has_norm = I.has_norm

  if isdefined(I, :norm)
    J.norm = I.norm
  end

  if isdefined(I, :is_prime)
    J.is_prime = I.is_prime
  end

  if isdefined(I, :splitting_type)
    J.splitting_type = I.splitting_type
  end

  return J
end

function image(f::NfRelToNfRelMor{T, T}, I::NfRelOrdFracIdl{T, S}) where {T, S}
  #S has to be an automorphism!!!!
  O = order(I)
  @assert ismaximal(O) # Otherwise the order might change
  K = nf(O)

  pb = pseudo_basis(I)

  z = sum(b * (f(a) * O) for (a, b) in pb)
  return z
end

# An element is locally a square if and only if the quadratic defect is 0, that is
# the valuation is inf.
# (see O'Meara, Introduction to quadratic forms, 3rd edition, p. 160)
function islocal_square(a, p)
  return quadratic_defect(a, p) isa PosInf
end

function _map(a::AbstractAlgebra.MatrixElem, f)
  z = similar(a)
  for i in 1:nrows(a)
    for j in 1:ncols(a)
      z[i, j] = f(a[i, j])
    end
  end
  return z
end

# I think I need a can_change_base_ring version

function element_with_signs(K, D::Dict{InfPlc, Int})
  return _element_with_signs(K, D)
end

function _element_with_signs(K, D)
  OK = maximal_order(K)
  G, mG = infinite_primes_map(OK, real_places(K), 1*OK)
  r = real_places(K)
  z = id(G)
  for (v, s) in D
    for i in 1:length(r)
      if s == 1
        ss = 0
      else
        ss = 1
      end

      if v == r[i]
        z = z + ss * G[i]
      end
    end
  end
  zz = elem_in_nf(mG(z))::elem_type(K)
  @assert all(u -> sign(zz, u[1]) == u[2], D)
  return zz
end

function element_with_signs(K, P::Vector{InfPlc}, S::Vector{Int})
  return _element_with_signs(K, zip(P, S))
end

function element_with_signs(K, A::Vector{Tuple{InfPlc, Int}})
  return _element_with_signs(K, A)
end

function prime_ideals_up_to(O::NfRelOrd, n::Union{Int, fmpz})
  p = 2
  z = ideal_type(O)[]
  while p <= n
    lp = prime_decomposition(base_ring(O), p)
    for q in lp
      if norm(q[1]) > n
        continue
      else
        lq = prime_decomposition(O, q[1])
        for Q in lq
          if absolute_norm(Q[1]) <= n
            push!(z, Q[1])
          end
        end
      end
    end
    p = next_prime(p)
  end
  return sort!(z, by = a -> absolute_norm(a))
end

################################################################################
#
#  Restriction of scalars
#
################################################################################

function restrict_scalars(V::AbsSpace, K::Field = FlintQQ, alpha = one(base_ring(V)))
  E = base_ring(V)
  n = rank(V)
  d = absolute_degree(E)
  B = absolute_basis(E)
  v = elem_type(E)[zero(E) for i in 1:n]
  w = elem_type(E)[zero(E) for i in 1:n]
  G = zero_matrix(FlintQQ, d * n, d * n)
  r = 1
  c = 1
  indices = Vector{Tuple{Int, Int}}(undef, n * d)
  for i in 1:n
    for bi in 1:length(B)
      v[i] = B[bi]
      c = 1
      for j in 1:n
        for bj in 1:length(B)
          w[j] = B[bj]
          G[r, c] = trace(alpha * inner_product(V, v, w), FlintQQ)
          w[j] = zero(E)
          c = c + 1
        end
      end
      v[i] = zero(E)
      indices[r] = (i, bi)
      r = r + 1
    end
  end

  VabstoV = function(v)
    @assert length(v) == d * n
    z = Vector{elem_type(E)}(undef, n)
    for i in 1:n
      z[i] = zero(E)
    end
    for k in 1:(d * n)
      (i, j) = indices[k]
      z[i] = z[i] + v[k] * B[j]
    end
    return z
  end

  VtoVabs = function(w)
    z = Vector{fmpq}(undef, d * n)
    k = 1
    for i in 1:n
      y = w[i]
      for j in 1:d
        z[k] = absolute_coeff(y, j - 1)
        k = k + 1
      end
    end
    return z
  end

  return quadratic_space(FlintQQ, G), VabstoV, VtoVabs
end

# Careful, starts at 0!
function absolute_coeff(z::nf_elem, i)
  return coeff(z, i)
end

function absolute_coeff(z::NumFieldElem, i)
  d = absolute_degree(base_field(parent(z)))
  rowindex = fld(i, d)
  colindex = (i % d)
  return absolute_coeff(coeff(z, rowindex), colindex)
end

function absolute_basis(K::NumField)
  k = base_field(K)
  kabs = absolute_basis(k)
  res = elem_type(K)[]
  for b in basis(K)
    for bb in kabs
      push!(res, bb * b)
    end
  end
  return res
end

function absolute_basis(K::NumField{fmpq})
  return basis(K)
end

#

istotally_real(::FlintRationalField) = true

istotally_positive(x::fmpq) = x > 0

# This function is really slow...
function denominator(M::fmpq_mat)
  d = one(FlintZZ)
  for i in 1:nrows(M)
    for j in 1:ncols(M)
      d = lcm!(d, d, denominator(M[i, j]))
    end
  end
  return d
end

function _weak_approximation_coprime(IP, S, M)
  R = order(M)
  A, _exp, _log = infinite_primes_map(R, IP, M)

  t = (1 + _exp(A([ S[j] == 1 ? 0 : -1 for j in 1:length(IP)])))
  @assert all(i -> sign(t, IP[i]) == S[i], 1:length(IP))
  return t
end

