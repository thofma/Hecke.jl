export short_vectors, short_vectors_iterator, shortest_vectors, kissing_number

@doc Markdown.doc"""
    short_vectors(L::ZLat, [lb = 0], ub, [elem_type = fmpz]; check::Bool = true)
                                       -> Vector{Tuple{Vector{elem_type}, fmpq}}

Returns all tuples `(v, n)` such that `n = v G v^t` satisfies `lb <= n <= ub`, where `G` is the
Gram matrix of `L` and `v` is non-zero.

Note that the vectors are computed up to sign (so only one of `v` and `-v`
appears).

It is assumed and checked that `L` is positive definite.

See also [`short_vectors_iterator`](@ref) for an iterator version.
"""
short_vectors

@doc Markdown.doc"""
    short_vectors_iterator(L::ZLat, [lb = 0], ub,
                           [elem_type = fmpz]; check::Bool = true)
                                    -> Tuple{Vector{elem_type}, fmpq} (iterator)

Returns an iterator for all tuples `(v, n)` such that `n = v G v^t` satisfies
`lb <= n <= ub`, where `G` is the Gram matrix of `L` and `v` is non-zero.

Note that the vectors are computed up to sign (so only one of `v` and `-v`
appears).

It is assumed and checked that `L` is positive definite.

See also [`short_vectors`](@ref).
"""
short_vectors_iterator

function short_vectors(L::ZLat, ub, elem_type::Type{S} = fmpz; check::Bool = true) where {S}
  if check
    @req ub >= 0 "the upper bound must be non-negative"
    @req is_definite(L) && (rank(L)==0 || gram_matrix(L)[1, 1]>0) "Zlattice must be positive definite"
  end
  if rank(L) == 0
    return Tuple{Vector{S}, fmpq}[]
  end
  _G = gram_matrix(L)
  return _short_vectors_gram(Vector, _G, ub, S)
end

function short_vectors_iterator(L::ZLat, ub, elem_type::Type{S} = fmpz; check::Bool = true) where {S}
  if check
    @req ub >= 0 "the upper bound must be non-negative"
    @req is_definite(L) && (rank(L)==0 || gram_matrix(L)[1, 1]>0) "Zlattice must be positive definite"
  end
  _G = gram_matrix(L)
  return _short_vectors_gram(LatEnumCtx, _G, ub, S)
end

function short_vectors(L::ZLat, lb, ub, elem_type::Type{S} = fmpz; check=true) where {S}
  if check
    @req lb >= 0 "the lower bound must be non-negative"
    @req ub >= 0 "the upper bound must be non-negative"
    @req is_definite(L) && (rank(L)==0 || gram_matrix(L)[1, 1]>0) "Zlattice must be positive definite"
  end
  if rank(L) == 0
    return Tuple{Vector{S}, fmpq}[]
  end
  _G = gram_matrix(L)
  return _short_vectors_gram(Vector, _G, lb, ub, S)
end

function short_vectors_iterator(L::ZLat, lb, ub, elem_type::Type{S} = fmpz; check=true) where {S}
  if check
    @req lb >= 0 "the lower bound must be non-negative"
    @req ub >= 0 "the upper bound must be non-negative"
    @req is_definite(L) && (rank(L) == 0 || gram_matrix(L)[1, 1]>0) "Zlattice must be positive definite"
  end
  _G = gram_matrix(L)
  return _short_vectors_gram(LatEnumCtx, _G, lb, ub, S)
end

################################################################################
#
#  Shortest vectors
#
################################################################################

@doc Markdown.doc"""
    shortest_vectors(L::ZLat, [elem_type = fmpz]; check::Bool = true)
                                               -> fmpq, Vector{elem_type}, fmpq}

Returns the list of shortest non-zero vectors. Note that the vectors are
computed up to sign (so only one of `v` and `-v` appears).

It is assumed and checked that `L` is positive definite.

See also [`minimum`](@ref).
"""
shortest_vectors(L::ZLat, ::fmpz)

function shortest_vectors(L::ZLat, elem_type::Type{S} = fmpz; check::Bool = true) where {S}
  if check
    @req rank(L) > 0 "Lattice must have positive rank"
    @req is_definite(L) && (rank(L) == 0 || gram_matrix(L)[1,1]>0) "Zlattice must be positive definite"
  end
  _G = gram_matrix(L)
  min, V = _shortest_vectors_gram(_G)
  L.minimum = min
  return V
end

################################################################################
#
#  Minimum
#
################################################################################

@doc Markdown.doc"""
    minimum(L::ZLat)

Return the minimum squared length among the non-zero vectors in `L`.
"""
function minimum(L::ZLat)
  @req rank(L) > 0 "Lattice must have positive rank"
  if !isdefined(L, :minimum)
    shortest_vectors(L)
  end

  return L.minimum
end

################################################################################
#
#  Kissing number
#
################################################################################

@doc Markdown.doc"""
    kissing_number(L::ZLat)

Return the Kissing number of the sphere packing defined by `L`.

This is the number of non-overlapping spheres touching any
other given sphere.
"""
function kissing_number(L::ZLat)
  @req rank(L) > 0 "Lattice must have positive rank"
  return 2 * length(shortest_vectors(L))
end

