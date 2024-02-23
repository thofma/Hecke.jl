@doc raw"""
    close_vectors(L:ZZLat, v:Vector, [lb,], ub; check::Bool = false)
                                            -> Vector{Tuple{Vector{Int}}, QQFieldElem}

Return all tuples `(x, d)` where `x` is an element of `L` such that `d = b(v -
x, v - x) <= ub`. If `lb` is provided, then also `lb <= d`.

If `filter` is not `nothing`, then only those `x` with `filter(x)` evaluating
to `true` are returned.

By default, it will be checked whether `L` is positive definite. This can be
disabled setting `check = false`.

Both input and output are with respect to the basis matrix of `L`.

# Examples

```jldoctest
julia> L = integer_lattice(matrix(QQ, 2, 2, [1, 0, 0, 2]));

julia> close_vectors(L, [1, 1], 1)
3-element Vector{Tuple{Vector{ZZRingElem}, QQFieldElem}}:
 ([2, 1], 1)
 ([0, 1], 1)
 ([1, 1], 0)

julia> close_vectors(L, [1, 1], 1, 1)
2-element Vector{Tuple{Vector{ZZRingElem}, QQFieldElem}}:
 ([2, 1], 1)
 ([0, 1], 1)
```
"""
close_vectors(L::ZZLat, v::Vector, arg...; kw...)

function close_vectors(L::ZZLat, v::Vector, upperbound, elem_type::Type{S} = ZZRingElem; kw...) where {S}
  @req upperbound >= 0 "The upper bound must be non-negative"
  return _close_vectors(L, QQ.(v), nothing, QQ(upperbound), elem_type; kw...)
end

function close_vectors_iterator(L::ZZLat, v::Vector, upperbound, elem_type::Type{S} = ZZRingElem; kw...) where {S}
  @req upperbound >= 0 "The upper bound must be non-negative"
  return _close_vectors_iterator(L, QQ.(v), nothing, QQ(upperbound), elem_type; kw...)
end

function close_vectors(L::ZZLat, v::Vector, lowerbound, upperbound, elem_type::Type{S} = ZZRingElem; kw...) where {S}
  @req upperbound >= 0 "The upper bound must be non-negative"
  @req lowerbound >= 0 "The lower bound must be non-negative"
  return _close_vectors(L, QQ.(v), QQ(lowerbound), QQ(upperbound), elem_type; kw...)
end

function close_vectors_iterator(L::ZZLat, v::Vector, lowerbound, upperbound, elem_type::Type{S} = ZZRingElem; kw...) where {S}
  @req upperbound >= 0 "The upper bound must be non-negative"
  @req lowerbound >= 0 "The lower bound must be non-negative"
  return _close_vectors_iterator(L, QQ.(v), QQ(lowerbound), QQ(upperbound), elem_type; kw...)
end

function _close_vectors(L::ZZLat, v::Vector{QQFieldElem}, lowerbound, upperbound::QQFieldElem, elem_type::Type{S} = ZZRingElem;
                                sorting::Bool=false,
                                check=true)  where {S}
  epsilon = QQ(1//10)   # some number > 0, not sure how it influences performance
  d = length(v)
  V = rational_span(L)
  G1 = gram_matrix(V)
  if check
    @req is_definite(L) == true && G1[1, 1] > 0 "integer_lattice must be positive definite"
    @req rank(L) == d "integer_lattice must have the same rank as the length of the vector in the second argument."
  end

  epsilon = QQ(1//10)   # some number > 0, not sure how it influences performance

  # Define
  # G = [ G1 | 0 ]
  #     [  0 | e ]
  # where e = upperbound//3 + epsilon
  # Define
  # B = [ 1  | 0 ]
  #     [ -v | 1 ]
  # Since we will be working in the rational_span(L) + Qw with w^2 = e.
  # Construct new gram matrix with respect to B:
  # [ G1   | (-v*G1)'    ]
  # [-v*G1 |  v*G1*v'+ e ]

  e = upperbound//3 + epsilon
  gram = zero_matrix(QQ, d + 1, d + 1)
  _copy_matrix_into_matrix(gram, 1, 1, G1)
  gram[d+1, d+1] = e + inner_product(V,v,v)
  vv = -v*G1
  for i in 1:d
    gram[d+1,i] = vv[i]
    gram[i,d+1] = vv[i]
  end

  delta = QQ(4//3)*upperbound + epsilon # this is upperbound + e
  if lowerbound === nothing
    sv = _short_vectors_gram(Vector, gram, delta, elem_type)
  else
    sv = _short_vectors_gram(Vector, gram, (lowerbound + e), delta, elem_type)
  end
  cv = Vector{Tuple{Vector{elem_type}, QQFieldElem}}()
  for a in sv
    _a, _l = a
    al = _a[end]
    if iszero(al)
      continue
    end
    @assert al == 1 || al == -1

    if al == -1
      x = elem_type[-_a[i] for i in 1:d]
    else
      x = elem_type[_a[i] for i in 1:d]
    end

    dist = _l - e

    @hassert :Lattice 3 inner_product(V, QQFieldElem.(x) - v, QQFieldElem.(x) - v) == dist

    push!(cv, (x, dist))
  end

  if sorting
    sort!(cv, by = x -> x[1])
  end
  return cv
end

function _close_vectors_iterator(L::ZZLat, v::Vector{QQFieldElem}, lowerbound, upperbound::QQFieldElem, elem_type::Type{S} = ZZRingElem;
                                sorting::Bool=false,
                                check=true, filter = nothing) where S
  d = length(v)
  V = rational_span(L)
  G1 = gram_matrix(V)
  if check
    @req is_definite(L) == true && G1[1, 1] > 0 "integer_lattice must be positive definite"
    @req rank(L) == d "integer_lattice must have the same rank as the length of the vector in the second argument."
  end

  epsilon = QQ(1//10)   # some number > 0, not sure how it influences performance

  # Define
  # G = [ G1 | 0 ]
  #     [  0 | e ]
  # where e = upperbound//3 + epsilon
  # Define
  # B = [ 1  | 0 ]
  #     [ -v | 1 ]
  # Since we will be working in the rational_span(L) + Qw with w^2 = e.
  # Construct new gram matrix with respect to B:
  # [ G1   | (-v*G1)'    ]
  # [-v*G1 |  v*G1*v'+ e ]

  e = upperbound//3 + epsilon
  gram = zero_matrix(QQ, d + 1, d + 1)
  _copy_matrix_into_matrix(gram, 1, 1, G1)
  gram[d+1, d+1] = e + inner_product(V,v,v)
  vv = -v*G1
  for i in 1:d
    gram[d+1,i] = vv[i]
    gram[i,d+1] = vv[i]
  end

  delta = QQ(4//3)*upperbound + epsilon # this is upperbound + e

  sv = _short_vectors_gram(LatEnumCtx, gram, lowerbound === nothing ? 0 : (lowerbound + e), delta, elem_type)

  C = LatCloseEnumCtx{typeof(sv), elem_type}(sv, e, d)

  return C
end

Base.IteratorSize(::Type{<:LatCloseEnumCtx}) = Base.SizeUnknown()

Base.eltype(::Type{LatCloseEnumCtx{X, elem_type}}) where {X, elem_type} = Tuple{Vector{elem_type}, QQFieldElem}

function Base.iterate(C::LatCloseEnumCtx{X, elem_type}, start = nothing) where {X, elem_type}
  e = C.e
  d = C.d

  if start === nothing
    it = iterate(C.short_vector_iterator)
  else
    it = iterate(C.short_vector_iterator, start)
  end

  @label main

  if it === nothing
    return nothing
  end

  st = it[2]::Int
  _a, _l = it[1]::Tuple{Vector{elem_type}, QQFieldElem}
  al = _a[end]
  if iszero(al)
    it = iterate(C.short_vector_iterator, st)
    @goto main
  end

  @assert al == 1 || al == -1

  if al == -1
    x = elem_type[-_a[i] for i in 1:d]
  else
    x = elem_type[_a[i] for i in 1:d]
  end
  dist = _l - e

  return (x, dist), st
end


################################################################################
#
#  Legacy interface
#
################################################################################

function closest_vectors(L::ZZLat, v::MatrixElem{T} , upperbound::T; kw...) where T <: RingElem
  _v = T[v[i] for i in 1:nrows(v)]
  return first.(close_vectors(L, _v, upperbound; kw...))
end
@doc raw"""
    _convert_type(G::MatrixElem{T}, K::MatrixElem{T}, d::T) -> Tuple{ZZLat, MatrixElem{T}, T}
Where T is a concrete type, e.g. ZZRingElem, QQFieldElem, etc.
Converts a quadratic triple QT = [Q, K, d] to the input values required for closest vector problem (CVP).
"""
function _convert_type(G::MatrixElem{T}, K::MatrixElem{T}, d::T) where T <: RingElem
  @req all(G[i,i]>0 for i in 1:nrows(G)) "G must be positive definite"  #cheap sanity check
  Q = G
  vector = -solve(Q, K; side = :right) #-inv(Q) * K
  upperbound = (transpose(vector) * Q * vector)[1,1] - d
  Lattice = integer_lattice(gram = Q, check=false)
  return Lattice, vector, upperbound
end

@doc raw"""
    _convert_type(L::ZZLat, v::MatrixElem{T}, c::T) -> Tuple{QQMatrix, QQMatrix, QQFieldElem}

Where T is a concrete type, e.g. ZZRingElem, QQFieldElem, etc.
Converts the input values from closest vector enumeration (CVE) to the corresponding quadratic triple QT = [Q, K, d].
"""
function _convert_type(L::ZZLat, v::MatrixElem{T}, c::T) where T <: RingElem
  V = ambient_space(L)
  Q = gram_matrix(V)
  @req all(Q[i,i]>0 for i in 1:nrows(Q)) "L must be definite"
  K = -Q*v
  v = vec([i for i in v])
  d = inner_product(V,v,v)-c
  return Q, K, d
end

@doc raw"""
    closest_vectors(Q::MatrixElem{T}, L::MatrixElem{T},
                    c::T; equal::Bool=false, sorting::Bool=false)
                                                    -> Vector{Vector{ZZRingElem}}


Return all the integer vectors `x` of length n such that the inhomogeneous
quadratic function `q_{QT}(x) := xQx + 2xL + c <= 0` corresponding to an n
variabled quadratic triple. If the optional argument ``equal = true``, it
return all vectors `x` such that `q_{QT}(x) = 0`. By default ``equal = false``.
If the argument ``sorting = true``, then we get a a list of sorted vectors.
The Default value for ``sorting`` is set to ``false``.
"""
function closest_vectors(G::MatrixElem{T}, L::MatrixElem{T}, c::T;
                   equal::Bool=false, sorting::Bool=false) where T <: RingElem
  Lattice, vector, upperbound = _convert_type(G, L, c)
  if equal
    cv = _close_vectors(Lattice, QQFieldElem[vector[i, 1] for i in 1:nrows(vector)],
                                     QQ(upperbound),
                                     QQ(upperbound); sorting = sorting)
    return map(x -> ZZRingElem.(x), first.(cv))
  else
    cv = _close_vectors(Lattice, QQFieldElem[vector[i, 1] for i in 1:nrows(vector)],
                                     nothing,
                                     QQ(upperbound); sorting = sorting)
    return map(x -> ZZRingElem.(x), first.(cv))
  end
end
