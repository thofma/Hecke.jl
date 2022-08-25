export close_vectors

@doc Markdown.doc"""
    close_vectors(L:ZLat, v:Vector, upperbound;
                  equal::Bool=false, check::Bool = false, filter)
                                            -> Vector{Tuple{Vector{Int}}, fmpq}

Return all tuples `(x, d)` where `x` is an element of `L` such that `d = b(v -
x, v - x) <= c`.

If `equal` is `true`, then only elements with `b(v - x, v - x) = c` are
returned.

If `filter` is not `nothing`, then only those `x` with `filter(x)` evaluating
to `true` are returned.

By default, it will be checked whether `L` is positive definite. This can be
disabled setting `check = false`.

Both input and output are with respect to the basis matrix of `L`.

```jldoctest
julia> L = Zlattice(matrix(QQ, 2, 2, [1, 0, 0, 2]));

julia> close_vectors(L, [1, 1], 1)
3-element Vector{Tuple{Vector{Int64}, fmpq}}:
 ([2, 1], 1)
 ([0, 1], 1)
 ([1, 1], 0)

julia> close_vectors(L, [1, 1], 1, equal = true, filter = x -> all(>=(1), x))
1-element Vector{Tuple{Vector{Int64}, fmpq}}:
 ([2, 1], 1)
```
"""
function close_vectors(L::ZLat, v::Vector, upperbound; kw...)
  return _close_vectors(L, QQ.(v), QQ(upperbound); kw...)
end

function _close_vectors(L::ZLat, v::Vector{fmpq}, upperbound::fmpq;
                                equal::Bool=false, sorting::Bool=false,
                                check=true, filter = nothing) where T <: RingElem
  epsilon = QQ(1//10)   # some number > 0, not sure how it influences performance
  d = length(v)
  G1 = gram_matrix(rational_span(L))
  if check
    @req is_definite(L) == true && G1[1, 1] > 0 "Zlattice must be positive definite"
    @req rank(L) == d "Zlattice must have the same rank as the length of the vector in the second argument."
  end
  # Construct
  # G = [ G1 | 0 ]
  #     [  0 | e ]
  # where e = upperbound//3 + epsilon
  G = zero_matrix(QQ, d + 1, d + 1)
  _copy_matrix_into_matrix(G, 1, 1, G1)
  e = upperbound//3 + epsilon
  G[d + 1, d + 1] = e
  # Construct
  # B = [ 1  | 0 ]
  #     [ -v | 1 ]
  # since we will be working in the rational_span(L) + Qw with w^2 = e
  B = identity_matrix(QQ, d + 1)
  GC.@preserve B begin
    for i in 1:d
      m = ccall((:fmpq_mat_entry, libflint),
                Ptr{fmpq}, (Ref{fmpq_mat}, Int, Int), B, d, i - 1)
      ccall((:fmpq_set, libflint), Cvoid, (Ptr{fmpq}, Ref{fmpq}), m, v[i])
      ccall((:fmpq_neg, libflint), Cvoid, (Ptr{fmpq}, Ptr{fmpq}), m, m)
    end
  end

  N = Zlattice(B, gram = G, check = false)

  delta = QQ(4//3)*upperbound + epsilon
  sv = short_vectors(N, delta)
  cv = Vector{Tuple{Vector{Int}, fmpq}}()
  V = rational_span(L)
  for a in sv
    _a, _l = a
    al = _a[end]
    if iszero(al)
      continue
    end
    @assert al == 1 || al == -1

    if al == -1
      x = Int[-_a[i] for i in 1:d]
    else
      x = Int[_a[i] for i in 1:d]
    end

    if filter !== nothing && !(filter(x)::Bool)
      continue
    end

    dist = _l - e

    @hassert :Lattice 3 inner_product(V, fmpq.(x) - v, fmpq.(x) - v) == dist

    if !equal || dist == upperbound
      push!(cv, (x, dist))
    end
  end

  if sorting
    sort!(cv, by = x -> x[1])
  end
  return cv
end

function sub!(z::Vector{fmpq}, x::Vector{fmpq}, y::Vector{fmpz})
  for i in 1:length(z)
    sub!(z[i], x[i], y[i])
  end
  return z
end

################################################################################
#
#  Legacy interface
#
################################################################################

function closest_vectors(L::ZLat, v::MatrixElem{T} , upperbound::T; kw...) where T <: RingElem
  _v = T[v[i] for i in 1:nrows(v)]
  return first.(close_vectors(L, _v, upperbound; kw...))
end
@doc Markdown.doc"""
    _convert_type(G::MatrixElem{T}, K::MatrixElem{T}, d::T) -> Tuple{ZLat, MatrixElem{T}, T}
Where T is a concrete type, e.g. fmpz, fmpq, etc.
Converts a quadratic triple QT = [Q, K, d] to the input values required for closest vector problem (CVP).
"""
function _convert_type(G::MatrixElem{T}, K::MatrixElem{T}, d::T) where T <: RingElem
  if G[1,1] > 0
    Q = G
  else
    Q = -G
  end
  vector = -inv(Q) * K
  upperbound = (-transpose(K) * inv(Q) * -K)[1] - d
  Lattice = Zlattice(gram = Q)
  return Lattice, vector, upperbound
end

@doc Markdown.doc"""
    _convert_type(L::ZLat, v::MatrixElem{T}, c::T) -> Tuple{fmpq_mat, fmpq_mat, fmpq}

Where T is a concrete type, e.g. fmpz, fmpq, etc.
Converts the input values from closest vector enumeration (CVE) to the corresponding quadratic triple QT = [Q, K, d].
"""
function _convert_type(L::ZLat, v::MatrixElem{T}, c::T) where T <: RingElem
  V = ambient_space(L)
  Q = gram_matrix(V)
  K = -Q*v
  v = vec([i for i in v])
  d = inner_product(V,v,v)-c
  return Q, K, d
end


@doc Markdown.doc"""
    closest_vectors(Q::MatrixElem{T}, L::MatrixElem{T}, c::T; equal::Bool=false, sorting::Bool=false)
                                                    -> Vector{Vector{fmpz}}


Return all the integer vectors `x` of length n such that the inhomogeneous
quadratic function `q_{QT}(x) := xQx + 2xL + c <= 0` corresponding to an n variabled
quadratic triple. If the optional argument ``equal = true``, it return
all vectors `x` such that `q_{QT}(x) = 0`. By default ``equal = false``.
If the argument ``sorting = true``, then we get a a list of sorted vectors.
The Default value for ``sorting`` is set to ``false``.
"""
function closest_vectors(G::MatrixElem{T}, L::MatrixElem{T}, c::T; equal::Bool=false, sorting::Bool=false) where T <: RingElem
  Lattice, vector, upperbound = _convert_type(G, L, c)
  return first.(_close_vectors(Lattice, fmpq[vector[i, 1] for i in 1:nrows(vector)],
                               QQ(upperbound); equal = equal, sorting = sorting))
end
