@doc raw"""
    short_vectors(L::ZZLat, [lb = 0], ub, [elem_type = ZZRingElem]; check::Bool = true)
                                       -> Vector{Tuple{Vector{elem_type}, QQFieldElem}}

Return all tuples `(v, n)` such that $n = |v G v^t|$ satisfies `lb <= n <= ub`,
where `G` is the Gram matrix of `L` and `v` is non-zero.

Note that the vectors are computed up to sign (so only one of `v` and `-v`
appears).

It is assumed and checked that `L` is definite.

See also [`short_vectors_iterator`](@ref) for an iterator version.
"""
short_vectors

@doc raw"""
    short_vectors_iterator(L::ZZLat, [lb = 0], ub,
                           [elem_type = ZZRingElem]; check::Bool = true)
                                    -> Tuple{Vector{elem_type}, QQFieldElem} (iterator)

Return an iterator for all tuples `(v, n)` such that $n = |v G v^t|$ satisfies
`lb <= n <= ub`, where `G` is the Gram matrix of `L` and `v` is non-zero.

Note that the vectors are computed up to sign (so only one of `v` and `-v`
appears).

It is assumed and checked that `L` is definite.

See also [`short_vectors`](@ref).
"""
short_vectors_iterator

function short_vectors(L::ZZLat, ub, elem_type::Type{S} = ZZRingElem; check::Bool = true) where {S}
  if check
    @req ub >= 0 "The upper bound must be non-negative"
    @req is_definite(L) "Lattice must be definite"
  end
  if rank(L) == 0
    return Tuple{Vector{S}, QQFieldElem}[]
  end
  _G = gram_matrix(L)
  if _G[1, 1] < 0
    _G = -_G
  end
  return _short_vectors_gram(Vector, _G, ub, S)
end

function short_vectors_iterator(L::ZZLat, ub, elem_type::Type{S} = ZZRingElem; check::Bool = true) where {S}
  if check
    @req ub >= 0 "The upper bound must be non-negative"
    @req is_definite(L) "Lattice must be definite"
  end
  _G = gram_matrix(L)
  if rank(L) != 0 && _G[1, 1] < 0
    _G = -_G
  end
  return _short_vectors_gram(LatEnumCtx, _G, ub, S)
end

function short_vectors(L::ZZLat, lb, ub, elem_type::Type{S} = ZZRingElem; check=true) where {S}
  if check
    @req lb >= 0 "The lower bound must be non-negative"
    @req ub >= 0 "The upper bound must be non-negative"
    @req is_definite(L) "Lattice must be definite"
  end
  if rank(L) == 0
    return Tuple{Vector{S}, QQFieldElem}[]
  end
  _G = gram_matrix(L)
  if _G[1, 1] < 0
    _G = -_G
  end
  return _short_vectors_gram(Vector, _G, lb, ub, S)
end

function short_vectors_iterator(L::ZZLat, lb, ub, elem_type::Type{S} = ZZRingElem; check=true) where {S}
  if check
    @req lb >= 0 "The lower bound must be non-negative"
    @req ub >= 0 "The upper bound must be non-negative"
    @req is_definite(L) "Lattice must be definite"
  end
  _G = gram_matrix(L)
  if rank(L) != 0 && _G[1, 1] < 0
    _G = -_G
  end
  return _short_vectors_gram(LatEnumCtx, _G, lb, ub, S)
end

################################################################################
#
#  Shortest vectors
#
################################################################################

@doc raw"""
    shortest_vectors(L::ZZLat, [elem_type = ZZRingElem]; check::Bool = true)
                                               -> QQFieldElem, Vector{elem_type}, QQFieldElem}

Return the list of shortest non-zero vectors in absolute value. Note that the
vectors are computed up to sign (so only one of `v` and `-v` appears).

It is assumed and checked that `L` is definite.

See also [`minimum`](@ref).
"""
shortest_vectors(L::ZZLat, ::ZZRingElem)

function shortest_vectors(L::ZZLat, elem_type::Type{S} = ZZRingElem; check::Bool = true) where {S}
  if check
    @req rank(L) > 0 "Lattice must have positive rank"
    @req is_definite(L) "Lattice must be definite"
  end
  _G = gram_matrix(L)
  if _G[1, 1] < 0
    _G = -_G
  end
  min, V = _shortest_vectors_gram(_G)
  L.minimum = min
  return V
end

################################################################################
#
#  Minimum
#
################################################################################

@doc raw"""
    minimum(L::ZZLat) -> QQFieldElem

Return the minimum absolute squared length among the non-zero vectors in `L`.
"""
function minimum(L::ZZLat)
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

@doc raw"""
    kissing_number(L::ZZLat) -> Int

Return the Kissing number of the sphere packing defined by `L`.

This is the number of non-overlapping spheres touching any
other given sphere.
"""
function kissing_number(L::ZZLat)
  @req rank(L) > 0 "Lattice must have positive rank"
  return 2 * length(shortest_vectors(L))
end

###############################################################################
#
# Short vectors affine
#
###############################################################################

function _vec(M::MatElem)
  r = elem_type(base_ring(M))[]
  sizehint!(r, nrows(M) * ncols(M))
  for j=1:ncols(M)
    for i=1:nrows(M)
      push!(r, M[i, j])
    end
  end
  return r
end

@doc raw"""
    enumerate_quadratic_triple -> Vector{Tuple{Vector{Int}, QQFieldElem}}

Return $\{x \in \mathbb Z^n : x Q x^T + 2xb^T + c <=0\}$.

#Input:
- `Q`: positive definite matrix
- `b`: row vector
- `c`: rational number
"""
function enumerate_quadratic_triple(Q, b, c; algorithm=:short_vectors, equal=false)
  if algorithm == :short_vectors
    L, p, dist = Hecke._convert_type(Q, b, QQ(c))
    #@vprint :K3Auto 1 ambient_space(L), basis_matrix(L), p, dist
    if equal
      cv = Hecke.close_vectors(L, _vec(p), dist, dist, check=false)
    else
      cv = Hecke.close_vectors(L, _vec(p), dist, check=false)
    end
  end
  return cv
end

@doc raw"""
    short_vectors_affine(S::ZZLat, v::MatrixElem, alpha, d)
    short_vectors_affine(gram::MatrixElem, v::MatrixElem, alpha, d)

Return the vectors of squared length `d` in the given affine hyperplane.

```math
\{x \in S : x^2=d, x.v=\alpha \}.
```
The matrix version takes `S` with standard basis and the given gram matrix.

# Arguments
- `v`: row vector with $v^2 > 0$
- `S`: a hyperbolic `Z`-lattice

The output is given in the ambient representation.

The implementation is based on Algorithm 2.2 in [Shi15](@cite)
"""
function short_vectors_affine(S::ZZLat, v::MatrixElem, alpha, d)
  alpha = QQ(alpha)
  gram = gram_matrix(S)
  tmp = v*gram_matrix(ambient_space(S))*transpose(basis_matrix(S))
  v_S = solve(gram_matrix(S),tmp; side = :left)
  sol = short_vectors_affine(gram, v_S, alpha, d)
  B = basis_matrix(S)
  return [s*B for s in sol]
end

function short_vectors_affine(gram::MatrixElem, v::MatrixElem, alpha, d)
  # find a solution <x,v> = alpha with x in L if it exists
  w = gram*transpose(v)
  tmp = Hecke.FakeFmpqMat(w)
  wn = numerator(tmp)
  wd = denominator(tmp)
  b, x = can_solve_with_solution(transpose(wn), matrix(ZZ, 1, 1, [alpha*wd]); side = :right)
  if !b
    return QQMatrix[]
  end
  K = kernel(wn; side = :left)
  # (x + y*K)*gram*(x + y*K) = x gram x + 2xGKy + y K G K y

  # now I want to formulate this as a cvp
  # (x +y K) gram (x+yK) ==d
  # (x
  GK = gram*transpose(K)
  Q = K * GK
  b = transpose(x) * GK
  c = (transpose(x)*gram*x)[1,1] - d
  # solve the quadratic triple
  Q = change_base_ring(QQ, Q)
  b = change_base_ring(QQ, transpose(b))
  if Q[1, 1] < 0
    map_entries!(-, Q, Q)
  end
  cv = enumerate_quadratic_triple(Q, b, QQ(c), equal=true)
  xt = transpose(x)
  cv = [xt+matrix(ZZ,1,nrows(Q),u[1])*K for u in cv]
  return cv #[u for u in cv if (u*gram*transpose(u))[1,1]==d]
end
