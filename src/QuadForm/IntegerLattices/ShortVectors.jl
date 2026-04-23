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
    @req is_definite(L) "Lattice must be definite"
  end
  if iszero(rank(L))
    return Vector{S}[]
  end
  _G = gram_matrix(L)
  if _G[1, 1] < 0
    _G = -_G
  end
  min, V = _shortest_vectors_gram(FinckePohstInt, _G)
  L.minimum = min
  if S === Int
    return V
  else
    return [S.(i) for i in V]
  end
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

###############################################################################
#
#  Density
#
###############################################################################

@doc raw"""
    center_density(L::ZZLat) -> RealFieldElem

Return the center density of the definite lattice ``L``.

For a definite lattice ``L`` of rank ``n``, absolute determinant ``d`` and
minimum ``m`` (in absolute value), we define the **center density** of ``L``
to be the real number defined by:

```math
\delta := \frac{(\sqrt{m}/2)^n}{\sqrt{d}}
```

# Examples
```jldoctest
julia> L = root_lattice(:E, 6);

julia> center_density(L)
[0.0721687836487032205 +/- 9.72e-20]
```
"""
@attr RealFieldElem function center_density(L::ZZLat)
  @req is_definite(L) "Only implemented for definite lattices"
  RR = real_field()
  mu = RR(minimum(L))
  d = RR(abs(det(L)))
  rho = sqrt(mu)/2
  return rho^(rank(L))/sqrt(d)
end

@doc raw"""
    density(L::ZZLat) -> RealFieldElem

Return the density of the definite lattice ``L``.

For a definite lattice ``L`` of rank ``n`` and minimum ``m``, the density of
``L`` is the proportion of the real space ``L\otimes \mathbb{R}`` covered by
non-overlapping balls of radius ``m`` centered in points of ``L``. It can
be computed as the product of the [`center_density(::ZZLat)`](@ref) of ``L``
times the volume of the unit ``n``-ball.

# Examples
```jldoctest
julia> L = root_lattice(:E, 8);

julia> density(L)
[0.253669507901048014 +/- 6.66e-19]
```
"""
@attr RealFieldElem function density(L::ZZLat)
  @req is_definite(L) "Only implemented for definite lattices"
  n = rank(L)
  RR = real_field()
  RRpi = RR(pi)
  m = div(n, 2, RoundDown)

  # Volume unit n-sphere
  if iseven(n)
    Vn = RRpi^m/RR(factorial(m))
  else
    Vn = RR(2^n)*RRpi^m*RR(factorial(m))/RR(factorial(n))
  end
  mu = RR(minimum(L))
  d = RR(abs(det(L)))
  rho = sqrt(mu)/2
  return Vn*rho^n/sqrt(d)
end

###############################################################################
#
#  Hermite number
#
###############################################################################

@doc raw"""
    hermite_number(L::ZZLat) -> RealFieldElem

Return the Hermite number of the definite lattice ``L``.

For a definite lattice ``L`` of rank ``n``, absolute determinant ``d`` and
minimum ``m``, the Hermite number of ``L`` is defined by:

```math
\gamma := \frac{m}{d^{1/n}}.
```

# Examples
```jldoctest
julia> L = root_lattice(:E, 7);

julia> hermite_number(L)
[1.811447328527813353 +/- 5.13e-19]
```
"""
@attr RealFieldElem function hermite_number(L::ZZLat)
  @req is_definite(L) "Only implemented for definite lattices"
  RR = real_field()
  mu = RR(minimum(L))
  d = RR(abs(det(L)))^(1/rank(L))
  return mu/d
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
@attr Int function kissing_number(L::ZZLat)
  @req is_definite(L) "Lattice must have positive rank"
  if rank(L) == 0
    return 0
  end
  return 2 * length(shortest_vectors(L))
end

################################################################################
#
#  Successive minima
#
################################################################################

@doc raw"""
    successive_minima(L::ZZLat) -> Vector{QQFieldElem}

Given a positive definite lattice $L$, return the successive minima of $L$.
See [`successive_minima_with_vectors`](@ref) for the definition.
"""
function successive_minima(L::ZZLat)
  return successive_minima_with_vectors(L)[1]
end

@doc raw"""
    successive_minima_with_vectors(L::ZZLat) -> Vector{QQFieldElem},
                                                Vector{Vector{ZZRingElem}}

Given a positive definite lattice $L$, return the successive minima of $L$ and
a list of vectors realizing the minima.

By definition, the $i$-th successive minima of $L$ is the smallest non-negative
integer $\lambda_i$, such that the vectors of $L$ of norm bounded by
$\lambda_i$ span a lattice of rank $i$.

# Examples

```jldoctest
julia> L = integer_lattice(gram = ZZ[1 0 0; 0 2 0; 0 0 3]);

julia> successive_minima_with_vectors(L)
(QQFieldElem[1, 2, 3], Vector{ZZRingElem}[[1, 0, 0], [0, 1, 0], [0, 0, 1]])
```
"""
function successive_minima_with_vectors(L::ZZLat)
  @req is_positive_definite(L) "Lattice must be positive definite"
  n = rank(L)
  # the ouput consists of two lists of length n,
  # so we can already initialize said lists
  res = Array{QQFieldElem}(undef, n)
  resv = Array{Vector{ZZRingElem}}(undef, n)

  # Trivial case
  if iszero(n)
    return res, resv
  end

  # Sometimes L has a good Gram matrix so there is nothing to do
  min_length = minimum(L)
  if all(isequal(min_length), diagonal(gram_matrix(L)))
    _v = zeros(ZZRingElem, n)
    for i in 1:n
      res[i] = min_length
      ei = deepcopy(_v)
      add!(ei[i], 1)
      resv[i] = ei
    end
    return res, resv
  end

  ind = Int(1) # Index of new successive minima
  m = min(maximum(diagonal(gram_matrix(lll(L)))), maximum(diagonal(gram_matrix(L))))

  # We iterate on vectors up to norm m; we put in a buffer list the vectors
  # of norm greater than min_length so that we treat shortest vectors first
  S = short_vectors_iterator(L, m)
  buffer = Tuple{Vector{ZZRingElem}, QQFieldElem}[]
  H = zero_matrix(ZZ, n, n) # hnf of current Q-generating set
  w = zero_matrix(ZZ, 1, n)
  for x in S
    if x[2] > min_length
      push!(buffer, deepcopy(x))
      continue
    end
    w[1:1, :] = first(x)
    # check whether the vector is already in the ZZ-span
    reduce_mod_hnf_ur!(w, H)
    iszero(w) && continue
    # Checks whether the vector is in the QQ-span
    H[ind:ind, :] = w
    hnf!(H)
    is_zero_row(H, ind) && continue
    # Rank increases
    res[ind] = last(x)
    resv[ind] = first(x)
    # We have found the good number of vectors so are done
    # We do not look for a basis of L, just of a finite index sublattice
    if ind == n
      return res, resv
    end
    ind += 1
  end

  sort!(buffer; by=last)
  while !isempty(buffer)
    x = popfirst!(buffer)
    w[1:1, :] = first(x)
    reduce_mod_hnf_ur!(w, H)
    iszero(w) && continue
    H[ind:ind, :] = w
    hnf!(H)
    is_zero_row(H, ind) && continue
    res[ind] = last(x)
    resv[ind] = first(x)
    if ind == n
      return res, resv
    end
    ind += 1
  end
  error("Something went wrong")
end

################################################################################
#
# Short vectors affine
#
################################################################################

@doc raw"""
    enumerate_quadratic_triples(
        Q::MatrixElem{T},
        b::MatrixElem{T},
        c::RationalUnion;
        algorithm::Symbol=:short_vectors,
        equal::Bool=false
      ) where T <: Union{ZZRingElem, QQFieldElem}
                              -> Vector{Tuple{Vector{ZZRingElem}, QQFieldElem}}

Given the Gram matrix ``Q`` of a positive definite quadratic form, return
the list of pairs ``(v, d)`` so that ``v`` satisfies $v*Q*v^T + 2*v*Q*b^T + c \leq 0$
where ``b`` is seen as a row vector and ``c`` is a rational number.
Moreover ``d`` is so that $(v-b)*Q*(v-b)^T = d$.

For the moment, only the algorithm `:short_vectors` is available. The function
uses the data required for the closest vector problem for the quadratic triple
`[Q, b, c]`; in particular, ``d`` is smaller than the associated upper-bound $M$
(see [`close_vectors`](@ref)).

If `equal` is set to `true`, the function returns only the pairs ``(v, d)`` such
that $d=M$.
"""
function enumerate_quadratic_triples(
    Q::MatrixElem{T},
    b::MatrixElem{T},
    c::RationalUnion;
    algorithm::Symbol=:short_vectors,
    equal::Bool=false
  ) where T <: Union{ZZRingElem, QQFieldElem}
  return [deepcopy(i) for i in enumerate_quadratic_triples_iterator(Q,b,c,algorithm,equal)]
end

function enumerate_quadratic_triples_iterator(
    Q::MatrixElem{T},
    b::MatrixElem{T},
    c::RationalUnion;
    algorithm::Symbol=:short_vectors,
    equal::Bool=false
  ) where T <: Union{ZZRingElem, QQFieldElem}
  if algorithm == :short_vectors
    if T == ZZRingElem
      _Q = map_entries(QQ, Q)
      _b = map_entries(QQ, b)
      L, p, dist = _convert_type(_Q, _b, QQ(c))
    else
      L, p, dist = _convert_type(Q, b, QQ(c))
    end
    dist < 0 && return Tuple{Vector{ZZRingElem}, QQFieldElem}[]
    if equal
      cv = close_vectors_iterator(L, vec(collect(p)), dist, dist, ZZRingElem; check=false)
    else
      cv = close_vectors_iterator(L, vec(collect(p)), dist, ZZRingElem; check=false)
    end
  else
    error("Algorithm ($(algorithm)) not (yet) implemented for this function")
  end
  return cv
end


########################################################################################
#
#        Short vectors affine
#
########################################################################################


@doc raw"""
    short_vectors_affine(
        S::ZZLat,
        v::QQMatrix,
        alpha::RationalUnion,
        d::RationalUnion
      ) -> Vector{QQMatrix}

Given a hyperbolic or negative definite $\mathbb{Z}$-lattice ``S``, return the
set of vectors

```math
\{x \in S : x^2=d, x.v=\alpha \}.
```
where ``v`` is a given vector in the ambient space of ``S`` with positive square,
and ``\alpha`` and ``d`` are rational numbers.

The vectors in output are given in terms of their coordinates in the ambient
space of ``S``.

The implementation is based on Algorithm 2.2 in [Shi15](@cite)
"""
function short_vectors_affine(
    S::ZZLat,
    v::QQMatrix,
    alpha::RationalUnion,
    d::RationalUnion
  )
  p, _, n = signature_tuple(S)
  @req p <= 1 || n <= 1 "Lattice must be definite or hyperbolic"
  _alpha = QQ(alpha)
  _d = QQ(d)
  gram = gram_matrix(S)
  tmp = v*gram_matrix(ambient_space(S))*transpose(basis_matrix(S))
  v_S = solve(gram_matrix(S), tmp; side=:left)
  if n > 1
    sol = _short_vectors_affine(gram, v_S, _alpha, _d)
  else
    map_entries!(-, gram, gram)
    sol = _short_vectors_affine(gram, v_S, -_alpha, -_d)
  end
  B = basis_matrix(S)
  return QQMatrix[s*B for s in sol]
end

@doc raw"""
    short_vectors_affine
        gram::MatrixElem{T},
        v::MatrixElem{T},
        alpha::RationalUnion,
        d::RationalUnion
      ) where T <: Union{ZZRingElem, QQFieldElem} -> Vector{MatrixElem{T}}

Given the Gram matrix `gram` of a hyperbolic or negative definite
$\mathbb{Z}$-lattice ``S``, return the set of vectors

```math
\{x \in S : x^2=d, x.v=\alpha \}.
```
where ``v`` is a given vector of positive square, represented by its coordinates
in the standard basis of the rational span of ``S``, and ``\alpha`` and ``d``
are rational numbers.

The vectors in output are given in terms of their coordinates in the rational
span of ``S``.

The implementation is based on Algorithm 2.2 in [Shi15](@cite)
"""
function short_vectors_affine(
    gram::MatrixElem{T},
    v::MatrixElem{T},
    alpha::RationalUnion,
    d::RationalUnion
  ) where T <: Union{ZZRingElem, QQFieldElem}
  return _short_vectors_affine(gram, v, alpha, d)
end

@doc raw"""
    short_vectors_affine_iterator
        gram::MatrixElem{T},
        v::MatrixElem{T},
        alpha::RationalUnion,
        d::RationalUnion
      ) where T <: Union{ZZRingElem, QQFieldElem} -> Vector{MatrixElem{T}}

Given the Gram matrix `gram` of a hyperbolic or negative definite
$\mathbb{Z}$-lattice ``S``, return an iterator over the following set of vectors

```math
\{x \in S : x^2=d, x.v=\alpha \}.
```
where ``v`` is a given vector of positive square, represented by its coordinates
in the standard basis of the rational span of ``S``, and ``\alpha`` and ``d``
are rational numbers.

The vectors in output are given in terms of their coordinates in the rational
span of ``S``.

The implementation is based on Algorithm 2.2 in [Shi15](@cite)
"""
function short_vectors_affine_iterator(
    gram::MatrixElem{T},
    v::MatrixElem{T},
    alpha::RationalUnion,
    d::RationalUnion
  ) where T <: Union{ZZRingElem, QQFieldElem}
  return _short_vectors_affine_iterator(gram, v, alpha, d)
end

# In this function we assume that gram is the Gram matrix of a definite or
# hyperbolic lattice. If not, then close_vectors will complain
function _short_vectors_affine(
    gram::MatrixElem{T},
    v::MatrixElem{T},
    alpha::RationalUnion,
    d::RationalUnion
  ) where T <: Union{ZZRingElem, QQFieldElem}
  return [deepcopy(i) for i in _short_vectors_affine_iterator(gram,v,alpha,d)]
end

@doc raw"""
    short_vectors_affine_iterator(
        S::ZZLat,
        v::QQMatrix,
        alpha::RationalUnion,
        d::RationalUnion
      ) -> Vector{QQMatrix}

Given a hyperbolic or negative definite $\mathbb{Z}$-lattice ``S``, return the
iterator that returns vectors

```math
\{x \in S : x^2=d, x.v=\alpha \}.
```
where ``v`` is a given vector in the ambient space of ``S`` with positive square,
and ``\alpha`` and ``d`` are rational numbers.

The vectors in output are given in terms of their coordinates in the ambient
space of ``S``.

The implementation is based on Algorithm 2.2 in [Shi15](@cite)
"""
function short_vectors_affine_iterator(
    S::ZZLat,
    v::QQMatrix,
    alpha::RationalUnion,
    d::RationalUnion
  )
  p, _, n = signature_tuple(S)
  @req p <= 1 || n <= 1 "Lattice must be definite or hyperbolic"
  _alpha = QQ(alpha)
  _d = QQ(d)
  gram = gram_matrix(S)
  tmp = v*gram_matrix(ambient_space(S))*transpose(basis_matrix(S))
  v_S = solve(gram_matrix(S), tmp; side=:left)
  if n > 1
    sol = _short_vectors_affine_iterator(gram, v_S, _alpha, _d)
  else
    map_entries!(-, gram, gram)
    sol = _short_vectors_affine_iterator(gram, v_S, -_alpha, -_d)
  end
  B = basis_matrix(S)
  elem_type = typeof(v)
  sv_affine_iterator = ShortVectorsAffineLatIterator{typeof(sol), elem_type}(sol, B, zero(B, 1, number_of_columns(B)))
  return sv_affine_iterator
end

function _short_vectors_affine_iterator(
    gram::MatrixElem{T},
    v::MatrixElem{T},
    alpha::RationalUnion,
    d::RationalUnion
  ) where T <: Union{ZZRingElem, QQFieldElem}
  # find a solution <x,v> = alpha with x in L if it exists
  res = MatrixElem{T}[]
  w = gram*transpose(v)
  if T == QQFieldElem
    wd = lcm(denominator(w), denominator(alpha))
    wn = map_entries(ZZ, wd*w)
    beta = numerator(alpha*wd)
  else
    wd = ZZ(denominator(alpha))
    wn = wd*w
    beta = numerator(alpha*wd)
  end

  ok, x = can_solve_with_solution(transpose(wn), matrix(ZZ, 1, 1, [beta]); side=:right)
  if !ok
    return res
  end

  K = kernel(wn; side=:left)
  # (x + y*K)*gram*(x + y*K) = x gram x + 2xGKy + y K G K y

  # now we want to formulate this as a cvp
  # (x +y K) gram (x+yK) == d
  GK = gram*transpose(K)
  Q = K * GK
  b = transpose(x) * GK
  c = (transpose(x)*gram*x)[1,1] - d
  # solve the quadratic triple
  if Q[1, 1] < 0
    map_entries!(-, Q, Q)
    cv_vec = enumerate_quadratic_triples_iterator(Q, transpose(-b), -c; equal=true)
  else
    cv_vec = enumerate_quadratic_triples_iterator(Q, transpose(b), c; equal=true)
  end
  xt = map_entries(base_ring(gram), transpose(x))
  elem_type = typeof(v)
  sv_affine_iterator = ShortVectorsAffineIterator{typeof(cv_vec), elem_type}(cv_vec, base_ring(gram), nrows(Q), K, xt, zero_matrix(base_ring(gram), 1, number_of_columns(xt)), zero_matrix(base_ring(gram), 1, nrows(Q)))
  return sv_affine_iterator
end

struct ShortVectorsAffineIterator{S, elem_type}
  cv_vec::S
  b_ring
  nrows
  K
  xt
  v
  u
end

Base.IteratorSize(::Type{<:ShortVectorsAffineIterator}) = Base.SizeUnknown()
Base.eltype(::Type{ShortVectorsAffineIterator{X, elem_type}}) where {X, elem_type} = Tuple{Vector{elem_type}}

function Base.iterate(C::ShortVectorsAffineIterator{X, elem_type}, start = nothing) where {X, elem_type}
  if start === nothing
    it = iterate(C.cv_vec)
  else
    it = iterate(C.cv_vec, start)
  end

  if it === nothing
    return nothing
  end
  #Cv = C.xt + matrix(C.b_ring, 1, C.nrows, it[1][1])*C.K
  for i in 1:C.nrows
    C.u[i] = it[1][1][i]
  end
  add!(C.v, C.xt, mul!(C.v, C.u, C.K))
  return (deepcopy(C.v)), it[2]
end

struct ShortVectorsAffineLatIterator{S, elem_type}
  sv_it::S
  B
  sv
end


Base.IteratorSize(::Type{<:ShortVectorsAffineLatIterator}) = Base.SizeUnknown()
Base.eltype(::Type{ShortVectorsAffineLatIterator{X, elem_type}}) where {X, elem_type} = Tuple{Vector{elem_type}}

function Base.iterate(C::ShortVectorsAffineLatIterator{X, elem_type}, start = nothing) where {X, elem_type}
  if start === nothing
    it = iterate(C.sv_it)
  else
    it = iterate(C.sv_it, start)
  end

  if it === nothing
    return nothing
  end

  mul!(C.sv, it[1], C.B)
  return (deepcopy(C.sv)), it[2]
end



########################################################################################
#
#        Short vectors with given divisibility
#
########################################################################################


@doc raw"""
    vectors_of_square_and_divisibility(
      L::ZZLat,
      S::ZZLat,
      n::RationalUnion,
      d::RationalUnion = scale(L);
      coordinates_representation::Symbol=:S,
      check::Bool=true,
    ) -> Vector{Tuple{QQMatrix}, RationalUnion, RationalUnion}}

Given a nondegenerate $\mathbb{Z}$-lattice ``L`` and a nondegenerate definite
$\mathbb{Z}$-lattice ``S`` in the ambient space of ``L``, return all the
vectors in $S \cap (L\otimes \mathbb{Q})$ whose square has absolute value $|n|$
and whose divisibility in ``L`` is in the ideal $d\mathbb{Z}$.

For a vector ``v`` in the ambient quadratic space $(V, \Phi)$ of ``L``,
we call the divisibility of ``v`` in ``L`` the nonnegative generator of the
fractional ideal $\Phi(v, L)$ of $\mathbb{Z}$.

The entry `n` must be nonzero and `d` must be a positive rational number,
set to `scale(L)` by default.

!!! note
    Alternatively, instead of single values `n` and `d` one can input:
    * a list of pairs of rational numbers `(n, d)` where `n` is nonzero and
      `d` is positive;
    * a dictionary whose keys are positive rational numbers `d` and the
      associated list of numbers consist of nonzero rational numbers `n`.

The output consists of a list of triples `(v, n', d')` where `v` is a vector
of ``S`` of square of absolute value $n'$ and of divisibility $d'$ in ``L``.

!!! note
    In the case where one wants to choose ``S`` to be ``L`` itself, one can
    call instead `vectors_of_square_and_divisibility(L, n, d)`.

One can choose in which coordinates system each vector `v` in output is
represented by changing the symbol `coordinates_representation`.
There are three possibilities:
  - `coordinates_representation = :L`: the vector `v` is given in terms of its
    coordinates in the standard basis of the rational span of the lattice
    ``L``;
  - `coordinates_representation = :S` (default): the vector `v` is given in
    terms of its coordinates in the fixed basis of the lattice ``S``;
  - `coordinates_representation = :ambient`: the vector `v` is given in terms
    of its coordinates in the standard basis of the ambient space of ``L``.

If the keyword argument `check` is set to true, the function checks whether
``S`` is definite.

# Examples
```jldoctest
julia> E6 = root_lattice(:E, 6)
Integer lattice of rank 6 and degree 6
with gram matrix
[ 2   -1    0    0    0    0]
[-1    2   -1    0    0    0]
[ 0   -1    2   -1    0   -1]
[ 0    0   -1    2   -1    0]
[ 0    0    0   -1    2    0]
[ 0    0   -1    0    0    2]

julia> A2 = lattice_in_same_ambient_space(E6, basis_matrix(E6)[1:2, :])
Integer lattice of rank 2 and degree 6
with gram matrix
[ 2   -1]
[-1    2]

julia> C = orthogonal_submodule(E6, A2)
Integer lattice of rank 4 and degree 6
with gram matrix
[12   -3    0   -3]
[-3    2   -1    0]
[ 0   -1    2    0]
[-3    0    0    2]

julia> vectors_of_square_and_divisibility(E6, C, 12, 3; coordinates_representation=:L)
9-element Vector{Tuple{QQMatrix, QQFieldElem, QQFieldElem}}:
 ([-1 -2 -3 -4 -2 0], 12, 3)
 ([-1 -2 -3 -1 1 -3], 12, 3)
 ([-2 -4 -6 -2 -1 -3], 12, 3)
 ([-1 -2 -3 -1 -2 -3], 12, 3)
 ([-2 -4 -6 -5 -4 -3], 12, 3)
 ([-1 -2 -3 -1 -2 0], 12, 3)
 ([-1 -2 -3 -4 -2 -3], 12, 3)
 ([-2 -4 -6 -5 -1 -3], 12, 3)
 ([-1 -2 -3 -1 1 0], 12, 3)

julia> L = integer_lattice(; gram=matrix(QQ, 2, 2, [2 1; 1 4]))
Integer lattice of rank 2 and degree 2
with gram matrix
[2   1]
[1   4]

julia> vectors_of_square_and_divisibility(L, 8, 2)
1-element Vector{Tuple{QQMatrix, QQFieldElem, QQFieldElem}}:
 ([-2 0], 8, 2)

julia> length(short_vectors(L, 8, 8))
3
```
"""
vectors_of_square_and_divisibility

function vectors_of_square_and_divisibility(
    L::ZZLat,
    S::ZZLat,
    n::RationalUnion,
    d::RationalUnion = scale(L);
    coordinates_representation::Symbol=:S,
    check::Bool=true,
  )
  @req ambient_space(L) === ambient_space(S) "Lattices do not lie in the same ambient space"
  if check
    @req is_definite(S) "Second input must be definite"
  end
  @req d > 0 "Divisibility ($d) must be positive"
  @req !iszero(n) "Square ($n) must be nonzero"
  nQQ = abs(QQ(n))
  de = denominator(n)
  if de > 1
    L = rescale(L, de; cached=false)
    S = lattice_in_same_ambient_space(L, basis_matrix(S))
    n = n*de^2
    d = d*de
  end
  Sd = intersect(d*dual(L), S)
  BSd = basis_matrix(Sd)
  l = short_vectors(Sd, n, n)
  if coordinates_representation == :S
    B = solve(basis_matrix(S), basis_matrix(Sd); side=:left)
  elseif coordinates_representation == :L
    B = solve(basis_matrix(L), basis_matrix(Sd); side=:left)
  elseif coordinates_representation == :ambient
    B = BSd
  else
    error("Wrong symbol for coordinates representation")
  end
  out = Tuple{QQMatrix, QQFieldElem, QQFieldElem}[]
  for a in l
    v = matrix(QQ, 1, rank(Sd), a[1])
    dv = divisibility(L, v*BSd)
    v = v*B
    push!(out, (v, nQQ, dv))
  end
  sort!(out; lt=(a,b) -> a[3] < b[3])
  return out
end

function vectors_of_square_and_divisibility(
    L::ZZLat,
    n::RationalUnion,
    d::RationalUnion = scale(L);
    coordinates_representation::Symbol=:ambient,
    check::Bool=true,
  )
  if check
    @req is_definite(L) "Lattice must be definite"
  end
  return vectors_of_square_and_divisibility(L, L, n, d; coordinates_representation, check=false)
end

function vectors_of_square_and_divisibility(
    L::ZZLat,
    S::ZZLat,
    vector_type::Vector;
    coordinates_representation::Symbol=:S,
    check::Bool=true,
  )
  @req ambient_space(L) === ambient_space(S) "Lattices do not lie in the same ambient space"
  if check
    @req is_definite(S) "Second input must be definite"
  end
  ns = sort!(unique!(first.(vector_type)))
  ds = [gcd([a[2] for a in vector_type if a[1] == n]) for n in ns]
  vector_type_dict = Dict{eltype(ds), Vector{eltype(ns)}}()
  for d in unique(ds)
    vector_type_dict[d] = [ns[i] for i in 1:length(ns) if ds[i] == d]
  end
  return vectors_of_square_and_divisibility(L, S, vector_type_dict; coordinates_representation, check=false)
end

function vectors_of_square_and_divisibility(
    L::ZZLat,
    vector_type::Vector;
    coordinates_representation::Symbol=:L,
    check::Bool=true,
  )
  if check
    @req is_definite(L) "Lattice must be definite"
  end
  return vectors_of_square_and_divisibility(L, L, vector_type; coordinates_representation, check=false)
end

function vectors_of_square_and_divisibility(
    L::ZZLat,
    S::ZZLat,
    vector_type::Dict;
    coordinates_representation::Symbol=:S,
    check::Bool=true,
  )
  @req ambient_space(L) === ambient_space(S) "Lattices do not lie in the same ambient space"
  if check
    @req is_definite(S) "Second input must be definite"
  end
  @req all(>(0), keys(vector_type)) "Divisibilities must be positive"
  out = Tuple{QQMatrix, QQFieldElem, QQFieldElem}[]
  for d in keys(vector_type)
    @req all(!iszero, vector_type[d]) "Squares for the divisibility $d must be nonzero"
    de = lcm(denominator.(vector_type[d]))
    if de > 1
      _L = rescale(L, de; cached=false)
      _S = lattice_in_same_ambient_space(_L, basis_matrix(S))
      _d = d*de
    else
      _L = L
      _S = S
      _d = d
    end
    Sd = intersect(_d*dual(_L), _S)
    BSd = basis_matrix(Sd)
    for n in vector_type[d]
      nQQ = abs(QQ(n))
      if de > 1
        _n = n*de^2
      else
        _n = n
      end
      l = short_vectors(Sd, _n, _n)
      if coordinates_representation == :S
        B = solve(basis_matrix(_S), basis_matrix(Sd); side=:left)
      elseif coordinates_representation == :L
        B = solve(basis_matrix(_L), basis_matrix(Sd); side=:left)
      elseif coordinates_representation == :ambient
        B = BSd
      else
        error("Wrong symbol for coordinates representation")
      end
      for a in l
        v = matrix(QQ, 1, rank(Sd), a[1])
        dv = divisibility(L, v*BSd)
        v = v*B
        push!(out, (v, nQQ, dv))
      end
    end
  end
  sort!(out, lt=(a,b) -> a[2] < b[2] || a[2] == b[2] && a[3] < b[3])
  return out
end

function vectors_of_square_and_divisibility(
    L::ZZLat,
    vector_type::Dict;
    coordinates_representation::Symbol=:L,
    check::Bool=true,
  )
  if check
    @req is_definite(L) "Lattice must be definite"
  end
  return vectors_of_square_and_divisibility(L, L, vector_type; coordinates_representation, check=false)
end


########################################################################################
#
#            Short vectors with condition
#
########################################################################################

raw"""
    short_vectors_with_condition(L::ZZLat; search_fixed_vectors::Bool) -> Tuple{<:Vector, <:Vector}, Vector{ZZMatrix}

Return a list of vectors, that contains the orbits of the standard basis vectors under the reduced automorphism group $\mathrm{Aut}(L, \rho)$.
together with a list of $\mathrm{Aut}(L, \rho)$-invariant gram matrices where $\rho$ is a Weyl vector of the root sublattice of `L`.

# Input
- `search_fixed_vectors::Bool` -- take sums of vectors with the same invariants to obtain new invariant vectors. Use it to refine the invariant. Rinse and repeat.

# Output:
- a tuple `(V, G)` consiting of:
- a list of tuples `V = [(v_1, n_1), (v_2, n_2), ....]`; where `v_i` is a point of `L` and `n_i` an $\mathrm{Aut}(L,\rho)$ invariant of `v_i`, called its "norm".
- a list of symmetric integer matrices `G = [G_1, ..., G_k]`;
such that:
- `dot(v_i,G[j]*v_i) == (n_i)[j]` for all `i` in `1,...,rank(L)` and `j` in `1,...,k`.
- the standard basis vectors and their norms with respect to `G` are contained in `V`
"""
function short_vectors_with_condition(L::ZZLat;
                                      search_fixed_vectors::Bool=false,
                                      search_invariant_subspace::Bool=false)
  return short_vectors_with_condition(ZZRingElem, L; search_fixed_vectors, search_invariant_subspace)
end

function short_vectors_with_condition(T::Type,
                                      L::ZZLat;
                                      search_fixed_vectors::Bool=true,
                                      search_invariant_subspace::Bool=false)
  proj, target_proj_root_inv, target_norms, denoms, grams = _short_vectors_with_condition_preprocessing(L, T)
  return _short_vectors_with_condition(T, L, proj, target_proj_root_inv, target_norms, denoms, grams; search_fixed_vectors, search_invariant_subspace)
end


function short_vectors_with_condition(L1::ZZLat,
                                      L2::ZZLat)
  T = ZZRingElem
  search_fixed_vectors = false
  search_invariant_subspace = false
  if L1===L2
    @vtime :Lattice 1 proj, target_proj_root_inv, target_norms, denoms, grams = _short_vectors_with_condition_preprocessing(L1)
    return true, _short_vectors_with_condition(T, L1, proj, target_proj_root_inv, target_norms, denoms, grams; search_fixed_vectors, search_invariant_subspace)
  end
  @vtime :Lattice 1 (proj1, target_proj_root_inv1, target_norms1, denoms1, grams1),(root_type1, fundamental_roots1), invariant_matrix1 = _short_vectors_with_condition_preprocessing_with_root_data(L1)
  @vtime :Lattice 1 (proj2, target_proj_root_inv2, target_norms2, denoms2, grams2),(root_type2, fundamental_roots2),invariant_matrix2 = _short_vectors_with_condition_preprocessing_with_root_data(L2)
  _V1 = Vector{Tuple{Vector{T},Vector{T}}}()
  _V2 = Vector{Tuple{Vector{T},Vector{T}}}()
  if root_type1 != root_type2 || rank(L1) != rank(L2) || det(L1) != det(L2)
    return false, _V1, _V2, ZZMatrix[], ZZMatrix[]
  end
  n = rank(L1)
  target_proj_root_inv2_in_L1 = typeof(target_proj_root_inv1)()
  invariant_matrix1QQ = QQ.(invariant_matrix1)
  invariant_matrix2QQ = QQ.(invariant_matrix2)
  G1fix = gram_matrix(ambient_space(L1),invariant_matrix1QQ)
  G2fix = gram_matrix(ambient_space(L2),invariant_matrix2QQ)
  if G1fix != G2fix
    @assert G1fix==G2fix "interesting case"
    return false, _V1, _V2, ZZMatrix[], ZZMatrix[]
  end
  Lproj1 = lattice(ambient_space(L1), proj1[1]; isbasis=false)
  for (v,n) in target_proj_root_inv2
    w1 = solve(invariant_matrix2QQ, v; side=:left)
    w = w1*invariant_matrix1QQ
    if !all(isone(denominator(i)) for i in coordinates(w, Lproj1))
      # the invariant (weyl) vectors embedd in some incompatible ways
      return false, _V1, _V2, ZZMatrix[], ZZMatrix[]
    end
    # it is not because we identify the fundamental root systems ... but they are not so easy to identify!
    push!(target_proj_root_inv2_in_L1, (w,n))
  end
  # Todo:
  # We disable the search for new invariant vectors, because it would be difficult to match them as is.
  # The reason is that we compute a basis of the invariant space in order for it to have small coefficients.
  # This basis depends on the original basis of the lattice (via  LLL, hnf and rref).
  # To make this work, one has to take the vectors from summation without postprocessing them, then it is clear how to match them
  # (sums of vectors with the same invariant must be mapped to one another).
  try
    T = Int
    _V1, grams1, _, _ = _short_vectors_with_condition(T, L1, proj1, target_proj_root_inv2_in_L1, target_norms2, denoms1, grams1; search_fixed_vectors, search_invariant_subspace, mode=:iso)
    _V2, grams2, _, _ = _short_vectors_with_condition(T, L2, proj2, target_proj_root_inv2, target_norms2, denoms2, grams2; search_fixed_vectors, search_invariant_subspace, mode=:auto)
  catch t
    t isa InexactError || rethrow(t)
    try
      T = ZZRingElem
      _V1, grams1, _, _ = _short_vectors_with_condition(T, L1, proj1, target_proj_root_inv2_in_L1, target_norms2, denoms1, grams1; search_fixed_vectors, search_invariant_subspace, mode=:iso)
      _V2, grams2, _, _ = _short_vectors_with_condition(T, L2, proj2, target_proj_root_inv2, target_norms2, denoms2, grams2; search_fixed_vectors, search_invariant_subspace, mode=:auto)
    catch s
      s isa InexactError || rethrow(s)
      # return the empty lists
      # then it will be handled by the direct approach later which is better.
      return true, _V1, _V2, grams1, grams2
    end
  end
  if length(_V1)!=length(_V2) || length(grams1)!=length(grams2)
    return false, _V1, _V2, ZZMatrix[], ZZMatrix[]
  end
  pushfirst!(grams1, ZZ.(gram_matrix(L1)))
  pushfirst!(grams2, ZZ.(gram_matrix(L2)))
  V1 = [(v, vcat([T(inner_product(L1, v, v))], n)) for (v, n) in _V1]
  V2 = [(v, vcat([T(inner_product(L2, v, v))], n)) for (v, n) in _V2]
  return true, V1, V2, grams1, grams2
end

function _short_vectors_with_condition_preprocessing(L::ZZLat,
                                                     elem_type::Type{S}=Int) where {S}
  root_types, fundamental_roots = _root_lattice_recognition_fundamental(L)
  weyl_group_gens, grams, ord, (proj_root_inv, proj_root_coinv) = _weyl_group(L, root_types, fundamental_roots)
  return _short_vectors_with_condition_preprocessing(L, fundamental_roots, grams, proj_root_inv, proj_root_coinv, :rank, S)
end

function _short_vectors_with_condition_preprocessing_with_root_data(L::ZZLat,
                                                     elem_type::Type{S}=Int) where {S}
  root_types, fundamental_roots = _root_lattice_recognition_fundamental(L)
  weyl_group_gens, grams, ord, (proj_root_inv, proj_root_coinv), invariant_matrix = _weyl_group(L, root_types, fundamental_roots)
  return _short_vectors_with_condition_preprocessing(L, fundamental_roots, grams, proj_root_inv, proj_root_coinv,:rank, S), (root_types, fundamental_roots), invariant_matrix
end

function _short_vectors_with_condition_preprocessing(L::ZZLat,
                                                     fundamental_roots::Vector{ZZMatrix},
                                                     grams::Vector{ZZMatrix},
                                                     proj_root_inv::QQMatrix,
                                                     proj_root_coinv::Vector{Tuple{QQMatrix,Int}},
                                                     sort::Symbol=:rank,
                                                     elem_type::Type{S}=Int) where {S}
  n = rank(L)
  @assert rank(L)==degree(L)
  @hassert :Lattice 1 isone(basis_matrix(L))
  R = reduce(vcat, fundamental_roots; init=zero_matrix(ZZ, 0, rank(L)))
  Rperp = orthogonal_submodule(L, R*basis_matrix(L))
  LL, _ = _short_vector_generators_with_sublattice_2(Rperp, S; up_to_sign=true)
  pushfirst!(LL, lattice(ambient_space(L), R))
  proj = __projections(LL)
  proj_rank = rank.(LL)
  @hassert :Lattice 1 proj[1] == proj_root_inv + sum(i[1] for i in proj_root_coinv; init=zero_matrix(QQ, n, n))
  popfirst!(proj)
  popfirst!(proj_rank)
  proj = append!(first.(proj_root_coinv), proj)
  proj_rank = append!([i[2] for i in proj_root_coinv], proj_rank)
  pushfirst!(proj_rank, -1) # not used
  pushfirst!(proj, proj_root_inv)
  w = length(grams)
  m = w + length(proj) - 1
  target_norms = Vector{ZZRingElem}[zeros_array(ZZ, m) for i in 1:n]
  denoms = ZZRingElem[ZZ(1)]
  tmp_mat = one(proj[1])
  for i in 2:length(proj)
    p = proj[i]
    gram_pQQ = mul!(tmp_mat, p, mul!(tmp_mat, gram_matrix(L),transpose!(tmp_mat,p)))
    d = denominator(gram_pQQ)
    push!(grams, numerator(gram_pQQ))
    push!(denoms, d)
  end
  for k in 1:m
    for i in 1:n
      target_norms[i][k] = grams[k][i,i]
    end
  end
  target_proj_root_inv = [(proj[1][i, :],target_norms[i][1:w]) for i in 1:n]

  if sort == :rank
    # don't touch the first one
    #@assert proj_rank[2:end] == rank.(proj[2:end])
    p = sortperm([proj_rank[i] for i in 2:length(proj)]; rev = false)
    #p = sortperm([rank(proj[i]) for i in 2:length(proj)]; rev = false)
    per = pushfirst!(p .+ 1, 1)
    per2 = append!(collect(1:w), p .+ (w))
    per2inv = invperm(per2)
    proj = proj[per]
    denoms = denoms[per]
    grams = grams[per2]
    target_norms = [i[per2] for i in target_norms]
  end
  return proj, target_proj_root_inv, target_norms, denoms, grams
end

function _short_vectors_with_condition(T::Type{Int},
                                      L::ZZLat,
                                      proj::Vector{QQMatrix}, target_invariant::Vector{Tuple{Vector{QQFieldElem}, Vector{ZZRingElem}}},
                                      target_norms::Vector{Vector{ZZRingElem}},
                                      denoms::Vector{ZZRingElem}, grams::Vector{ZZMatrix};
                                      search_fixed_vectors::Bool=true,
                                      search_invariant_subspace::Bool=false,
                                      mode::Symbol=:auto)
  denoms_Int = Int.(denoms)
  target_norms_Int = Vector{Int}[Int.(i) for i in target_norms]
  target_invariant_Int = [(i[1],Int.(i[2])) for i in target_invariant]
  return _short_vectors_with_condition_integral(L,
                                           proj,
                                           target_invariant_Int,
                                           target_norms_Int,
                                           denoms_Int,
                                           grams;
                                           search_fixed_vectors,
                                           search_invariant_subspace,
                                           mode)
end

function _short_vectors_with_condition(T::Type{ZZRingElem},
                                      L::ZZLat,
                                      proj::Vector{QQMatrix}, target_invariant::Vector{Tuple{Vector{QQFieldElem}, Vector{ZZRingElem}}},
                                      target_norms::Vector{Vector{ZZRingElem}},
                                      denoms::Vector{ZZRingElem},
                                      grams::Vector{ZZMatrix};
                                      search_fixed_vectors::Bool=true,
                                      search_invariant_subspace::Bool=false,
                                      mode::Symbol=:auto)
  return _short_vectors_with_condition_integral(L, proj, target_invariant, target_norms, denoms, grams; search_fixed_vectors, search_invariant_subspace, mode)
end

function update_short_vector_invariants(D::S, T, found::Int) where {S<:Dict{Vector{Int}, Vector{LinearAlgebra.Adjoint{Int64, Vector{Int64}}}}}
  Dnew = S()
  n = ncols(T)
  for k in keys(D)
    k_new = vcat(zeros(Int, found), k)
    for v in D[k]
      k_new[1:n] .= _canonicalize!((v * T)') # _canonicalize! allows us to consider this invariant up to sign
      if k_new in keys(Dnew)
        push!(Dnew[k_new], v)
      else
        Dnew[deepcopy(k_new)] = [v]
      end
    end
  end
  return Dnew
end

function update_short_vector_invariants(D::S, T, found::Int) where {S<:Dict{Vector{ZZRingElem}, <:Vector{<:Vector{<:Union{ZZRingElem,QQFieldElem}}}}}
  Dnew = S()
  n = ncols(T)
  for k in keys(D)
    k_new = vcat(zeros_array(ZZ, found), k)
    for v in D[k]
      ii = _canonicalize!(ZZ.(v * T))
      k_new[1:n] = ii
      if k_new in keys(Dnew)
        push!(Dnew[k_new], v)
      else
        Dnew[deepcopy(k_new)] = [v]
      end
    end
  end
  return Dnew
end

#invariant_subspaceF[1:end-1,:] must be in rref!
function __search_invariant_subspaces!(D::Dict, invariant_subspace::QQMatrix, new_invariant_subspace::ZZMatrix, tmp_vec::Vector, tmp_mat::QQMatrix, H::ZZMatrix, invariant_subspaceF::fpMatrix, Hv::Set{ZZMatrix}, search_invariant_subspace::Bool=false, search_fixed_vectors::Bool=true)
  i1 = nrows(new_invariant_subspace)
  i2 = nrows(invariant_subspace)
  r1 = nrows(invariant_subspace)
  w = i2 - i1
  F = base_ring(invariant_subspaceF)
  pivs = zeros(Int, ncols(invariant_subspaceF))
  pure = zeros(Bool, ncols(invariant_subspaceF))
  dirty = true
  # compute pivs and pure
  Hecke._reduce_modulo_rref(invariant_subspaceF,nrows(invariant_subspaceF)-1, pivs, pure, dirty)
  dirty = false
  #Hv = Set{ZZMatrix}()
  for k in keys(D)
    if nrows(invariant_subspace)==ncols(invariant_subspace)
      # everything invariant nothing more to do
      break
    end
    if search_invariant_subspace && 40>length(D[k])>1 && length(Hv)<8
      #_hv = _fundamental_roots!([__not_adj(i) for i in D[k]])  # breaks stuff for ZZRingElem
      _hv = _row_span!([__not_adj(i) for i in D[k]])
      hv = matrix(ZZ, _hv)
      reduce_mod_hnf_ur!(hv, H)
      hv = hnf!(saturate(hv))
      push!(Hv, hv)
    end
    search_fixed_vectors || continue
    # the ones which do not have an invariant component are up to +-1 and sum to 0, discard them
    all(iszero(k[i]) for i in i1+1:i2) && continue
    # compute v = sum(D[k])
    # we cannot allow an overflow here
    v = ___sum(D[k]; init=tmp_vec)

    # copy to a matrix
    @assert length(v) == ncols(tmp_mat)
    @inbounds for i in 1:length(v)
      tmp_mat[i] = v[i]
      invariant_subspaceF[end, i] = v[i]
    end
    # Check if we discovered something new.
    if !Hecke._reduce_modulo_rref(invariant_subspaceF,nrows(invariant_subspaceF)-1, pivs, pure, dirty)
      rref!(invariant_subspaceF)
      dirty = true
      invariant_subspaceF = vcat(invariant_subspaceF, zero_matrix(F, 1, ncols(invariant_subspaceF)))
      invariant_subspace = vcat(invariant_subspace, tmp_mat)
      #rref!(invariant_subspace) # serves no purpose anymore
      new_invariant_subspace = vcat(new_invariant_subspace, numerator(tmp_mat))
      new_invariant_subspace = saturate(new_invariant_subspace)
      reduce_mod_hnf_ur!(new_invariant_subspace, H)
    else
      dirty = false
    end
  end
  @vprintln :Lattice 1 "Found $(length(Hv)) invariant subspaces"
  found = nrows(invariant_subspace) - r1
  return found, invariant_subspace, new_invariant_subspace, invariant_subspaceF, Hv
end

function ___sum(V::Vector{Vector{ZZRingElem}}; init::Vector)
  if eltype(init) === Int
    @assert false
    for i in 1:length(init)
      init[i] = 0
    end
  else
    init = zero!.(init)
  end
  for i in V
    add!.(init, i)
  end
  return init
end

function ___sum(V::Vector{<:LinearAlgebra.Adjoint}; init::Vector)
  if eltype(init) === Int
    @assert false
    for i in 1:length(init)
      init[i] = 0
    end
  else
    init = zero!.(init)
  end
  for i in V
    add!.(init, i')
  end
  return init
end

@inline function add!(z::Vector{QQFieldElem}, x::Vector{QQFieldElem}, y::Vector{QQFieldElem})
  @inbounds for i in 1:length(x)
    z[i] = add!(z[i], x[i], y[i])
  end
  return z
end

@inline function sub!(z::Vector{QQFieldElem}, x::Vector{QQFieldElem}, y::Vector{QQFieldElem})
  @inbounds for i in 1:length(x)
    z[i] = sub!(z[i], x[i], y[i])
  end
  return z
end

function _is_product_integral(b, flag_project2, tmp, tmpZZ)
  z = tmp
  for i in 1:ncols(flag_project2)
    mul!(z, b, @view flag_project2[:, i:i])
    if !is_integral(z[1])
      return false
    end
  end
  return true
end

function mul!(z::Vector{QQFieldElem}, a::Vector{ZZRingElem}, b::QQMatrix)
  @ccall libflint.fmpq_mat_fmpz_vec_mul_ptr(z::Ptr{Ref{QQFieldElem}}, a::Ptr{Ref{ZZRingElem}}, length(a)::Int, b::Ref{QQMatrix})::Nothing
  return z
end

function _is_integral(x::Vector{QQFieldElem}, tmp::ZZRingElem)
  return all(isone(denominator!(tmp, i)) for i in x)
end


function _denominator(v::Vector{QQFieldElem})
  z = one(ZZ)
  tmp = ZZ()
  for i in 1:length(v)
    z = lcm!(z, z, denominator!(tmp, v[i]))
  end
  return z
end


__zeros_array(::Type{ZZRingElem}, x...) = zeros_array(ZZ, x...)
__zeros_array(::Type{Int}, x...) = zeros(Int, x)'
__vcat(x::Vector{ZZRingElem},y::Vector{ZZRingElem}) = vcat(x,y) # append! does not work
function __vcat(x::LinearAlgebra.Adjoint{Int64, Vector{Int64}}, y::LinearAlgebra.Adjoint{Int64, Vector{Int64}})
  return vcat(x',y')'
end

function _short_vectors_with_condition_integral(L::ZZLat, proj::Vector{QQMatrix},
                                                target_invariant,
                                                target_norms::Vector{Vector{CoeffType}},
                                                denoms::Vector{CoeffType},
                                                grams::Vector{ZZMatrix};
                                                search_fixed_vectors::Bool=true,
                                                search_invariant_subspace::Bool=false,
                                                mode::Symbol=:auto) where {CoeffType <: Union{Int, ZZRingElem}}
  # Let L_i := proj[i](L)
  # We lll reduce each L_i and work throughout with the basis
  # M = L_1 + L_2 + ... + L_n
  # Set flag_proj[i] = sum(proj[1:i]) : L --> L_1 + ... + L_i=:N_i and let M_i < N_i be the image
  # We build up the short vectors along the flag
  # M_1 < M_2 < M_3 < .... < M_n = L
  # The step M_i to M_{i+1} is via
  # M_{i+1} < M_i + L_{i+1}
  # and testing for integrality
  # In the postprocessing we transform from the basis of M to the basis of L.

  if CoeffType === ZZRingElem
    VectorType = Vector{ZZRingElem}
  else
    VectorType = LinearAlgebra.Adjoint{Int64, Vector{Int64}}
  end
  @hassert :Lattice 1 isone(sum(proj))
  @hassert :Lattice 1 all(i^2==i for i in proj)
  n = rank(L)
  V = ambient_space(L)
  projL = [lll(rescale(lattice(V, proj[i]; check=false, isbasis=false),denoms[i]; cached=false);_is_definite=true) for i in 1:length(proj)]
  target_signed_invariant = Vector{CoeffType}[CoeffType.(ZZ.(coordinates(a, projL[1]))) for (a,_) in target_invariant]
  # We take one representative up to sign.
  target_invariant = [(_canonicalize!(i[1]),i[2]) for i in target_invariant]
  unique!(target_invariant)

  @assert all(is_integral(projL[i]) for i in 2:length(projL))
  B = reduce(vcat, basis_matrix.(projL))
  Binv = ZZ.(inv(B))
  L_in_L1toLn = hnf(Binv)
  gramB = B*gram_matrix(L)*transpose(B)

  # keeps track of the invariant subspace
  # built from invariant vectors discovered during the process and the input, i.e. the row span of proj[1]
  invariant_subspace_rank, invariant_subspace = rref(proj[1])
  invariant_subspace = invariant_subspace[1:invariant_subspace_rank, :]*Binv[:,1:invariant_subspace_rank]
  H = hnf!(saturate(numerator(invariant_subspace)))
  Hv = Set{ZZMatrix}()
  prime = next_prime(1 << (8 * sizeof(Int) - 2))
  F = Native.GF(prime)
  invariant_subspaceF = F.(H)
  rref!(invariant_subspaceF)
  invariant_subspaceF = vcat(invariant_subspaceF, zero_matrix(F,1,ncols(invariant_subspaceF)))
  # invariant_subspaceF[1:nrows(invariant_subspaceF)-1,:] must always be in rref!, we use it to solve efficiently
  # overflow is no problem ... then we just do a few useless computations, i.e. new_invariant_subspace gets a zero row.
  new_invariant_subspace = zero_matrix(ZZ, 0, invariant_subspace_rank) # keeps track of what is new
  T = zero_matrix(ZZ, rank(projL[1]), 0)
  w0 = invariant_subspace_rank

  flag_projection = proj[1]
  tmpZZ = ZZ()
  short_vectors1 = Dict{Vector{CoeffType},Vector{VectorType}}()
  for (_a,b) in target_invariant
    # For now we need to transform from the basis of L to that of L_1
    # TODO: Remove this?
    if CoeffType === ZZRingElem
      a = ZZ.(coordinates(_a, projL[1]))
    else
      a = (CoeffType.(ZZ.(coordinates(_a, projL[1]))))'
    end
    if b in keys(short_vectors1)
      # different targets can have the same first projection
      if !(a in short_vectors1[b])
        push!(short_vectors1[b], a)
      end
    else
      short_vectors1[b]=[a]
    end
  end
  k = length(proj)
  w = length(target_norms[1]) - (k-1)
  zeroCoeff = zero(CoeffType)
  #flag_projection = deepcopy(proj[1]) # changed inplace later
  for i in 2:k
    short_vectors2 = Dict{Vector{CoeffType},Vector{VectorType}}()
    for a in Set(n[1:w+i-1] for n in target_norms)
      short_vectors2[a] = VectorType[]
    end

    # prepare for integrality test
    N_i = reduce(vcat, basis_matrix(projL[j]) for j in 1:i)
    #flag_projection = add!(flag_projection, proj[i])
    #M_i = lattice(V, flag_projection; isbasis=false, check=false)
    M_i_in_N_i = @view L_in_L1toLn[:,1:nrows(N_i)]
    #M_i_in_N_i = ZZ.(solve(N_i,basis_matrix(M_i);side=:left))
    Sf, Uf, Vf = snf_with_transform(M_i_in_N_i)
    Vf = Vf
    _eldivNi_mod_Mi = diagonal(Sf)
    n_ones = count(isone, _eldivNi_mod_Mi)
    for i in n_ones+1:ncols(Vf)
      Vf[:,i] = mod.(Vf[:,i] ,Sf[i,i])
    end
    _eldivNi_mod_Mi = _eldivNi_mod_Mi[n_ones+1:end]
    r1 = sum(rank(projL[j]) for j in 1:i-1)
    _VfN_iminus1 = Vf[1:r1, n_ones+1:end]
    _VfLi = Vf[r1+1:end, n_ones+1:end]
    # deal with ZZRingElem vs Int
    if CoeffType === ZZRingElem
      VfN_iminus1 = _VfN_iminus1
      VfLi = _VfLi
      eldivNi_mod_Mi = _eldivNi_mod_Mi
    elseif CoeffType === Int
      VfN_iminus1 = [CoeffType(i) for i in _VfN_iminus1]
      VfLi = [CoeffType(i) for i in _VfLi]
      eldivNi_mod_Mi = (Int.(_eldivNi_mod_Mi))'
    end
    @assert nrows(VfLi) == rank(projL[i])
    @vprintln :Lattice 3 "elementary divisors $eldivNi_mod_Mi at stage i=$i"

    # prepare for filtering by norm
    target_norm_i = Set(n[w+i-1] for n in target_norms)
    r = nrows(invariant_subspace)
    target_norm = Dict{CoeffType, Set{Vector{CoeffType}}}()
    for n in target_norms
      a = n[w+i-1]
      b = n[1:w+i-2]
      if a in keys(target_norm)
        push!(target_norm[a], b)
      else
        target_norm[a] = Set([b])
      end
    end
    # prepare gluing data
    rank_i = rank(projL[i])
    tmp_u = __zeros_array(CoeffType, ncols(VfN_iminus1))
    short_vectors1_extra = Dict{Vector{CoeffType},Dict{Vector{CoeffType}, Vector{VectorType}}}()
    for k1 in keys(short_vectors1)
      for a in short_vectors1[k1]
        a_mod_Mi =__mul_mod!(tmp_u, a, VfN_iminus1, eldivNi_mod_Mi)
        k = a_mod_Mi
        # take into account that short_vectors returns only non-zero vectors.
        if zeroCoeff in keys(target_norm) && k1 in target_norm[zeroCoeff] && iszero(k)
          push!(k1, zeroCoeff)
          push!(short_vectors2[k1], __vcat(a,__zeros_array(CoeffType, rank_i)))
          pop!(k1)
        end
        if k in keys(short_vectors1_extra)
          D = short_vectors1_extra[k]
          if k1 in keys(D)
            push!(D[k1], a)
          else
            D[k1] = [a]
          end
        else
          short_vectors1_extra[deepcopy(k)] = Dict(k1=>[a])
        end
      end
    end
    #DNeg = Dict{Vector{Int},Vector{Int}}()
    #for k in keys(short_vectors1_extra)
    #  u = mod.((-).(k), eldivNi_mod_Mi')
    #  DNeg[u] = k
    #end
    # lower and upper bound for short vector enumeration of L_i
    ma = CoeffType(maximum(target_norm_i))
    mi = CoeffType(minimum(i for i in target_norm_i if !iszero(i);init=ma)) #not accepted by _finckepostint
    Gi = ZZ.(gram_matrix(projL[i])) # already lll reduced
    tmp_u1 = __zeros_array(CoeffType, ncols(VfLi))
    tmp_u2 = __zeros_array(CoeffType, ncols(VfLi))
    tmp_s = __zeros_array(CoeffType, ncols(Gi))
    for (s, q) in __short_vectors(Gi, mi, ma)
      # This is the innermost loop - do as little as possible here
      q in target_norm_i || continue
      if CoeffType===ZZRingElem
        tmp_s = set!.(tmp_s, s)
      else
        tmp_s = s'
      end
      s_mod_Mi = __mul_mod!(tmp_u1, tmp_s, VfLi, eldivNi_mod_Mi)
      k1plus = s_mod_Mi
      if k1plus in keys(short_vectors1_extra)
        D = short_vectors1_extra[k1plus]
        for t in target_norm[q]
          t in keys(D) || continue
          Dt = D[t]
          push!(t, q)
          for b in Dt
            push!(short_vectors2[t], __vcat(b, -tmp_s))
          end
          pop!(t)
        end
      end
      k1minus = __neg_mod!(tmp_u2, s_mod_Mi, eldivNi_mod_Mi)
      #if k1minus in keys(short_vectors1_extra)
      #if k1plus in keys(DNeg)
      #  k1minus = DNeg[k1plus]  # the dict variant is 0.2 ms faster ... not worth it
      #else
      #  continue
      #end
      if k1minus in keys(short_vectors1_extra)
        D = short_vectors1_extra[k1minus]
        for t in target_norm[q]
          t in keys(D) || continue
          iszero(t) && continue # avoid overcounting
          Dt = D[t]
          push!(t, q)
          for b in Dt
            push!(short_vectors2[t], __vcat(b, deepcopy(tmp_s)))
          end
          pop!(t)
        end
      end
    end
    T = vcat(T, zero_matrix(ZZ,rank(projL[i]),ncols(T)))
    if search_invariant_subspace || search_fixed_vectors
      # bring invariant_subspace to the correct size
      # TODO: It would probably be more efficient to just padd
      # the invariant sum by zeros in the end
      n_i = nrows(N_i)
      r_i = rank(projL[i])
      invariant_subspace = hcat(invariant_subspace, zero_matrix(QQ, nrows(invariant_subspace), r_i))
      invariant_subspaceF = hcat(invariant_subspaceF, zero_matrix(F, nrows(invariant_subspaceF), r_i)) # preserves rref!
      _Hv = ZZMatrix[hcat(i, zero_matrix(ZZ, nrows(i), r_i)) for i in Hv]
      Hv = Set(_Hv)
      new_invariant_subspace = hcat(new_invariant_subspace, zero_matrix(ZZ, nrows(new_invariant_subspace), r_i))
      H = hcat(H, zero_matrix(ZZ,nrows(H), r_i))
      tmp_invariant_vec = zeros_array(ZZ, n_i)
      tmpQQmat = zero_matrix(QQ, 1, n_i)
      # compute invariant vectors by taking the sum of all vectors with the same invariant
      # if we find something refine the invariants and search anew
      old_invariant_subspace_rank = nrows(invariant_subspace)
      t = rank(new_invariant_subspace)
      while true
        abc = __search_invariant_subspaces!(short_vectors2,
                                        invariant_subspace,
                                        new_invariant_subspace,
                                        tmp_invariant_vec,
                                        tmpQQmat,
                                        H,
                                        invariant_subspaceF,
                                        Hv, search_invariant_subspace, search_fixed_vectors)
        found, invariant_subspace, new_invariant_subspace, invariant_subspaceF, Hv = abc
        iszero(found) && break
        # update the invariants
        T = numerator(new_invariant_subspace*view(gramB,1:n_i,1:n_i))
        T = transpose(lll!(T))
        if CoeffType===ZZRingElem
          TCoeff = T
        elseif CoeffType===Int
          TCoeff = [CoeffType(i) for i in T]
        end
        @vprintln :Lattice 5 "hnf(new_invariant_subspace) = $(hnf(numerator(new_invariant_subspace*B[1:n_i,:])))"
        @vprintln :Lattice 4 "rref(invariant_subspace) = $(rref(invariant_subspace*B[1:n_i,:]))"
        @vprintln :Lattice 3 "T = $T"
        short_vectors2 = update_short_vector_invariants(short_vectors2, TCoeff, found)
      end
      found_this_round = nrows(invariant_subspace) - old_invariant_subspace_rank
      if found_this_round > 0
        # update target_norms
        t_old = t
        t = ncols(T)
        # Norms of the basis vectors of L
        # Since we work in the basis of L_1 + ... + L_i we need to compensate with Binv
        target_norms = [vcat(_canonicalize!(Binv[j,1:n_i]*T), target_norms[j][t_old+1:end]) for j in 1:nrows(Binv)]
        # filter what we do not need anymore
        invs = Set([target_norms[j][1:t+w0+i] for j in 1:nrows(Binv)])
        for k in keys(short_vectors2)
          k in invs && continue
          delete!(short_vectors2, k)
        end
      end
      w += found_this_round
    end
    short_vectors1 = short_vectors2
    @vprintln :Lattice 2 "$(sum(length(i) for i in values(short_vectors1);init=0)) vectors at stage i=$i"
  end
  # assemble the output
  n_out = sum(length.(values(short_vectors1)))
  output = Vector{Tuple{Vector{CoeffType}, Vector{CoeffType}}}(undef, n_out)
  invariants = Vector{Int}(undef, n_out)
  r = nrows(new_invariant_subspace)
  gZ = ZZ.(gram_matrix(L))
  BinvT = Binv*T
  for i in r:-1:1 # reverse order because of pushfirst!
    t = BinvT[:,i:i]
    tG = t*transpose(t)
    pushfirst!(grams, tG)
  end
  pushfirst!(grams, gZ)
  i = 0
  if CoeffType===ZZRingElem
    _B = numerator(B)
    d = denominator(B)
    gramL_CoeffType = gZ
  else
    _B = [CoeffType(i) for i in numerator(B)]
    d = CoeffType(denominator(B))
    gramL_CoeffType = [CoeffType(i) for i in gZ]
  end
  tmp_v = [CoeffType(0) for i in 1:ncols(gZ)]

  r1 = rank(projL[1])
  compressor = [1 for i in 1:r1]#[rand(1:1000) for i in 1:r1]
  target_signed_invariant_compressed = [dot(i,compressor) for i in target_signed_invariant]
  for b in keys(short_vectors1)
    bret = copy(b)
    @inbounds for i in 1:r
      bret[i] = bret[i]^2
    end
    isempty(short_vectors1[b]) && continue  # can happen for targets coming from a non-isometric lattice

    v = divexact.(__not_adj(first(short_vectors1[b])*_B), d)
    s = __norm!(gramL_CoeffType, v, tmp_v)
    pushfirst!(bret, s)
    for z in short_vectors1[b]
      i = i+1
      # TODO: computation of the invariant could be
      # faster if we do better bookkeeping
      # ... which perhaps we should do anyways
      invariant = dot(view(z, 1:r1), compressor)
      vv = divexact.(__not_adj(z*_B), d)
      vv, flipped = _canonicalize_with_data!(vv)
      if flipped
        invariants[i] = -invariant
      else
        invariants[i] = invariant
      end
      output[i] = (vv, copy(bret))
    end
  end
  @vprintln :Lattice 2 "discovered an additional fixed subspace of rank $(nrows(new_invariant_subspace))"
  @vprintln :Lattice 1 "visible fixed subspace has rank $(nrows(invariant_subspace))"
  if false # stuff from search_invariant_subspaces
    A = [i*B for i in Hv]
    V = ambient_space(L)
    A = [1-matrix(orthogonal_projection(V, a)) for a in A]
    A = [numerator(a*gZ*transpose(a)) for a in A]
    A = filter!(!in(grams), A)
    if length(A)>0
      _A = sum(rand(0:100)*a for a in A)
      if CoeffType === Int
        _ACoeff = [CoeffType(i) for i in _A]
      else
        _ACoeff = _A
      end
      push!(grams, _A)
      @vtime :Lattice 1 output = [(v,push!(i, __norm!(_ACoeff,v,tmp_v))) for (v,i) in output]
    end
  end
  if get_assertion_level(:Lattice) > 1
    for (v, n) in output
      @assert all(dot(v, grams[i], v) == n[i] for i in 1:length(grams)) "$(gram_matrix(L)), $((target_invariant,target_norms))"
    end
    abs_target_signed_invariant_compressed = Set(abs.(target_signed_invariant_compressed))
    @assert all(abs(i) in abs_target_signed_invariant_compressed for i in invariants)
    @assert length(invariants) == length(output)
    @assert length(target_signed_invariant_compressed) == rank(L)
    # This test makes sense only in automorphism mode
    if mode == :auto
      @assert [Binv[i,1:r1] for i in 1:n] == target_signed_invariant
      E = CoeffType.(identity_matrix(ZZ, n))
      for i in 1:n
        ei = E[i,:]
        @assert any(ei==j[1] for j in output)
        j = findfirst(==(ei), first.(output))
        @assert target_signed_invariant_compressed[i] == invariants[j]
      end
    end
    # so does this one
  end
  return output, grams, BinvT, proj[1], [numerator(i*B) for i in Hv], (invariants, target_signed_invariant_compressed)
end

__norm!(gram::Matrix{Int}, v::Vector{Int}, tmp_v::Vector{Int}) = dot(v, gram, v)
__norm!(gram::ZZMatrix, v::Vector{ZZRingElem}, tmp_v::Vector{ZZRingElem}) = dot(mul!(tmp_v,v,gram),v) # this could be improved if necessary


@inline function __mul_mod!(u::Vector{S}, v::Vector{S}, A, moduli::Vector{S}) where {S<:ZZRingElem}
  #@assert length(v) == nrows(A)
  #@assert ncols(A)==length(moduli)==length(u)
  u = mul!(u, v, A)
  return mod!.(u, moduli)
end

@inline function __mul_mod!(u::S, v::S, A::Matrix{Int}, moduli::S) where {S<:LinearAlgebra.Adjoint{Int, Vector{Int}}}
  #@assert length(v) == nrows(A)
  #@assert ncols(A)==length(moduli)==length(u)
  u = LinearAlgebra.mul!(u, v, A)
  u .= mod.(u, moduli)
  return u'
end


@inline function __neg_mod!(u::S, v::S, moduli::S) where {S<:Vector{ZZRingElem}}
  #@assert length(u) == length(v)
  return mod!.(neg!.(u,v), moduli)
end

@inline function __neg_mod!(u::S, v, moduli::S) where {S<:LinearAlgebra.Adjoint{Int, Vector{Int}}}
  #@assert length(u) == length(v)
  #for i in eachindex(v)
  #  @inbounds u[i] = mod(-v[i], moduli[i])
  #end
  u' .= mod!.(neg!.(u',v), moduli')
  return u'
end

@inline __not_adj(x::Vector{ZZRingElem}) = x
@inline __not_adj(x) = x'

## Directly via enumeration

function short_vectors_with_condition_direct(T::Type,
                                      L::ZZLat;
                                      search_fixed_vectors::Bool=true)
  proj, target_proj_root_inv, target_norms, denoms, grams = _short_vectors_with_condition_preprocessing(L)
  return _short_vectors_with_condition_direct(T, L, proj, target_proj_root_inv, target_norms, denoms, grams; search_fixed_vectors)
end

function _short_vectors_with_condition_direct(T::Type{Int},
                                      L::ZZLat,
                                      proj::Vector{QQMatrix}, target_invariant::Vector{Tuple{Vector{QQFieldElem}, Vector{ZZRingElem}}},
                                      target_norms::Vector{Vector{ZZRingElem}},
                                      denoms::Vector{ZZRingElem}, grams::Vector{ZZMatrix};
                                      search_fixed_vectors::Bool=true)
  denoms_Int = Int.(denoms)
  target_norms_Int = Vector{Int}[Int.(i) for i in target_norms]
  target_invariant_Int = [(i[1],Int.(i[2])) for i in target_invariant]
  return _short_vectors_with_condition_direct_integral(L,
                                           proj,
                                           target_invariant_Int,
                                           target_norms_Int,
                                           denoms_Int,
                                           grams;
                                           search_fixed_vectors)

end

function _short_vectors_with_condition_direct_integral(L::ZZLat, proj::Vector{QQMatrix}, target_invariant, target_norms::Vector{Vector{CoeffType}}, denoms::Vector{CoeffType}, grams::Vector{ZZMatrix}; search_fixed_vectors::Bool=true) where {CoeffType <: Union{Int, ZZRingElem}}
  target_invariant = [(_canonicalize!(i[1]),i[2]) for i in deepcopy(target_invariant)]
  G = ZZ.(gram_matrix(L))
  M = Int(maximum(diagonal(G)))
  gramsint = [Matrix{Int}(g) for g in grams]
  sv = _short_vectors_gram_nolll_integral(FinckePohstInt, G, 0, M, nothing, one(ZZ), Int)
  targetinvs3 = Set((Rational{Int}.(v), Int.(n)) for (v, n) in target_invariant)
  targetinvs2 = Set{Tuple{Vector{Int}, Vector{Int}}}()
  for (v, n) in target_invariant
    vv, d = integral_split(v, ZZ)
    push!(targetinvs2, (push!(Int.(vv), Int(d)), n))
  end
  #targetinvs = Set(target_invariant)
  ww = zeros(Int, length(sv[1][1]))
  l = length(target_invariant[1][2])
  k = length(grams)
  www = zeros_array(QQ, nrows(G))
  projint, d = integral_split(proj[1], ZZ)
  projintt = Matrix(Matrix{Int}(projint)')
  projrat = Matrix{Rational{Int}}(proj[1])'
  wwwww = zeros(Int, nrows(G) + 1)
  nn = nrows(G)
  tempnorm = zeros(Int, k)
  tempnormshort = view(tempnorm, 1:l)

  res = Tuple{Vector{CoeffType}, Vector{Int}}[]
  resD = Dict{Vector{Rational{Int}}, Vector{ZZRingElem}}(w => zeros_array(ZZ, nn) for (w, _) in targetinvs3)
  resdict = Dict{Vector{QQFieldElem}, Vector{Vector{ZZRingElem}}}(QQ.(w) => Vector{ZZRingElem}[] for (w, _) in targetinvs3)
  resS = Dict{Vector{QQFieldElem}, Vector{ZZRingElem}}(QQ.(w) => zeros_array(ZZ, nn) for (w, _) in targetinvs3)

  for (v, _) in sv
    LinearAlgebra.mul!(view(wwwww, 1:nn), projintt, v)
    wwwww[nn + 1] = d
    gg = gcd(wwwww)

    if gg != 1
      for i in 1:nn+1
        wwwww[i] = divexact(wwwww[i], gg)
      end
    end
    _canonicalize_finckepohstint!(wwwww, nn)
    #@assert wwww == wwwww

    for i in 1:l
      tempnormshort[i] = dot(v, LinearAlgebra.mul!(ww, gramsint[i], v))
    end

    (wwwww, tempnormshort) in targetinvs2 || continue
    for i in (l + 1):k
      tempnorm[i] = Int(dot(v, LinearAlgebra.mul!(ww, gramsint[i], v)))
    end

    tempnorm in target_norms || continue
    _w = wwwww[1:nn].//wwwww[nn+1]
    _ww = _canonicalize!(QQ.(v) * proj[1])
    #@info _w == _ww
    #@info _w
    #@info _ww
    #@assert QQ.(_ww) == _w
    # this is the "real" invariant
    @assert (_w, tempnormshort) in targetinvs3
    resD[_w] = resD[_w] .+ v
    if _canonicalize!(QQ.(v) * proj[1]) == QQ.(v) * proj[1]
      if !iszero(_w)
        resS[_ww] = resS[_ww] .+ v
      end
      push!(resdict[_ww], v)
    else
      if !iszero(_w)
        resS[_ww] = resS[_ww] .+ (-v)
      end
      push!(resdict[_ww], -v)
    end
    push!(res, (v, copy(tempnorm)))
  end

  #return resD

  _, invbas = rref(proj[1])

  if search_fixed_vectors
    invrank, invbas = rref(proj[1])
    oldinvrank = invrank
    newinvvec = []
    totalnew = 0
    local T
    local TT
    while true
      for (k, v) in resS
        fl = can_solve(invbas, QQ.(v); side = :left)
        if !fl
          push!(newinvvec, v)
          invrank, invbas = rref(vcat(invbas, matrix(QQ, 1, ncols(invbas), QQ.(v))))
        end
      end
      found = invrank - oldinvrank
      totalnew += found
      if found == 0
        break
      end
      #@info found
      #@info totalnew
      T = saturate(hnf(matrix(identity.(newinvvec))))
      TT = transpose(lll(numerator(T * gram_matrix(L))))
      #@info size(T)
      resSS = typeof(resS)()
      for (k, vS) in resdict
        if iszero(k)
          continue
        end
        for v in vS
          knew = append!(zeros(eltype(k), totalnew), k)
          ii = _canonicalize!(ZZ.(v * TT))
          neg = true
          if ZZ.(v * TT) == ii
            neg = false
          end
          knew[1:totalnew] = ii
          if haskey(resSS, knew)
            resSS[knew] = resSS[knew] .+ (neg ? -v : v)
          else
            resSS[knew] = (neg ? -v : v)
          end
        end
      end
      resS = resSS
      oldinvrank = invrank
      # update gram matrices
    end

    if totalnew > 0
      for i in totalnew:-1:1 # reverse order because of pushfirst!
        t = TT[:,i:i]
        tG = t*transpose(t)
        pushfirst!(grams, tG)
      end

      res2 = copy(res)
      for i in 1:length(res2)
        v = res2[i][1]
        res2[i] = (v, [Int(dot(v, g * v)) for g in grams])
      end
      return res2, grams, TT, proj[1]
    end
  end

  #
  res = [(v, CoeffType[dot(v, g * v) for g in grams]) for (v, _) in res ]

  #return resD

  return res, grams, zero_matrix(ZZ, nrows(G), 0), proj[1]
end

# TODO: get rid of this once finckepost can deal with ZZRingElem
function __short_vectors(G::ZZMatrix, lb, ub)
  sv = __enumerate_gram(FinckePohstInt, G, lb, ub, Int, identity, identity, Int)
  #return __enumerate_gram(LatEnumCtx, G, lb, ub, QQFieldElem, identity, identity, QQFieldElem)
  return sv
end

#function __short_vectors(G::ZZMatrix, lb::ZZRingElem, ub::ZZRingElem)
#  return __enumerate_gram(LatEnumCtx, G, lb, ub, QQFieldElem, identity, identity, QQFieldElem)
#end

function _finckepohstint_shortest(G::ZZMatrix)
  @assert is_positive_entry(G,1,1)
  Glll, T = lll_gram_with_transform(G)
  ubInt = Int(minimum(diagonal(Glll)))
  fl, V = _finckepohstint(Glll, ubInt; dolll=false)
  @assert fl
  m = minimum(i[2] for i in V)
  if isone(T)
    return m, [i[1] for i in V if i[2] == m]
  else
    _T = [Int(i) for i in T]
    return m, [(i[1]'*_T)' for i in V if i[2] == m]
  end
end

function _finckepohstint_shortest(G::QQMatrix)
  _G, d  = integral_split(G,ZZ)
  m, V = _finckepohstint_shortest(_G)
  return QQ(m,d), V
end


function _shortest_vectors_gram_finckepostint(G::Union{QQMatrix,ZZMatrix})
  try
    return _finckepohstint_shortest(G)
  catch k
    k isa InexactError || rethrow(k)
    return _shortest_vectors_gram(G)
  end
end
