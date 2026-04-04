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
    return Vector{ZZRingElem}[]
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
    successive_minima_with_vectors(L::ZZLat) -> Vector{QQFieldElem}, Vector{ZZRingElem}

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
  if rank(L) == 0
    return Int[]
  end
  n = rank(L)
  m = maximum(diagonal(gram_matrix(lll(L))); init = zero(ZZ))
  S = short_vectors(L, m)
  sort!(S; by = x -> x[2])
  mi = S[1][2]
  cur_mi = mi
  res = QQFieldElem[cur_mi]
  resv = [S[1][1]]
  cur_i = findlast(x -> x[2] == mi, S)
  B = echelon_form(matrix(QQ, [x[1] for x in view(S, 1:cur_i)]); trim = true)
  while length(res) < n
    cur_mi = S[cur_i + 1][2]
    next_i = findlast(x -> x[2] == cur_mi, S)
    @assert next_i > cur_i
    # the following constructs a potential large marix
    # better would be a "streaming" version which takes as input only the vector
    # but we don't have this for rational matrices
    # (we only care about rank = dimension of rational span)
    B = echelon_form(vcat(B, matrix(QQ, [x[1] for x in view(S, cur_i+1:next_i)])); trim = true)
    if nrows(B) > length(res)
      for _ in 1:(nrows(B) - length(res))
        push!(res, cur_mi)
        push!(resv, S[cur_i + 1][1])
      end
    end
    cur_i = next_i
  end
  return res, resv
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
    short_vectors_with_condition(L::ZZLat; search_new_invariant_vectors::Bool) -> Tuple{<:Vector, <:Vector}, Vector{ZZMatrix}

Return a list of vectors, that contains the orbits of the standard basis vectors under the reduced automorphism group $\mathrm{Aut}(L, \rho)$.
together with a list of $\mathrm{Aut}(L, \rho)$-invariant gram matrices where $\rho$ is a Weyl vector of the root sublattice of `L`.

# Input
- `search_new_invariant_vectors::Bool` -- take sums of vectors with the same invariants to obtain new invariant vectors. Use it to refine the invariant. Rinse and repeat.

# Output:
- a tuple `(V, G)` consiting of:
- a list of tuples `V = [(v_1, n_1), (v_2, n_2), ....]`; where `v_i` is a point of `L` and `n_i` an $\mathrm{Aut}(L,\rho)$ invariant of `v_i`, called its "norm".
- a list of symmetric integer matrices `G = [G_1, ..., G_k]`;
such that:
- `dot(v_i,G[j]*v_i) == (n_i)[j]` for all `i` in `1,...,rank(L)` and `j` in `1,...,k`.
- the standard basis vectors and their norms with respect to `G` are contained in `V`
"""
function short_vectors_with_condition(L::ZZLat;
                                      search_new_invariant_vectors::Bool=false)
  return short_vectors_with_condition(QQFieldElem, L; search_new_invariant_vectors)
end

function short_vectors_with_condition(T::Type,
                                      L::ZZLat;
                                      search_new_invariant_vectors::Bool=true)
  proj, target_proj_root_inv, target_norms, denoms, grams = _short_vectors_with_condition_preprocessing(L)
  return _short_vectors_with_condition(T, L, proj, target_proj_root_inv, target_norms, denoms, grams; search_new_invariant_vectors)
end

function _short_vectors_with_condition_preprocessing(L::ZZLat)
  root_types, fundamental_roots = _root_lattice_recognition_fundamental(L)
  weyl_group_gens, grams, ord, (proj_root_inv, proj_root_coinv) = _weyl_group(L, root_types, fundamental_roots)
  return _short_vectors_with_condition_preprocessing(L::ZZLat, root_types, fundamental_roots, grams, proj_root_inv, proj_root_coinv)
end

function _short_vectors_with_condition_preprocessing(L::ZZLat,
                                                     root_types::Vector{Tuple{Symbol,Int}},
                                                     fundamental_roots::Vector{ZZMatrix},
                                                     grams::Vector{ZZMatrix},
                                                     proj_root_inv::QQMatrix,
                                                     proj_root_coinv::Vector{QQMatrix},
                                                     sort=:rank)
  n = rank(L)
  R = reduce(vcat, fundamental_roots; init=zero_matrix(ZZ, 0, rank(L)))
  Rperp = orthogonal_submodule(L, R*basis_matrix(L))
  LL, _ = _short_vector_generators_with_sublattice_2(Rperp; up_to_sign=true)
  pushfirst!(LL, lattice(ambient_space(L), R))
  proj = __projections(LL)
  @hassert :Lattice 1 proj[1] == proj_root_inv + sum(proj_root_coinv; init=zero_matrix(QQ, n, n))
  popfirst!(proj)
  proj = append!(proj_root_coinv, proj)
  pushfirst!(proj, proj_root_inv)
  w = length(grams)
  m = w + length(proj) - 1
  target_norms = Vector{ZZRingElem}[zeros_array(ZZ, m) for i in 1:n]
  denoms = [ZZ(1)]
  for i in 2:length(proj)
    p = proj[i]
    gram_pQQ = p*gram_matrix(L)*transpose(p)
    d = denominator(gram_pQQ)
    push!(grams, numerator(gram_pQQ))
    push!(denoms, d)
  end
  for k in 1:m
    for i in 1:n
      target_norms[i][k] = grams[k][i,i]
    end
  end
  # We take one representative up to sign.
  # Do we want this in the preprocessing or in short_vectors_with_condition?
  target_proj_root_inv = [(_canonicalize!(proj[1][i, :]),target_norms[i][1:w]) for i in 1:n]
  unique!(target_proj_root_inv)

  if sort == :rank
    # don't touch the first one
    p = sortperm([rank(proj[i]) for i in 2:length(proj)]; rev = false)
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
                                      search_new_invariant_vectors::Bool=true)
  denoms_Int = Int.(denoms)
  target_norms_Int = Vector{Int}[Int.(i) for i in target_norms]
  target_invariant_Int = [(i[1],Int.(i[2])) for i in target_invariant]
  return _short_vectors_with_condition_int(L,
                                           proj,
                                           target_invariant_Int,
                                           target_norms_Int,
                                           denoms_Int,
                                           grams;
                                           search_new_invariant_vectors)
end

function _short_vectors_with_condition(T::Type{QQFieldElem},
                                      L::ZZLat,
                                      proj::Vector{QQMatrix}, target_invariant::Vector{Tuple{Vector{QQFieldElem}, Vector{ZZRingElem}}},
                                      target_norms::Vector{Vector{ZZRingElem}},
                                      denoms::Vector{ZZRingElem},
                                      grams::Vector{ZZMatrix};
                                      search_new_invariant_vectors::Bool=true)
  return _short_vectors_with_condition_QQ(L, proj, target_invariant, target_norms, denoms, grams; search_new_invariant_vectors)
end

function _short_vectors_with_condition_QQ(L::ZZLat, proj::Vector{QQMatrix}, target_invariant, target_norms::Vector{Vector{ZZRingElem}}, denoms::Vector{ZZRingElem}, grams::Vector{ZZMatrix}; search_new_invariant_vectors::Bool=true)
  @hassert :Lattice 1 isone(sum(proj))
  @hassert :Lattice 1 all(i^2==i for i in proj)
  n = rank(L)

  # keeps track of the invariant subspace
  # built from invariant vectors discovered during the process and the input, i.e. the row span of proj[1]
  invariant_subspace_rank, invariant_subspace = rref(proj[1])
  invariant_subspace = invariant_subspace[1:invariant_subspace_rank, :]
  H = hnf!(numerator(invariant_subspace))
  new_invariant_subspace = zero_matrix(ZZ, 0, rank(L)) # keeps track of what is new
  T = zero_matrix(ZZ, n, 0)
  w0 = invariant_subspace_rank
  S = solve_init(invariant_subspace)

  V = ambient_space(L)
  projL = [lll(rescale(lattice(V, proj[i]; check=false, isbasis=false),denoms[i]; cached=false)) for i in 1:length(proj)]
  @assert all(is_integral(projL[i]) for i in 2:length(projL))
  # L1 < Sat(L1+L2) < .... < Sat(L1+...+Ln) = L
  flag_projection = proj[1]
  tmpZZ = ZZ()
  short_vectors1 = Dict{Vector{ZZRingElem},Vector{Vector{QQFieldElem}}}()
  for (a,b) in target_invariant
    if b in keys(short_vectors1)
      # different targets can have the same first projection
      if !(a in short_vectors1[b])
        push!(short_vectors1[b], a)
      end
    else
      short_vectors1[b]=[a]
    end
  end
  #unique!(short_vectors1)  # different targets can have the same first projection
  k = length(proj)
  w = length(target_norms[1]) - (k-1)
  zeroZZ = zero(ZZ)
  good = 0
  miss = 0
  vmat = zero_matrix(QQ, 1, n)
  tmp2 = zeros_array(QQ, n)
  tmp_invariant_vec = zeros_array(QQ, n)
  tmpv = zeros_array(QQ, n)
  Lflag = projL[1]
  for i in 2:k
    short_vectors2 = Dict{Vector{ZZRingElem},Vector{Vector{QQFieldElem}}}()
    for a in Set(n[1:w+i-1] for n in target_norms)
      short_vectors2[a] = Vector{QQFieldElem}[]
    end
    flag_projection = flag_projection + proj[i]
    #bigL = vcat(basis_matrix(Lflag), basis_matrix(projL[i]))
    Lflag = lattice(V, flag_projection; isbasis=false, check=false)
    #Lflag_in_bigL = ZZ.(solve(bigL, basis_matrix(Lflag); side=:left))
    #Sf, Tf, Uf = snf_with_transform(Lflag_in_bigL)
    flag_projectionZ = coordinates(flag_projection, Lflag)
    tmp = zeros_array(QQ, ncols(flag_projectionZ))
    target_norm_i = Set(n[w+i-1] for n in target_norms)
    r = nrows(invariant_subspace)
    target_norm = Dict{ZZRingElem, Set{Vector{ZZRingElem}}}()
    for n in target_norms
      a = n[w+i-1]
      b = n[1:w+i-2]
      if a in keys(target_norm)
        push!(target_norm[a], b)
      else
        target_norm[a] = Set([b])
      end
    end
    ma = maximum(target_norm_i)
    mi = minimum(i for i in target_norm_i if !iszero(i);init=ma)
    # prepare gluing data
    short_vectors1_extra = Dict{Tuple{Vector{ZZRingElem},ZZRingElem},Dict{Vector{ZZRingElem}, Vector{Vector{QQFieldElem}}}}()
    for k1 in keys(short_vectors1)
      for a in short_vectors1[k1]
        b = mul!(tmp, a, flag_projectionZ)
        d = _denominator(b)
        k2 = mod.(mul!.(b,d), d)
        # take into account that short_vectors returns only non-zero vectors.
        if zeroZZ in keys(target_norm) && k1 in target_norm[zeroZZ] && iszero(k2)
          push!(k1, zeroZZ)
          push!(short_vectors2[k1], deepcopy(a))
          pop!(k1)
        end
        k = (k2, d)
        if k in keys(short_vectors1_extra)
          D = short_vectors1_extra[k]
          if k1 in keys(D)
            push!(D[k1], a)
          else
            D[k1] = [a]
          end
        else
          short_vectors1_extra[k] = Dict(k1=>[a])
        end
      end
    end
    a = zeros_array(QQ, ncols(basis_matrix(projL[i])))
    Gi = ZZ.(gram_matrix(projL[i])) # already lll reduced
    for (s, q) in __enumerate_gram(LatEnumCtx, Gi, mi, ma, QQFieldElem, identity, identity, QQFieldElem)
      q in target_norm_i || continue
      a = mul!(a, s, basis_matrix(projL[i]))
      b = mul!(tmp, a, flag_projectionZ)
      d = _denominator(b)
      b = mod!.(mul!(b, d), d)
      k1plus = (b, d)
      k1minus = (mod!.(-b,d), d)
      if k1plus in keys(short_vectors1_extra)
        D = short_vectors1_extra[k1plus]
        for t in target_norm[q]
          t in keys(D) || continue
          Dt = D[t]
          push!(t, q)
          for b in Dt
            push!(short_vectors2[t], b-a)
          end
          pop!(t)
        end
      end
      if k1minus in keys(short_vectors1_extra)
        D = short_vectors1_extra[k1minus]
        for t in target_norm[q]
          t in keys(D) || continue
          iszero(t) && continue # avoid overcounting
          Dt = D[t]
          push!(t, q)
          for b in Dt
            push!(short_vectors2[t], b+a)
          end
          pop!(t)
        end
      end
    end
    if search_new_invariant_vectors
      tmpQQmat = zero_matrix(QQ, 1, n)
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
                                        H)
        found, invariant_subspace, new_invariant_subspace = abc
        iszero(found) && break
        # update the invariants
        T = ZZ.(new_invariant_subspace*gram_matrix(L))
        T = transpose(lll(T))
        @vprintln :Lattice 2 "T = $T"
        short_vectors2 = update_short_vector_invariants(short_vectors2, T, found)
      end
      found_this_round = nrows(invariant_subspace) - old_invariant_subspace_rank
      if found_this_round > 0
        # update target_norms
        t_old = t
        t = ncols(T)
        target_norms = [vcat(_canonicalize!(deepcopy(T[j, :])), target_norms[j][t_old+1:end]) for j in 1:nrows(T)]
        # filter what we do not need anymore
        invs = Set([target_norms[j][1:t+w0+i] for j in 1:nrows(T)])
        for k in keys(short_vectors2)
          k in invs && continue
          delete!(short_vectors2, k)
        end
      end
      w += found_this_round
    end
    short_vectors1 = short_vectors2
  end
  # assemble the output
  output = Vector{Tuple{Vector{QQFieldElem}, Vector{QQFieldElem}}}(undef, sum(length.(values(short_vectors1))))
  r = nrows(new_invariant_subspace)
  gZ = ZZ.(gram_matrix(L))
  for i in r:-1:1 # reverse order because of pushfirst!
    t = T[:,i:i]
    tG = t*transpose(t)
    pushfirst!(grams, tG)
  end
  i = 0
  for b in keys(short_vectors1)
    bret = copy(b)
    @inbounds for i in 1:r
      bret[i] = bret[i]^2
    end
    for z in short_vectors1[b]
      i = i+1
      output[i] = (_canonicalize!(z), bret)
    end
  end
  @vprintln :Lattice 2 "discovered an additional fixed subspace of rank $(nrows(new_invariant_subspace))"
  @vprintln :Lattice 1 "visible fixed subspace has rank $(nrows(invariant_subspace))"
  if get_assertion_level(:Lattice) > 1
    for (v, n) in output
      @assert all(dot(v * grams[i], v) == n[i] for i in 1:length(grams))
    end
  end
  return output, grams, T, proj[1]
end

function _short_vectors_with_condition_int(L::ZZLat, proj::Vector{QQMatrix}, target_invariant, target_norms::Vector{Vector{Int}}, denoms::Vector{Int}, grams::Vector{ZZMatrix}; search_new_invariant_vectors::Bool=true)
  @hassert :Lattice 1 isone(sum(proj))
  @hassert :Lattice 1 all(i^2==i for i in proj)
  k = length(proj)

  # keeps track of the invariant subspace
  # built from invariant vectors discovered during the process and the input, i.e. the row span of proj[1]
  invariant_subspace_rank, invariant_subspace = rref(proj[1])
  invariant_subspace = invariant_subspace[1:invariant_subspace_rank, :]
  H = hnf!(numerator(invariant_subspace))
  S = solve_init(invariant_subspace)
  new_invariant_subspace = zero_matrix(ZZ, 0, rank(L)) # keeps track of what is new
  n = rank(L)
  T = zero_matrix(ZZ, n, 0)
  w0 = invariant_subspace_rank
  w = length(target_norms[1]) - (k-1)
  V = ambient_space(L)
  projL = [lll(rescale(lattice(V, proj[i]; check=false, isbasis=false),denoms[i])) for i in 1:length(proj)]

  # L1 < Sat(L1+L2) < .... < Sat(L1+...+Ln) = L
  z = zeros(QQFieldElem, n)
  flag_projection = proj[1]
  tmpZZ = ZZ()
  short_vectors1 = Dict{Vector{Int},Vector{Tuple{LinearAlgebra.Adjoint{Int64, Vector{Int64}}, Int}}}()
  for j in 1:length(target_invariant)
    i, nn = target_invariant[j]
    tinvn, invd = integral_split(i, ZZ)
    v = (Int.(tinvn)', Int(invd))
    nn = Int.(nn[1:w])
    if nn in keys(short_vectors1)
      if !(v in short_vectors1[nn]) # different targets can have the same first projection
        push!(short_vectors1[nn], v)
      end
    else
      short_vectors1[nn]=[v]
    end
  end

  basismatprojL = Vector{Tuple{Matrix{Int}, Int}}(undef, k)
  for i in 1:k
    M = basis_matrix(projL[i])
    Mint = Matrix{Int}(numerator(M))
    Md = denominator(M)
    basismatprojL[i] = Mint, Md
  end
  tmp2 = zeros_array(QQ, n)
  tmp2_new = zeros(Int, n)'
  tmp2_new2 = zeros(Int, n)'
  tmp2_new3 = zeros(Int, n)'
  tmp_invariant_vec = zeros_array(ZZ, n)
  tmpQQmat = zero_matrix(QQ, 1, n)
  for i in 2:k
    short_vectors2 = Dict{Vector{Int}, Vector{Tuple{LinearAlgebra.Adjoint{Int, Vector{Int}}, Int}}}()
    for a in Set(n[1:w+i-1] for n in target_norms)
      short_vectors2[a] = Tuple{LinearAlgebra.Adjoint{Int, Vector{Int}}, Int}[]
    end

    flag_projection = flag_projection + proj[i]
    Lflag = lattice(V, flag_projection; isbasis=false, check=false)
    flag_projectionZ = coordinates(flag_projection, Lflag)
    flag_projectionZmat = Matrix{Int}(ZZ.(flag_projectionZ))
    tmp = zeros_array(QQ, ncols(flag_projectionZ))
    tmpforproj = zeros(Int, ncols(flag_projectionZ))'
    target_norm_i = Set(n[w+i-1] for n in target_norms)
    target_norm = Dict{Int, Set{Vector{Int}}}()
    for n in target_norms
      a = n[w+i-1]
      b = n[1:w+i-2]
      if a in keys(target_norm)
        push!(target_norm[a], b)
      else
        target_norm[a] = Set([b])
      end
    end
    #=
    # prepare gluing data
    short_vectors1_extra = Dict{Tuple{Matrix{Int},Int},Dict{Vector{Int}, Vector{Tuple{LinearAlgebra.Adjoint{Int, Vector{Int}}, Int}}}}()
    for k1 in keys(short_vectors1)
      for a in short_vectors1[k1]
        b = a[1]*flag_projectionZmat
        k2 = mod.(b, a[2])
        k = (k2, a[2])
        if k in keys(short_vectors1_extra)
          D = short_vectors1_extra[k]
          if k1 in keys(D)
            push!(D[k1], a)
          else
            D[k1] = [a]
          end
        else
          short_vectors1_extra[k] = Dict(k1=>[a])
        end
      end
    end
    =#

    ma = maximum(target_norm_i)
    mi = minimum(i for i in target_norm_i if !iszero(i);init=ma) #does this hurt or help?
    if 0 in keys(target_norm)
      for a in target_norm[0]
        SV = short_vectors1[a]
        push!(a, 0)
        for j in 1:length(SV)
          bb = SV[j]
          bb1, bb2 = bb
          isgood = true
          for i in 1:size(flag_projectionZmat, 2)
            if !is_zero(mod(bb1 * (@view flag_projectionZmat[:, i]), bb2))
              isgood = false
              break
            end
          end
          if isgood
            push!(short_vectors2[a], deepcopy(bb))
          end
        end
        pop!(a)
      end
    end
    bmat, bmatden = basismatprojL[i][1], basismatprojL[i][2]
    tmp4 = zeros(Int, size(bmat, 2))'
    Gi = ZZ.(gram_matrix(projL[i])) # already lll reduced
    for (s, qQQ) in __enumerate_gram(LatEnumCtx, Gi, mi, ma, QQFieldElem, identity, identity, Int) # no postprocessing
      q = Int(qQQ)
      q in target_norm_i || continue
      aa = LinearAlgebra.mul!(tmp4, s', bmat)
      for t in target_norm[q]
        SV = short_vectors1[t]
        push!(t, q)
        d = bmatden * first(SV)[2]
        for j in 1:length(SV)
          bb = SV[j]
          tmp2_new .= bmatden .* bb[1]
          tmp2_new2 .= bb[2] .* aa
          tmp2_new3 .= tmp2_new .+ tmp2_new2
          isgood = true
          for i in 1:length(tmpforproj)
            if !is_zero(mod(tmp2_new3 * (@view flag_projectionZmat[:, i]), d))
              isgood = false
              break
            end
          end
          if isgood
            push!(short_vectors2[t], (copy(tmp2_new3), d))
          end
          if !iszero(bb[1])
            tmp2_new3 .= tmp2_new .- tmp2_new2
            isgood = true
            for i in 1:length(tmpforproj)
              if !is_zero(mod(tmp2_new3 * (@view flag_projectionZmat[:, i]), d))
                isgood = false
                break
              end
            end
            if isgood
              push!(short_vectors2[t], (copy(tmp2_new3), d))
            end
          end
        end
        pop!(t)
      end
    end
    if search_new_invariant_vectors
      # compute invariant vectors by taking the sum of all vectors with the same invariant
      # if we find something refine the invariants and search anew
      old_invariant_subspace_rank = nrows(invariant_subspace)
      t = rank(new_invariant_subspace)
      @label search_invariants_int
      found, invariant_subspace, new_invariant_subspace = __search_invariant_subspaces!(short_vectors2, invariant_subspace, new_invariant_subspace, tmp_invariant_vec, tmpQQmat, H)
      # update the invariants
      if found > 0
        T = new_invariant_subspace*gram_matrix(L)
        T = transpose(lll(ZZ.(T)))
        # we cannot allow overflow in T here, because we do an exact division later
        ## TInt = [BigInt(x) % Int for x in numerator(T)]  #convert with overflow
        short_vectors2 = update_short_vector_invariants(short_vectors2, T, found)
        @goto search_invariants_int
      end
      found = rank(invariant_subspace) - old_invariant_subspace_rank

      if found > 0
        TInt = Matrix{Int}(T)
        # update target_norms
        t_old = t
        t = ncols(T)
        target_norms = [vcat(_canonicalize!(TInt[j, :]), target_norms[j][t_old+1:end]) for j in 1:nrows(T)]
        # filter what we do not need anymore
        invs = Set([target_norms[j][1:t+w0+i] for j in 1:nrows(T)])
        for k in keys(short_vectors2)
          k in invs && continue
          @vprintln :Lattice 5 "deleting vectors with key $k"
          delete!(short_vectors2, k)
        end
      end
      w += found
    end
    short_vectors1 = short_vectors2
  end
  r = nrows(new_invariant_subspace)
  gZ = ZZ.(gram_matrix(L))
  for i in r:-1:1  # reverse order because of pushfirst
    t = T[:,i:i]
    tG = t*transpose(t)
    pushfirst!(grams, tG)
  end
  i = 0
  output = Vector{Tuple{Vector{Int}, Vector{Int}}}(undef, sum(length.(values(short_vectors1))))
  for b in keys(short_vectors1)
    bret = copy(b)
    @inbounds for i in 1:r
      bret[i] = bret[i]^2
    end
    for (z, d) in short_vectors1[b]
      i = i+1
      @inbounds for j in 1:n
        z[j] = divexact(z[j], d)
      end
      output[i] = (_canonicalize!(z'), bret)
    end
  end
  @vprintln :Lattice 1 "discovered an additional fixed subspace of rank $(nrows(new_invariant_subspace))"
  @vprintln :Lattice 1 "visible fixed subspace has rank $(nrows(invariant_subspace))"
  if get_assertion_level(:Lattice) > 1
    for (v, n) in output
      @assert length(n) == length(grams)
      @assert all(dot(v * grams[i], v) == n[i] for i in 1:length(grams))
    end
    # check that we get the standard basis vectors
    ei = zeros(Int, n)
    for i in 1:n
      ei[i]=1
      @assert any(i[1]==ei for i in output)
      ei[i]=0
    end
  end
  return output, grams, T, proj[1]
end

function update_short_vector_invariants(D::S, T, found::Int) where {S<:Dict{Vector{Int}, Vector{Tuple{LinearAlgebra.Adjoint{Int64, Vector{Int64}}, Int}}}}
  Dnew = S()
  n = ncols(T)
  for k in keys(D)
    k_new = vcat(zeros(Int, found), k)
    for v in D[k]
      ii = _canonicalize!(v[1]' * T) # _canonicalize! allows us to consider this invariant up to sign
      k_new[1:n] = divexact.(ii, v[2]) # if there is an overflow elsewhere, this will likely throw an error
      if k_new in keys(Dnew)
        push!(Dnew[k_new], v)
      else
        Dnew[deepcopy(k_new)] = [v]
      end
    end
  end
  return Dnew
end

function update_short_vector_invariants(D::S, T, found::Int) where {S<:Dict{Vector{ZZRingElem}, Vector{Vector{QQFieldElem}}}}
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

#modifies tmp_vec and tmp_mat
function __search_invariant_subspaces!(D::Dict, invariant_subspace::QQMatrix, new_invariant_subspace::ZZMatrix, tmp_vec::Vector, tmp_mat::QQMatrix, H::ZZMatrix)
  S = solve_init(invariant_subspace)
  i1 = nrows(new_invariant_subspace)
  i2 = nrows(invariant_subspace)
  r1 = nrows(invariant_subspace)
  w = i2 - i1
  for k in keys(D)
    if nrows(invariant_subspace)==ncols(invariant_subspace)
      # everything invariant nothing more to do
      break
    end
    # the ones which do not have an invariant component are up to +-1 and sum to 0, discard them
    all(iszero(k[i]) for i in i1+1:i2) && continue
    # compute v = sum(D[k])
    # we cannot allow an overflow here
    v = ___sum(D[k]; init=tmp_vec)
    # copy to a matrix
    @inbounds for i in 1:length(v)
      tmp_mat[i] = v[i]
    end
    # Check if we discovered something new.
    if !can_solve(S, tmp_mat; side=:left)
      invariant_subspace = vcat(invariant_subspace, tmp_mat)
      rref!(invariant_subspace)
      new_invariant_subspace = vcat(new_invariant_subspace, numerator(tmp_mat))
      new_invariant_subspace = saturate(new_invariant_subspace)
      reduce_mod_hnf_ur!(new_invariant_subspace, H)
      S = solve_init(invariant_subspace)
    end
  end
  found = nrows(invariant_subspace) - r1
  return found, invariant_subspace, new_invariant_subspace
end

function ___sum(V::Vector{<:Tuple}; init::Vector)
  if eltype(init) === Int
    for i in 1:length(init)
      init[i] = 0
    end
  else
    init = zero!.(init)
  end
  c = first(V)[2]
  for i in V
    @assert c == i[2] # assert that everyone has the same denominator i[2]
    add!.(init, i[1]')
  end
  return init
end

function ___sum(V::Vector; init::Vector)
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
