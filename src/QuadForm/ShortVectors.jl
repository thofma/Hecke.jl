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


function short_vectors_with_condition(L::ZZLat)
  proj, target_proj_root_inv, target_norms = _short_vectors_with_condition_preprocessing(L)
  return short_vectors_with_condition(L, proj, target_proj_root_inv, target_norms)
end

function _short_vectors_with_condition_preprocessing(L::ZZLat)
  proj = _invariant_projections(L)
  proj_root_inv,proj_root_coinv = _weyl_group(L)[4]
  @assert proj[1] == proj_root_inv+proj_root_coinv
  proj[1]= proj_root_coinv
  pushfirst!(proj, proj_root_inv)
  n = rank(L)
  z = zero_matrix(ZZ, 1, n)
  targets = ZZMatrix[]
  for i in 1:n
    ei = deepcopy(z)
    ei[i] = 1
    push!(targets, ei)
  end
  target_projections = [[t*p for p in proj] for t in targets]
  target_norms = [QQFieldElem[(i*gram_matrix(L)*transpose(i))[1] for i in t] for t in target_projections]
  target_proj_root_inv = [t[1] for t in target_projections]
  return proj, target_proj_root_inv, target_norms
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

"""
    _short_vectors_with_condition(L::ZZLat, proj::Vector{QQMatrix}, target_norms::Vector{Vector{QQFieldElem}})

Return all vectors ``v`` of ``L`` such that
proj[i](v)^2 = target_norms[i] for all i.
"""
function short_vectors_with_condition(L::ZZLat, proj::Vector{QQMatrix}, target_invariant, target_norms::Vector{Vector{QQFieldElem}})
#   perm = sortperm(proj;by=rank)
#   proj = proj[perm]
#   target_norms =[i[perm] for i in target_norms]
  @hassert :Lattice 1 isone(sum(proj))
  @hassert :Lattice 1 all(i^2==i for i in proj)
  n = rank(L)
  V = ambient_space(L)
  projL = [lattice(V, p; check=false, isbasis=false) for p in proj]
  # L1 < Sat(L1+L2) < .... < Sat(L1+...+Ln) = L
  z = zeros(QQFieldElem, n)
  flag_projection = proj[1]
  tmpZZ = ZZ()
  short_vectors1 = Tuple{Vector{QQFieldElem},Vector{QQFieldElem}}[(i[1,:],n[1:1]) for (i,n) in zip(target_invariant,target_norms)]
  unique!(short_vectors1) # different targets can have the same first projection
  k = length(proj)
  zeroQQ = zero(QQ)
  good = 0
  miss = 0
  tmpv = [zero(QQ)]
  for i in 2:k
    short_vectors2 = Tuple{Vector{QQFieldElem},Vector{QQFieldElem}}[]
    flag_projection = flag_projection + proj[i]
    Lflag = lattice(V, flag_projection; isbasis=false, check=false)
    flag_projectionZ = coordinates(flag_projection, Lflag)
    tmp = zeros_array(QQ, ncols(flag_projectionZ))
    tmp2 = zeros_array(QQ, n)
    target_norm_i = Set(n[i] for n in target_norms)
    target_norm = Set(n[1:i] for n in target_norms)
    #@info target_norm
    mi = minimum(target_norm_i)
    ma = maximum(target_norm_i)
    if zeroQQ in target_norm_i
      # make up for the fact that short_vectors returns only non-zero vectors.
      for (b, normb) in short_vectors1
        # we want to look at norm_a_b = vcat(normb,[zero(QQ)]), but this allocates too much
        # we want to check properties of [normb..., zeroQQ]
        # we push! zeroQQ to normb and call it norm_a_b
        # if it is good, we take a copy of this
        # if not, we pop zeroQQ from it
        norm_a_b = push!(normb, zeroQQ)
        if !(norm_a_b in target_norm)
          pop!(norm_a_b)
          continue
        end
        if _is_product_integral(b, flag_projectionZ, tmpv, tmpZZ)
        # if _is_integral(mul!(tmp, b, flag_projectionZ), tmpZZ)
          push!(short_vectors2, (b, copy(norm_a_b)))
        end
        pop!(norm_a_b)
      end
    end
    a = zeros_array(QQ, ncols(basis_matrix(projL[i])))
    for (s, q) in _short_vectors_gram(LatEnumCtx, gram_matrix(projL[i]), mi, ma)
      q in target_norm_i || continue
      a = mul!(a, s, basis_matrix(projL[i])) # a = s*basis_matrix(projL[i])
      for (b, normb) in short_vectors1
        #norm_a_b = vcat(normb,[q])
        norm_a_b = push!(normb, q)
        if !(norm_a_b in target_norm)
          pop!(norm_a_b)
          continue
        end
        c = add!(tmp2, b, a)
        #if _is_integral(mul!(tmp, c, flag_projectionZ), tmpZZ)
        if _is_product_integral(c, flag_projectionZ, tmpv, tmpZZ)
          push!(short_vectors2, (deepcopy(c), copy(norm_a_b)))
        end
        c = sub!(tmp2, b, a)
        #if _is_integral(mul!(tmp, c, flag_projectionZ), tmpZZ)
        if _is_product_integral(c, flag_projectionZ, tmpv, tmpZZ)
          push!(short_vectors2, (deepcopy(c), copy(norm_a_b)))
        end
        pop!(norm_a_b)
      end
    end
    short_vectors1 = short_vectors2
  end
  @hassert :Lattice 1 all(matrix(QQ, 1, length(i),i)*proj[1] in target_invariant for (i,_) in short_vectors1)
  @hassert :Lattice 1 all([[(j*gram_matrix(L)*transpose(j))[1] for j in [matrix(QQ, 1, length(i),i)*p for p in proj]] in target_norms for (i,_) in short_vectors1])
  return short_vectors1
end

function _is_integral(x::Vector{QQFieldElem}, tmp::ZZRingElem)
  return all(isone(denominator!(tmp, i)) for i in x)
end
