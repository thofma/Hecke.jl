################################################################################
#
#  Eisenstein reduction of positive definite ternary quadratic forms
#
#  Equation, theorem and page numbers are those of [Dic30], Chapter XI, in
#  the 1957 Chelsea reprint, which reproduces the first edition. Throughout,
#  the Gram matrix [a t s; t b r; s r c] stands for Dickson's form (13),
#  a*x^2 + b*y^2 + c*z^2 + 2*r*y*z + 2*s*x*z + 2*t*x*y.
#
################################################################################

# Coefficients (a, b, c, r, s, t) of Dickson's form (13), so that the Gram
# matrix is [a t s; t b r; s r c].
struct _TernaryCoefficients{E}
  a::E
  b::E
  c::E
  r::E
  s::E
  t::E
end

# The rows of the transform, or nothing when it is not tracked.
const _TernaryRows{E} = Union{Nothing, NTuple{3, NTuple{3, E}}}

# A machine integer whose arithmetic throws OverflowError instead of wrapping.
# The reduction runs on it first and falls back to a wider type on overflow.
struct _TernaryWord{T <: Union{Int64, Int128}}
  v::T
end

################################################################################
#
#  Gram matrices
#
################################################################################

@doc raw"""
    is_eisenstein_reduced(G::MatElem{ZZRingElem}; check::Bool = true) -> Bool

Return whether the positive definite ternary quadratic form with Gram matrix
$G$ is reduced in the sense of Eisenstein [Dic30](@cite), Theorem 103.

The matrix

```math
G = \begin{pmatrix} a & t & s \\ t & b & r \\ s & r & c \end{pmatrix}
```

is read as the form $ax^2 + by^2 + cz^2 + 2ryz + 2sxz + 2txy$. It is reduced
if $r, s, t$ are all positive or all nonpositive, and

- $a \leq b \leq c$;
- $a \geq |2t|$, $a \geq |2s|$ and $b \geq |2r|$;
- $a + b + 2r + 2s + 2t \geq 0$;
- if $r, s, t > 0$: $s \leq 2r$ if $a = 2t$, $t \leq 2r$ if $a = 2s$, and
  $t \leq 2s$ if $b = 2r$;
- if $r, s, t \leq 0$: $s = 0$ if $a = -2t$, $t = 0$ if $a = -2s$, $t = 0$
  if $b = -2r$, and $a + 2s + t \leq 0$ if $a + b + 2r + 2s + 2t = 0$;
- $|r| \leq |s|$ if $a = b$, and $|s| \leq |t|$ if $b = c$.

These are Dickson's conditions (16)-(18), (25), (26) and (41). The conditions
on the boundary cases, where one of the inequalities is an equality, make the
reduced form unique: every positive definite ternary form is equivalent under
$\mathrm{GL}_3(\mathbf{Z})$ to exactly one reduced form [Dic30](@cite),
Theorem 104, which [`eisenstein_reduction`](@ref) returns.

If `check` is `true`, it is tested that $G$ is a symmetric, positive definite
$3 \times 3$ matrix.

# Examples

```jldoctest
julia> G = ZZ[23 34 68; 34 68 102; 68 102 204];

julia> is_eisenstein_reduced(G)
false

julia> is_eisenstein_reduced(eisenstein_reduction(G))
true
```
"""
function is_eisenstein_reduced(G::MatElem{ZZRingElem}; check::Bool = true)
  if check
    @req nrows(G) == 3 && ncols(G) == 3 "Gram matrix must be 3x3"
    @req is_symmetric(G) "Gram matrix must be symmetric"
    # Sylvester's criterion
    @req G[1, 1] > 0 && G[1, 1] * G[2, 2] - G[1, 2]^2 > 0 && det(G) > 0 (
      "Gram matrix must be positive definite")
  end
  f = _TernaryCoefficients(G[1, 1], G[2, 2], G[3, 3], G[2, 3], G[1, 3], G[1, 2])
  return _satisfies_theorem_103(f)
end

@doc raw"""
    eisenstein_reduction(G::MatElem{ZZRingElem}; check::Bool = true)
      -> ZZMatrix

Return the Gram matrix of the Eisenstein reduced form equivalent to the
positive definite ternary quadratic form with Gram matrix $G$.

Equivalent forms have the same reduction [Dic30](@cite), Theorem 104, so two
positive definite ternary forms are equivalent under
$\mathrm{GL}_3(\mathbf{Z})$ if and only if their reductions are equal. See
[`is_eisenstein_reduced`](@ref) for the conditions and how $G$ is read.

If `check` is `true`, it is tested that $G$ is a symmetric $3 \times 3$
matrix. A form that is not positive definite raises an `ArgumentError` in
either case.

# Examples

```jldoctest
julia> G = ZZ[23 34 68; 34 68 102; 68 102 204];

julia> eisenstein_reduction(G)
[ 3    -1    -1]
[-1    23   -11]
[-1   -11    23]
```
"""
function eisenstein_reduction(G::MatElem{ZZRingElem}; check::Bool = true)
  if check
    @req nrows(G) == 3 && ncols(G) == 3 "Gram matrix must be 3x3"
    @req is_symmetric(G) "Gram matrix must be symmetric"
  end
  return first(_eisenstein_reduce(G, Val(false)))
end

@doc raw"""
    eisenstein_reduction_with_transform(G::MatElem{ZZRingElem};
                                        check::Bool = true)
      -> ZZMatrix, ZZMatrix

Return the Eisenstein reduction $R$ of the positive definite ternary quadratic
form with Gram matrix $G$, see [`eisenstein_reduction`](@ref), and a matrix
$U \in \mathrm{GL}_3(\mathbf{Z})$ with $U G U^T = R$.

The rows of $U$ are the reduced basis, as in
`lll_gram_indef_with_transform`. The form $R$ is unique, but $U$ is
not when the form has automorphisms other than $\pm 1$.

If `check` is `true`, it is tested that $G$ is a symmetric $3 \times 3$
matrix. A form that is not positive definite raises an `ArgumentError` in
either case.

# Examples

```jldoctest
julia> G = ZZ[23 34 68; 34 68 102; 68 102 204];

julia> R, U = eisenstein_reduction_with_transform(G);

julia> U * G * transpose(U) == R
true

julia> abs(det(U))
1
```
"""
function eisenstein_reduction_with_transform(G::MatElem{ZZRingElem};
                                             check::Bool = true)
  if check
    @req nrows(G) == 3 && ncols(G) == 3 "Gram matrix must be 3x3"
    @req is_symmetric(G) "Gram matrix must be symmetric"
  end
  return _eisenstein_reduce(G, Val(true))
end

################################################################################
#
#  Lattices
#
################################################################################

@doc raw"""
    is_eisenstein_reduced(L::ZZLat) -> Bool

Return whether the Gram matrix of the basis of the positive definite lattice
$L$ of rank 3 is Eisenstein reduced, see
[`is_eisenstein_reduced(::MatElem{ZZRingElem})`](@ref).
"""
function is_eisenstein_reduced(L::ZZLat)
  @req rank(L) == 3 "Lattice must have rank 3"
  @req is_positive_definite(L) "Lattice must be positive definite"
  M, _ = _integral_split_gram(L)
  return is_eisenstein_reduced(M; check = false)
end

@doc raw"""
    eisenstein_reduction(L::ZZLat; same_ambient::Bool = true) -> ZZLat

Return the lattice $L$, which must be positive definite of rank 3, with a
basis whose Gram matrix is Eisenstein reduced, see
[`eisenstein_reduction(::MatElem{ZZRingElem})`](@ref).

The Gram matrix of the result determines $L$ up to isometry: two such lattices
are isometric if and only if the Gram matrices of their reductions are equal.

By default, the result lies in the ambient space of $L$. This can be disabled
by setting `same_ambient = false`.

# Examples

```jldoctest
julia> L = integer_lattice(; gram = ZZ[23 34 68; 34 68 102; 68 102 204]);

julia> gram_matrix(eisenstein_reduction(L))
[ 3    -1    -1]
[-1    23   -11]
[-1   -11    23]
```
"""
function eisenstein_reduction(L::ZZLat; same_ambient::Bool = true)
  @req rank(L) == 3 "Lattice must have rank 3"
  @req is_positive_definite(L) "Lattice must be positive definite"
  M, d = _integral_split_gram(L)
  R, U = _eisenstein_reduce(M, Val(true))
  if same_ambient
    return lattice(ambient_space(L), U * basis_matrix(L); isbasis = true,
                   check = false)
  end
  return integer_lattice(; gram = QQ(1, d) * R, check = false)
end

################################################################################
#
#  Theorem 103
#
################################################################################

# Theorem 103 of [Dic30], p. 171, on the coefficients of form (13): r, s, t
# all positive (sigma = 1) or all nonpositive (sigma = -1), and (16)-(18),
# (25), (26) with (26_4), and (41). The printed text reads "(16)-(28)"; the
# conditions meant are (16)-(18), the ones Lemma 1 on p. 166 states.
function _satisfies_theorem_103(f::_TernaryCoefficients{E}) where {E}
  a, b, c, r, s, t = f.a, f.b, f.c, f.r, f.s, f.t
  z = zero(a)
  # (16), for a positive form
  (z < a && a <= b && b <= c) || return false
  positive = z < r && z < s && z < t
  positive || (r <= z && s <= z && t <= z) || return false
  r2, s2, t2 = r + r, s + s, t + t
  # (17), which reads a >= 2*sigma*t, a >= 2*sigma*s, b >= 2*sigma*r
  (abs(t2) <= a && abs(s2) <= a && abs(r2) <= b) || return false
  # (18); for sigma = 1 it follows from (16) and (17)
  diagonal = a + b + r2 + s2 + t2
  z <= diagonal || return false
  if positive
    # (25)
    a == t2 && r2 < s && return false
    a == s2 && r2 < t && return false
    b == r2 && s2 < t && return false
  else
    # (26), including (26_4)
    a == -t2 && s != z && return false
    a == -s2 && t != z && return false
    b == -r2 && t != z && return false
    diagonal == z && z < a + s2 + t && return false
  end
  # (41)
  a == b && abs(s) < abs(r) && return false
  b == c && abs(t) < abs(s) && return false
  return true
end

################################################################################
#
#  Arithmetic
#
################################################################################

# The reduction of G, and with Val(true) the transform. Runs in Int64, then in
# Int128, then in ZZRingElem, moving on only when the narrower arithmetic
# overflows; each attempt starts again from G.
function _eisenstein_reduce(G::MatElem{ZZRingElem}, track::Val)
  scratch = ZZRingElem()
  small = true
  medium = true
  for (i, j) in ((1, 1), (2, 2), (3, 3), (2, 3), (1, 3), (1, 2))
    x = _ternary_entry!(scratch, G, i, j)
    small &= fits(Int64, x)
    medium &= nbits(x) < 127
  end
  if small
    try
      f = _ternary_word_coefficients(Int64, G)
      return _ternary_result(_reduce_coefficients(f, track)...)
    catch err
      err isa OverflowError || rethrow()
    end
  end
  if medium
    try
      f = _ternary_word_coefficients(Int128, G)
      return _ternary_result(_reduce_coefficients(f, track)...)
    catch err
      err isa OverflowError || rethrow()
    end
  end
  f = _TernaryCoefficients(G[1, 1], G[2, 2], G[3, 3], G[2, 3], G[1, 3], G[1, 2])
  return _ternary_result(_reduce_coefficients(f, track)...)
end

# G[i, j], written into scratch where the matrix type allows it. The bounds
# are checked here because getindex! does not check them.
function _ternary_entry!(scratch::ZZRingElem, G::ZZMatrix, i::Int, j::Int)
  (i <= nrows(G) && j <= ncols(G)) || throw(BoundsError(G, (i, j)))
  getindex!(scratch, G, i, j)
  return scratch
end

function _ternary_entry!(scratch::ZZRingElem, G::MatElem{ZZRingElem}, i::Int,
                         j::Int)
  return G[i, j]
end

# The coefficients of G as checked machine integers of type T; every entry
# must fit in T.
function _ternary_word_coefficients(::Type{T},
                                    G::MatElem{ZZRingElem}) where {T}
  scratch = ZZRingElem()
  entry(i::Int, j::Int) = _TernaryWord{T}(T(_ternary_entry!(scratch, G, i, j)))
  return _TernaryCoefficients(entry(1, 1), entry(2, 2), entry(3, 3),
                              entry(2, 3), entry(1, 3), entry(1, 2))
end

# Arithmetic on _TernaryWord. Every operation that can leave the range of T
# throws OverflowError.
Base.:+(x::_TernaryWord{T}, y::_TernaryWord{T}) where {T} =
  _TernaryWord{T}(Base.Checked.checked_add(x.v, y.v))
Base.:-(x::_TernaryWord{T}, y::_TernaryWord{T}) where {T} =
  _TernaryWord{T}(Base.Checked.checked_sub(x.v, y.v))
Base.:-(x::_TernaryWord{T}) where {T} =
  _TernaryWord{T}(Base.Checked.checked_neg(x.v))
Base.:*(x::_TernaryWord{T}, y::_TernaryWord{T}) where {T} =
  _TernaryWord{T}(Base.Checked.checked_mul(x.v, y.v))
Base.abs(x::_TernaryWord{T}) where {T} =
  _TernaryWord{T}(Base.Checked.checked_abs(x.v))
Base.fld(x::_TernaryWord{T}, y::_TernaryWord{T}) where {T} =
  _TernaryWord{T}(Base.Checked.checked_fld(x.v, y.v))
Base.:<(x::_TernaryWord{T}, y::_TernaryWord{T}) where {T} = x.v < y.v
Base.:<=(x::_TernaryWord{T}, y::_TernaryWord{T}) where {T} = x.v <= y.v
Base.:(==)(x::_TernaryWord{T}, y::_TernaryWord{T}) where {T} = x.v == y.v
Base.zero(x::_TernaryWord{T}) where {T} = _TernaryWord{T}(zero(T))
Base.one(x::_TernaryWord{T}) where {T} = _TernaryWord{T}(one(T))

################################################################################
#
#  The reduction
#
################################################################################

# The reduced coefficients of f and, with Val(true), the rows of the transform.
function _reduce_coefficients(f::_TernaryCoefficients{E},
                              ::Val{track}) where {E, track}
  o, z = one(f.a), zero(f.a)
  rows = track ? ((o, z, z), (z, o, z), (z, z, o)) : nothing
  f, rows = _successive_minima_basis(f, rows)
  return _select_reduced(f, rows)
end

# A basis whose Gram matrix satisfies Dickson's (16), (17) and the four
# diagonal inequalities of p. 165, so a reduced fundamental parallelepiped in
# the sense of Theorem 101, p. 163: its diagonal is the successive minima.
#
# Each step replaces one basis vector by a strictly shorter one and leaves the
# other two alone, so the trace falls by at least one per step and the loop
# ends. On a form that is not positive definite a diagonal entry eventually
# drops to zero or below, which raises. A form that passes every test of the
# loop is positive definite: with |2t| <= a <= b the plane of the first two
# vectors is definite, the diagonal inequalities put the projection of the
# third into the Voronoi cell of the origin in that plane, whose squared
# circumradius is at most 2b/3, and so c <= det(G)/(ab - t^2) + 2b/3 forces
# det(G) > 0 once c >= b.
function _successive_minima_basis(f::_TernaryCoefficients{E},
                                  rows::_TernaryRows{E}) where {E}
  z = zero(f.a)
  while true
    f, rows = _sort_diagonal(f, rows)
    @req z < f.a "Gram matrix must be positive definite"
    a, b, c, r, s, t = f.a, f.b, f.c, f.r, f.s, f.t
    if a < abs(t + t)
      f, rows = _subtract_from_second(f, rows, _ternary_round(t, a))
      continue
    end
    if a < abs(s + s)
      f, rows = _subtract_first_from_third(f, rows, _ternary_round(s, a))
      continue
    end
    if b < abs(r + r)
      f, rows = _subtract_second_from_third(f, rows, _ternary_round(r, b))
      continue
    end
    # Q(v3 + e*v1 + d*v2) - c for the four signs e, d
    ab = a + b
    r2, s2, t2 = r + r, s + s, t + t
    best = ab + s2 + r2 + t2
    e, d = 1, 1
    x = ab + s2 - r2 - t2
    if x < best
      best, e, d = x, 1, -1
    end
    x = ab - s2 + r2 - t2
    if x < best
      best, e, d = x, -1, 1
    end
    x = ab - s2 - r2 + t2
    if x < best
      best, e, d = x, -1, -1
    end
    best < z || return f, rows
    f, rows = _add_diagonal(f, rows, best, e, d)
  end
end

# The integer nearest to x/y, rounding halves up; y > 0. The remainder
# x - q*y lies in [-y/2, y/2).
function _ternary_round(x::E, y::E) where {E}
  return fld(x + x + y, y + y)
end

# Reorders the basis so that a <= b <= c, Dickson's (16).
function _sort_diagonal(f::_TernaryCoefficients{E},
                        rows::_TernaryRows{E}) where {E}
  if f.b < f.a
    f = _TernaryCoefficients(f.b, f.a, f.c, f.s, f.r, f.t)
    rows = _ternary_permute(rows, 2, 1, 3)
  end
  if f.c < f.b
    f = _TernaryCoefficients(f.a, f.c, f.b, f.r, f.t, f.s)
    rows = _ternary_permute(rows, 1, 3, 2)
    if f.b < f.a
      f = _TernaryCoefficients(f.b, f.a, f.c, f.s, f.r, f.t)
      rows = _ternary_permute(rows, 2, 1, 3)
    end
  end
  return f, rows
end

_ternary_permute(rows::Nothing, i::Int, j::Int, k::Int) = nothing

function _ternary_permute(rows::NTuple{3, NTuple{3, E}}, i::Int, j::Int,
                          k::Int) where {E}
  return (rows[i], rows[j], rows[k])
end

# u - k*w, for rows of the transform.
function _ternary_row_sub(u::NTuple{3, E}, k::E, w::NTuple{3, E}) where {E}
  return (u[1] - k * w[1], u[2] - k * w[2], u[3] - k * w[3])
end

# v2 -> v2 - q*v1.
function _subtract_from_second(f::_TernaryCoefficients{E},
                               rows::_TernaryRows{E},
                               q::E) where {E}
  a, t = f.a, f.t
  g = _TernaryCoefficients(a, f.b - q * (t + t - q * a), f.c, f.r - q * f.s,
                           f.s, t - q * a)
  rows === nothing && return g, nothing
  return g, (rows[1], _ternary_row_sub(rows[2], q, rows[1]), rows[3])
end

# v3 -> v3 - q*v1.
function _subtract_first_from_third(f::_TernaryCoefficients{E},
                                    rows::_TernaryRows{E},
                                    q::E) where {E}
  a, s = f.a, f.s
  g = _TernaryCoefficients(a, f.b, f.c - q * (s + s - q * a), f.r - q * f.t,
                           s - q * a, f.t)
  rows === nothing && return g, nothing
  return g, (rows[1], rows[2], _ternary_row_sub(rows[3], q, rows[1]))
end

# v3 -> v3 - q*v2.
function _subtract_second_from_third(f::_TernaryCoefficients{E},
                                     rows::_TernaryRows{E},
                                     q::E) where {E}
  b, r = f.b, f.r
  g = _TernaryCoefficients(f.a, b, f.c - q * (r + r - q * b), r - q * b,
                           f.s - q * f.t, f.t)
  rows === nothing && return g, nothing
  return g, (rows[1], rows[2], _ternary_row_sub(rows[3], q, rows[2]))
end

# v3 -> v3 + e*v1 + d*v2 with e, d in {1, -1}, where delta = Q(v3') - c.
function _add_diagonal(f::_TernaryCoefficients{E},
                       rows::_TernaryRows{E},
                       delta::E, e::Int, d::Int) where {E}
  a, b, t = f.a, f.b, f.t
  s = e == 1 ? f.s + a : f.s - a
  s = d == 1 ? s + t : s - t
  r = e == 1 ? f.r + t : f.r - t
  r = d == 1 ? r + b : r - b
  g = _TernaryCoefficients(a, b, f.c + delta, r, s, t)
  rows === nothing && return g, nothing
  u1, u2, u3 = rows
  w = ntuple(i -> (e == 1 ? u3[i] + u1[i] : u3[i] - u1[i]) +
                  (d == 1 ? u2[i] : -u2[i]), 3)
  return g, (u1, u2, w)
end

# The coefficient vectors with entries in {-1, 0, 1}, one of each pair +-u.
const _TERNARY_UNIT_VECTORS = (
  (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, -1, 0), (1, 0, 1),
  (1, 0, -1), (0, 1, 1), (0, 1, -1), (1, 1, 1), (1, 1, -1), (1, -1, 1),
  (1, -1, -1))

# The Eisenstein reduced form equivalent to f, which must be the output of
# _successive_minima_basis, and the matching rows of the transform.
#
# Every form satisfying Theorem 103 satisfies (16)-(18), so by p. 165 and
# Theorem 101 its basis is a reduced parallelepiped and its diagonal is that
# of f, the successive minima. Relative to the basis v1, v2, v3 of f, each
# vector of such a basis has coordinates in {-1, 0, 1}. In the plane of v1,
# v2, which is Lagrange-Gauss reduced, a primitive vector of norm at most b is
# +-v1, +-v2 or +-v2 +- v1. Off it, a coordinate of size 2 or more on v3 costs
# at least 4(c - 2b/3) > c, and within the coset v3 + <v1, v2> the norm c is
# reached only at the vertices of the Delaunay triangles around the projection
# of v3. So the reduced form is the Gram matrix, made sign-normal, of a basis
# drawn from these 13 vectors with norms a, b, c, and by Theorem 104 the first
# such basis whose form satisfies Theorem 103 gives the only one.
function _select_reduced(f::_TernaryCoefficients{E},
                         rows::_TernaryRows{E}) where {E}
  g, signs = _sign_normal(f)
  _satisfies_theorem_103(g) && return g, _ternary_apply_signs(rows, signs)
  V = _TERNARY_UNIT_VECTORS
  # Gu[k] is G times the k-th vector, norms[k] its value under the form
  Gu = ntuple(k -> _gram_times(f, V[k]), Val(13))
  norms = ntuple(k -> _ternary_dot(V[k], Gu[k]), Val(13))
  for i in 1:13
    norms[i] == f.a || continue
    for j in 1:13
      (j != i && norms[j] == f.b) || continue
      t = _ternary_dot(V[j], Gu[i])
      for k in 1:13
        (k != i && k != j && norms[k] == f.c) || continue
        abs(_ternary_det(V[i], V[j], V[k])) == 1 || continue
        h = _TernaryCoefficients(f.a, f.b, f.c, _ternary_dot(V[k], Gu[j]),
                                 _ternary_dot(V[k], Gu[i]), t)
        g, signs = _sign_normal(h)
        _satisfies_theorem_103(g) || continue
        rows === nothing && return g, nothing
        new_rows = (_ternary_combine_rows(V[i], rows),
                    _ternary_combine_rows(V[j], rows),
                    _ternary_combine_rows(V[k], rows))
        return g, _ternary_apply_signs(new_rows, signs)
      end
    end
  end
  error("No Eisenstein reduced form among the bases of small coefficients")
end

# The sign changes of the basis vectors, as in section 80, p. 164, that make
# r, s, t all positive when r*s*t > 0 and all nonpositive otherwise; returns
# the new coefficients and the signs (e1, e2, e3), under which t, s, r are
# multiplied by e1*e2, e1*e3, e2*e3. With a zero among r, s, t the signs are
# not unique but the coefficients are.
function _sign_normal(f::_TernaryCoefficients{E}) where {E}
  z = zero(f.a)
  sr = _ternary_sign(f.r)
  ss = _ternary_sign(f.s)
  st = _ternary_sign(f.t)
  sigma = sr * ss * st > 0 ? 1 : -1
  e2 = st != 0 ? sigma * st : 1
  e3 = ss != 0 ? sigma * ss : 1
  if sr != 0
    if st == 0
      e2 = sigma * sr * e3
    elseif ss == 0
      e3 = sigma * sr * e2
    end
  end
  r, s, t = abs(f.r), abs(f.s), abs(f.t)
  if sigma < 0
    r, s, t = z - r, z - s, z - t
  end
  return _TernaryCoefficients(f.a, f.b, f.c, r, s, t), (1, e2, e3)
end

_ternary_sign(x) = x < zero(x) ? -1 : (zero(x) < x ? 1 : 0)

_ternary_apply_signs(rows::Nothing, signs::NTuple{3, Int}) = nothing

function _ternary_apply_signs(rows::NTuple{3, NTuple{3, E}},
                              signs::NTuple{3, Int}) where {E}
  return ntuple(i -> signs[i] == 1 ? rows[i] : map(-, rows[i]), 3)
end

# G*u for the Gram matrix G of f and u with entries in {-1, 0, 1}.
function _gram_times(f::_TernaryCoefficients{E}, u::NTuple{3, Int}) where {E}
  return (_ternary_combination(u, f.a, f.t, f.s),
          _ternary_combination(u, f.t, f.b, f.r),
          _ternary_combination(u, f.s, f.r, f.c))
end

# u[1]*x + u[2]*y + u[3]*z for u with entries in {-1, 0, 1}.
function _ternary_combination(u::NTuple{3, Int}, x::E, y::E, z::E) where {E}
  return _ternary_term(u[1],
                       _ternary_term(u[2],
                                     _ternary_term(u[3], zero(x), z), y), x)
end

_ternary_term(k::Int, acc::E, x::E) where {E} =
  k == 0 ? acc : (k == 1 ? acc + x : acc - x)

_ternary_dot(u::NTuple{3, Int}, w::NTuple{3, E}) where {E} =
  _ternary_combination(u, w...)

function _ternary_det(u::NTuple{3, Int}, v::NTuple{3, Int}, w::NTuple{3, Int})
  return u[1] * (v[2] * w[3] - v[3] * w[2]) -
         u[2] * (v[1] * w[3] - v[3] * w[1]) +
         u[3] * (v[1] * w[2] - v[2] * w[1])
end

# The row u[1]*rows[1] + u[2]*rows[2] + u[3]*rows[3], u in {-1, 0, 1}^3.
function _ternary_combine_rows(u::NTuple{3, Int},
                               rows::NTuple{3, NTuple{3, E}}) where {E}
  return ntuple(i -> _ternary_combination(u, rows[1][i], rows[2][i],
                                          rows[3][i]), 3)
end

# The output matrices, from coefficients and rows in any of the arithmetics.
_ternary_result(f::_TernaryCoefficients, rows::Nothing) =
  (_ternary_gram_matrix(f), nothing)

function _ternary_result(f::_TernaryCoefficients{E},
                         rows::NTuple{3, NTuple{3, E}}) where {E}
  U = zero_matrix(ZZ, 3, 3)
  for i in 1:3, j in 1:3
    U[i, j] = _ternary_integer(rows[i][j])
  end
  return (_ternary_gram_matrix(f), U)
end

function _ternary_gram_matrix(f::_TernaryCoefficients)
  R = zero_matrix(ZZ, 3, 3)
  R[1, 1] = _ternary_integer(f.a)
  R[2, 2] = _ternary_integer(f.b)
  R[3, 3] = _ternary_integer(f.c)
  R[2, 3] = R[3, 2] = _ternary_integer(f.r)
  R[1, 3] = R[3, 1] = _ternary_integer(f.s)
  R[1, 2] = R[2, 1] = _ternary_integer(f.t)
  return R
end

_ternary_integer(x::_TernaryWord) = x.v
_ternary_integer(x::ZZRingElem) = x
