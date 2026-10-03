################################################################################
#
#  ReconstructNumerics.jl : numerical helpers of the reconstruction
#
#  Sizes and relative radii of balls (the diagnostics in the info of the
#  reconstruction) and the square root of a form that is a square (the Cayley
#  cubic of the genus 4 reconstruction): a recurrence, Newton steps on the
#  midpoints and a rigorous enclosure. Independent of the genus; the kernels
#  are numerical_kernel (Numerics/NumericalKernel.jl).
#
################################################################################

################################################################################
#
#  Sizes and radii of balls (diagnostics)
#
################################################################################

_abs64(z::AcbFieldElem) = abs(RSR._c64(z))
_safe_log2(x::Float64) = x > 0 ? log2(x) : -Inf

# radius of a ball (upper bound in Float64)
_radius64(z::AcbFieldElem) = Float64(Hecke.radius(real(z))) + Float64(Hecke.radius(imag(z)))

# log2 of the largest radius relative to the largest midpoint: for vectors,
# matrices and polynomials the maximum over the entries of max radius / max
# |entry| (vectors of vectors: per vector)
_log2_relative_radius(z::AcbFieldElem) = _safe_log2(_radius64(z) / max(_abs64(z), 1e-300))
_log2_relative_radius(v::Vector{AcbFieldElem}) = _safe_log2(maximum(_radius64, v) / max(maximum(_abs64, v), 1e-300))
_log2_relative_radius(v::Vector{Vector{AcbFieldElem}}) = maximum(_log2_relative_radius, v)
_log2_relative_radius(v::Vector{<:MPolyRingElem}) = maximum(_log2_relative_radius, v)
_log2_relative_radius(M::AcbMatrix) = _log2_relative_radius([M[i, j] for i in 1:nrows(M) for j in 1:ncols(M)])
_log2_relative_radius(p::MPolyRingElem) = _log2_relative_radius(collect(coefficients(p)))

################################################################################
#
#  Square roots of sextic forms
#
################################################################################

# all exponent vectors of length n and total degree d
function _exponent_vectors(n::Int, d::Int)
  n == 1 && return [[d]]
  return [vcat([i], e) for i in d:-1:0 for e in _exponent_vectors(n - 1, d - i)]
end

function _polynomial_from_dict(R::MPolyRing, D::Dict{Vector{Int}, AcbFieldElem})
  ctx = MPolyBuildCtx(R)
  for (e, c) in D
    push_term!(ctx, c, e)
  end
  return finish(ctx)
end

# log2 of max |coefficient of F - H^2| / max |coefficient of F|
function _square_residual(F::Dict{Vector{Int}, AcbFieldElem}, H::Dict{Vector{Int}, AcbFieldElem})
  D = copy(F)
  for (e1, c1) in H, (e2, c2) in H
    e = e1 + e2
    D[e] = get(D, e, zero(c1)) - c1*c2
  end
  return _safe_log2(maximum(_abs64, values(D)) / maximum(_abs64, values(F)))
end

# H^2 = F (exponent dicts; H with all its monomials as keys): Newton steps on
# the midpoints (solve 2 H D = F - H^2 by least squares, H += D; each step
# doubles the number of correct bits; the recurrence of _sqrt_homogeneous
# alone loses many bits when the leading coefficient is
# small), then a rigorous enclosure (_enclose_square_root!).
function _refine_square_root!(F::Dict{Vector{Int}, AcbFieldElem}, H::Dict{Vector{Int}, AcbFieldElem};
                              steps::Int = 3)
  Fm = Dict(e => _acb_mid(c) for (e, c) in F)
  for e in keys(H)
    H[e] = _acb_mid(H[e])
  end
  for _ in 1:steps
    J, R, _ = _square_root_system(Fm, H)
    n = ncols(J)
    A = hcat(J, R)
    K = numerical_kernel(A; nullity = 1)[1]
    t = -K[n + 1, 1]
    for (k, mk) in enumerate(collect(keys(H)))
      H[mk] = _acb_mid(H[mk] + K[k, 1] / t)
    end
  end
  return _enclose_square_root!(F, H)
end

# The linearization at H: J (2 H D = J D, columns: the keys of H in the order
# of keys(H)) and R = F - H^2 (one row per monomial)
function _square_root_system(F::Dict{Vector{Int}, AcbFieldElem}, H::Dict{Vector{Int}, AcbFieldElem})
  CC = parent(first(values(F)))
  unknowns = collect(keys(H))
  D = copy(F)
  for (e1, c1) in H, (e2, c2) in H
    e = e1 + e2
    D[e] = get(D, e, zero(CC)) - c1*c2
  end
  equations = collect(keys(D))
  index = Dict(e => i for (i, e) in enumerate(equations))
  J = zero_matrix(CC, length(equations), length(unknowns))
  for (k, mk) in enumerate(unknowns), (e, c) in H
    J[index[e + mk], k] += 2*c
  end
  R = matrix(CC, length(equations), 1, [D[e] for e in equations])
  return J, R, equations
end

# H (exact midpoints, close to a square root of the ball polynomial F) is
# replaced by balls containing the square root of F near H: with H~ = H + D,
# the equations for D are J D + D^2 = R; on n independent equations
# (n = number of unknowns) D = J_s^-1 (R_s - (D^2)_s), a contraction on the
# ball of radius eps around 0 if |J_s^-1 R_s| + |J_s^-1| n eps^2 <= eps.
function _enclose_square_root!(F::Dict{Vector{Int}, AcbFieldElem}, H::Dict{Vector{Int}, AcbFieldElem})
  CC = parent(first(values(F)))
  J, R, _ = _square_root_system(F, H)
  n = ncols(J)
  rows = _numerical_kernel_data(J; nullity = 0).pivot_rows
  Js = matrix(CC, n, n, [J[i, k] for i in rows for k in 1:n])
  Rs = matrix(CC, n, 1, [R[i, 1] for i in rows])
  Jinv = _inv_precond(Js)
  E = Jinv * Rs
  upper(z) = (a = abs(z); Float64(Hecke.midpoint(a)) + Float64(Hecke.radius(a)))
  e_max = maximum(upper(E[k, 1]) for k in 1:n)
  jinv_norm = maximum(sum(upper(Jinv[i, k]) for k in 1:n) for i in 1:n)
  eps = 2*e_max + 2.0^(-2*precision(CC))
  quadratic = jinv_norm * n * eps^2
  @req e_max + quadratic <= eps "Could not enclose the square root (increase the precision)."
  err = ArbField(precision(CC))(quadratic * (1 + 1e-10))
  for (k, mk) in enumerate(collect(keys(H)))
    H[mk] = H[mk] + E[k, 1]
    _add_error!(H[mk], err)
  end
  return H
end

# Square root H of a form F of degree 2d that is a square: the variable x_i0
# with the largest coefficient c of x_i0^(2d); H = sqrt(c) x_i0^d + ..., the
# coefficients of x_i0^(d - i) m (m of degree i in the other variables) from
# the coefficient of x_i0^(2d - i) m in F - (known part)^2, i = 1..d.
# (Magma: ComputeSqrtHomogeneous.)
function _sqrt_homogeneous(F::MPolyRingElem)
  R = parent(F)
  n = nvars(R)
  Fd = Dict{Vector{Int}, AcbFieldElem}(e => c for (c, e) in zip(coefficients(F), exponent_vectors(F)))
  CC = base_ring(R)
  d = div(total_degree(F), 2)
  pure(i, e) = [j == i ? e : 0 for j in 1:n]
  i0 = argmax([_abs64(get(Fd, pure(i, 2*d), zero(CC))) for i in 1:n])
  r0 = RSR._rotated_power(Fd[pure(i0, 2*d)], 1//2)
  H = Dict{Vector{Int}, AcbFieldElem}(pure(i0, d) => r0)
  others = [j for j in 1:n if j != i0]
  for i in 1:d
    known = copy(H)
    for m in _exponent_vectors(n - 1, i)
      e = zeros(Int, n)
      e[others] = m
      target = copy(e)
      target[i0] = 2*d - i
      s = get(Fd, target, zero(CC))
      for (e1, c1) in known, (e2, c2) in known
        e1 + e2 == target && (s -= c1*c2)
      end
      e[i0] = d - i
      H[e] = s / (2*r0)
    end
  end
  _refine_square_root!(Fd, H)
  return _polynomial_from_dict(R, H), _square_residual(Fd, H)
end
