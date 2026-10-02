################################################################################
#
#  RieSrf/Numerics/IntegrationParameters.jl : integration parameters
#
#  The user settings of the numerical computation (IntegrationParameters) and
#  the constants of the precision management (guard bits, see the comment
#  before _quadrature_guard_bits).
#
################################################################################

@doc raw"""
    IntegrationParameters(; integration_method = :heuristic, int_style = :mixed,
                            midpoint_precision = :auto, adaptive = true,
                            chunk_len = 16, group_cost = 1.0, superelliptic = true,
                            precision_retry = true, accuracy = :both,
                            direct_infinity = false)

Settings for the numerical computations on a Riemann surface.

- `integration_method`: `:heuristic` (heuristic bounds for the integrands; the
  only method at the moment, `:rigorous` is not implemented yet).
- `int_style`: `:mixed` (Gauss-Legendre, and double exponential for subpaths
  close to a discriminant point), `:gl` (Gauss-Legendre only) or `:de`
  (double exponential only).
  (Strings such as `"Mixed"` or `"GL"` are accepted as well.)
- `midpoint_precision`: precision used for the intermediate steps of the
  analytic continuation; `0` switches it off, `:auto` chooses heuristically.
- `adaptive`: adaptive step size (predictor-corrector) in the analytic continuation.
- `chunk_len`: number of abscissae per parallel job.
- `group_cost`: cost of an extra Gauss-Legendre scheme when grouping the
  subpaths (see `_gl_group_rs`).
- `superelliptic`: with `model = :auto`, compute the period matrices and the
  Abel-Jacobi map of a curve of the form c*y^m + q(x) = 0 (or with x and y
  swapped, q separable of degree at least 3) with the algorithm for
  superelliptic curves (Molin-Neurohr), which is much faster. `false` uses the
  general algorithm for every curve.
- `precision_retry`: if the matrix selected by `accuracy`
  claims fewer bits than the requested precision, compute the integrals once
  more with a higher target and working precision (the integration is redone,
  so this roughly doubles the time). `false` accepts a few bits less instead.
- `accuracy`: which absolute accuracy the precision retry aims for:
  `:small` (the small period matrix tau), `:big` (the big period matrix) or
  `:both` (the default). The two can differ a lot: tau does not depend on the scaling of
  the differentials, the big period matrix does. For curves with large
  coefficients or far-out discriminant points the entries of the big period
  matrix can be of size 2^70 while tau is of moderate size, and then an
  absolute accuracy of 2^-prec for the big period matrix needs ~70 bits
  more working precision. With the general algorithm, `:big` and `:both`
  raise the working precision by log2 of the integrand bound in advance, which
  normally avoids the retry (the superelliptic algorithm already does so).
- `direct_infinity`: general algorithm: also integrate along one big circle
  around all discriminant points (a loop around infinity) and compare with
  the loop around infinity composed of the other loops. If they agree the
  smaller ball is used, otherwise a warning is given. Off by default: it is a
  consistency check, the gain in precision was negligible in the tests and
  the big circle costs a lot of extra nodes.

The parameters of a Riemann surface are fixed once a numerical computation
has started. Values `:auto` are then replaced by concrete values, which can be
inspected with `resolved_integration_parameters`.
"""
mutable struct IntegrationParameters
  integration_method::Symbol
  int_style::Symbol
  midpoint_precision::Union{Symbol, Int}
  adaptive::Bool
  chunk_len::Int
  group_cost::Float64
  superelliptic::Bool
  precision_retry::Bool
  accuracy::Symbol
  direct_infinity::Bool
end

function IntegrationParameters(; integration_method::Union{Symbol, String} = :heuristic,
                                 int_style::Union{Symbol, String} = :mixed,
                                 midpoint_precision::Union{Symbol, Int} = :auto,
                                 adaptive::Bool = true,
                                 chunk_len::Int = 16,
                                 group_cost::Real = 1.0,
                                 superelliptic::Bool = true,
                                 precision_retry::Bool = true,
                                 accuracy::Symbol = :both,
                                 direct_infinity::Bool = false)
  P = IntegrationParameters(_option_symbol(integration_method), _option_symbol(int_style),
                            midpoint_precision,
                            adaptive, chunk_len, Float64(group_cost), superelliptic,
                            precision_retry, accuracy, direct_infinity)
  _check_integration_parameters(P)
  return P
end

Base.copy(P::IntegrationParameters) =
  IntegrationParameters(P.integration_method, P.int_style, P.midpoint_precision,
                        P.adaptive, P.chunk_len, P.group_cost, P.superelliptic,
                        P.precision_retry, P.accuracy, P.direct_infinity)

function Base.show(io::IO, P::IntegrationParameters)
  print(io, "IntegrationParameters(integration_method = $(repr(P.integration_method)), ",
            "int_style = $(repr(P.int_style)), midpoint_precision = $(repr(P.midpoint_precision)), ",
            "adaptive = $(P.adaptive), chunk_len = $(P.chunk_len), group_cost = $(P.group_cost), ",
            "superelliptic = $(P.superelliptic), precision_retry = $(P.precision_retry), ",
            "accuracy = $(repr(P.accuracy)), ",
            "direct_infinity = $(P.direct_infinity))")
end

function _check_integration_parameters(P::IntegrationParameters)
  @req P.integration_method !== :rigorous "Rigorous integration is not implemented yet; use integration_method = :heuristic."
  @req P.integration_method === :heuristic "integration_method must be :heuristic."
  @req P.int_style in (:mixed, :gl, :de) "int_style must be :mixed, :gl or :de."
  mp = P.midpoint_precision
  @req (mp === :auto) || (mp isa Int && mp >= 0) "midpoint_precision must be :auto or an integer >= 0."
  @req P.chunk_len >= 1 "chunk_len must be positive."
  @req P.group_cost >= 0 "group_cost must be nonnegative."
  @req P.accuracy in (:small, :big, :both) "accuracy must be :small, :big or :both."
  return P
end

# "Mixed" -> :mixed, "GL" -> :gl etc.
_option_symbol(x::Union{Symbol, String}) = Symbol(lowercase(String(x)))

# Direct assignments convert strings as well (P.int_style = "GL").
function Base.setproperty!(P::IntegrationParameters, name::Symbol, value)
  if name in (:integration_method, :int_style) && value isa String
    value = _option_symbol(value)
  end
  return setfield!(P, name, convert(fieldtype(IntegrationParameters, name), value))
end

# Copy of P with some fields changed (keyword arguments = field names).
function _with_changes(P::IntegrationParameters; kw...)
  Q = copy(P)
  for (k, v) in kw
    @req hasfield(IntegrationParameters, k) "Unknown integration parameter $k."
    k in (:integration_method, :int_style) && (v = _option_symbol(v))
    setfield!(Q, k, convert(fieldtype(IntegrationParameters, k), v))
  end
  return _check_integration_parameters(Q)
end

# Heuristic for midpoint_precision = :auto. With the adaptive continuation the
# low-precision midpoints only pay off at high precision (f2: slower at 200
# bits, 10% faster at 1000 bits).
_auto_midpoint_precision(computational_precision::Int) = computational_precision >= 400 ? 128 : 0

# Precision management (general algorithm):
#   target precision T = prec + _quadrature_guard_bits() + ceil(log2 K), K the
#     number of subpaths: the quadrature is chosen for (heuristic) errors 2^-T
#     of the integrals along the subpaths, and 2^-T is added to their radii,
#     so that a period (a sum of at most K of them) is still accurate to about
#     prec + guard bits;
#   working precision W = T + _rounding_guard_bits(): room for the rounding
#     errors (measured losses are mostly 2-13 bits);
#   precision_retry: if tau (accuracy = :small), the big period matrix (:big)
#     or either of them (:both) still claims fewer than prec bits (e.g. after
#     the inversion of P1, or because the periods are large), the integration
#     is redone once with T raised by the shortfall + _retry_extra_bits().
# Before the paths are known (discriminant points, fundamental group) the
# estimate K = 1024 is used. The working precision is never lowered below this
# initial one, so that the paths and the integrands normally have the same
# precision; it is raised if K > 1024 or after a retry.
_quadrature_guard_bits() = 10
# Extra target bits growing with the genus: tau loses more to the inversion of
# P1 and the sums over more chains for larger genus. Measured shortfalls of
# tau without it: none up to genus 8, 5-7 bits for genus 12-28, 9 for genus
# 54; each would cost a full retry (about twice the time).
_genus_guard_bits(g::Int) = g <= 1 ? 0 : ceil(Int, 2*log2(g))
_retry_extra_bits() = 8
# accuracy = :big/:both: extra working precision log2(M) for an integrand
# bound M (measured shortfalls of the big period matrix without it: 51-53
# bits for log2 M = 63-71; none for log2 M < 10).
_magnitude_guard_bits(M::ArbFieldElem) =
  (isfinite(M) && M > 1) ? max(0, ceil(Int, _arb_mid_f64(log(M) / log(parent(M)(2))))) : 0
_initial_target_precision(prec::Int) = prec + _quadrature_guard_bits() + 10
_rounding_guard_bits() = 32

# Default type of the numerical output of a RiemannSurface created with a
# precision (riemann_surface(f, prec)): :acb or :complex. A surface created
# with riemann_surface(f, ComplexField()) always has :complex.
_default_output() = :acb
