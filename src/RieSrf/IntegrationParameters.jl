################################################################################
#
#  Integration parameters
#
################################################################################

@doc raw"""
    IntegrationParameters(; integration_method = "heuristic", int_style = "Mixed",
                            midpoint_precision = :auto, adaptive = true,
                            chunk_len = 16, group_cost = 1.0, superelliptic = true,
                            precision_retry = true, direct_infinity = false)

Settings for the numerical computations on a Riemann surface.

- `integration_method`: `"heuristic"` or `"rigorous"`.
- `int_style`: `"Mixed"`, `"GL"` (Gauss-Legendre) or `"DE"` (double exponential).
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
- `precision_retry`: general algorithm: if the small period matrix claims
  fewer bits than the requested precision, compute the integrals once more
  with a higher target and working precision (the integration is redone, so
  this roughly doubles the time). `false` accepts a few bits less instead.
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
  integration_method::String
  int_style::String
  midpoint_precision::Union{Symbol, Int}
  adaptive::Bool
  chunk_len::Int
  group_cost::Float64
  superelliptic::Bool
  precision_retry::Bool
  direct_infinity::Bool
end

function IntegrationParameters(; integration_method::String = "heuristic",
                                 int_style::String = "Mixed",
                                 midpoint_precision::Union{Symbol, Int} = :auto,
                                 adaptive::Bool = true,
                                 chunk_len::Int = 16,
                                 group_cost::Real = 1.0,
                                 superelliptic::Bool = true,
                                 precision_retry::Bool = true,
                                 direct_infinity::Bool = false)
  P = IntegrationParameters(integration_method, int_style, midpoint_precision,
                            adaptive, chunk_len, Float64(group_cost), superelliptic,
                            precision_retry, direct_infinity)
  _check_integration_parameters(P)
  return P
end

Base.copy(P::IntegrationParameters) =
  IntegrationParameters(P.integration_method, P.int_style, P.midpoint_precision,
                        P.adaptive, P.chunk_len, P.group_cost, P.superelliptic,
                        P.precision_retry, P.direct_infinity)

function Base.show(io::IO, P::IntegrationParameters)
  print(io, "IntegrationParameters(integration_method = \"$(P.integration_method)\", ",
            "int_style = \"$(P.int_style)\", midpoint_precision = $(repr(P.midpoint_precision)), ",
            "adaptive = $(P.adaptive), chunk_len = $(P.chunk_len), group_cost = $(P.group_cost), ",
            "superelliptic = $(P.superelliptic), precision_retry = $(P.precision_retry), ",
            "direct_infinity = $(P.direct_infinity))")
end

function _check_integration_parameters(P::IntegrationParameters)
  @req P.integration_method in ("heuristic", "rigorous") "integration_method must be \"heuristic\" or \"rigorous\"."
  @req P.int_style in ("Mixed", "GL", "DE") "int_style must be \"Mixed\", \"GL\" or \"DE\"."
  mp = P.midpoint_precision
  @req (mp === :auto) || (mp isa Int && mp >= 0) "midpoint_precision must be :auto or an integer >= 0."
  @req P.chunk_len >= 1 "chunk_len must be positive."
  @req P.group_cost >= 0 "group_cost must be nonnegative."
  return P
end

# Copy of P with some fields changed (keyword arguments = field names).
function _with_changes(P::IntegrationParameters; kw...)
  Q = copy(P)
  for (k, v) in kw
    @req hasfield(IntegrationParameters, k) "Unknown integration parameter $k."
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
#   precision_retry: if tau still claims fewer than prec bits (e.g. after the
#     inversion of P1), the integration is redone once with T raised by the
#     shortfall + _retry_extra_bits().
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
_initial_target_precision(prec::Int) = prec + _quadrature_guard_bits() + 10
_rounding_guard_bits() = 32
