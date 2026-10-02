################################################################################
#
#  RieSrf/Paths/AnalyticContinuation.jl : continuing the fiber along a path
#
#  For a path x(t) in the x-plane and the fiber y_1, ..., y_m of f(x, y) = 0
#  over its start point, the functions here follow every root y_i along the
#  path (Neurohr, Section 4.4). This gives the permutations of the sheets
#  along the paths (monodromy) and the fibers at the quadrature nodes.
#
#  A step x1 -> x2 is accepted when the Weierstrass corrections at x2 isolate
#  the roots (_isolation_check!); the roots at x2 are then refined with
#  acb_poly_find_roots. The steps are chosen
#  - adaptively with a secant predictor (_continue_adaptive!; the default for
#    the period matrix and the monodromy), or
#  - by bisection (_continue_by_bisection!; integration parameter
#    adaptive = false, and analytic_continuation, used by the Abel-Jacobi map).
#  Both can work in mixed precision: the checks and the intermediate points in
#  a low-precision workspace, the roots at the targets at full precision.
#  _continue_unchecked! makes a step without the check, for paths to infinity.
#
#  Entry points: analytic_continuation, _continue_adaptive!,
#  _continue_by_bisection!, _continue_unchecked!, _fresh_fiber!.
#
################################################################################

################################################################################
#
#  Workspace
#
################################################################################

# Everything a continuation needs for one polynomial f(x, y) at one precision,
# with preallocated scratch values: the continuation is the innermost loop of
# the period computation and must not allocate. One workspace per thread.
mutable struct ContinuationWorkspace
  split_polynomial::Vector{Vector{AcbFieldElem}}  # _split_in_y(f): x-coefficients of y^0, ..., y^m
  Ky::AcbPolyRing                       # C[y] at the precision of the workspace
  m::Int                                # degree of f in y (number of sheets)
  fiber_polynomial::AcbPolyRingElem     # f(x, y) for the current x (_specialize_x!)
  leading_coefficient::AcbFieldElem     # the y^m coefficient of fiber_polynomial
  corrections::Vector{AcbFieldElem}     # Weierstrass corrections W_i of the last checked fiber
  abs_corrections::Vector{ArbFieldElem} # |W_i|
  max_correction::ArbFieldElem          # max_i |W_i|
  movement::Vector{ArbFieldElem}        # |zp_i - z_i| (adaptive check)
  worst_lhs::ArbFieldElem               # left side of the worst pair in _pairwise_check!
  worst_rhs::ArbFieldElem               # right side of the worst pair in _pairwise_check!
  product::AcbFieldElem                 # scratch
  diff::AcbFieldElem                    # scratch
  abs_diff::ArbFieldElem                # scratch
  lhs::ArbFieldElem                     # scratch
  ratio::ArbFieldElem                   # scratch
  start_values::Ptr{acb_struct}         # input of acb_poly_find_roots (m entries)
  roots::Ptr{acb_struct}                # output of acb_poly_find_roots (m entries)
  coefficient_table::Ptr{acb_struct}    # split_polynomial for acb_dot: (m + 1) x x_length, row-major
  x_length::Int                         # number of columns of coefficient_table
  row_lengths::Vector{Int}              # lengths of its rows without trailing zeros
  x_powers::Ptr{acb_struct}             # 1, x, ..., x^(x_length - 1)

  function ContinuationWorkspace(split_polynomial::Vector{Vector{AcbFieldElem}}, Ky::AcbPolyRing)
    CC = base_ring(Ky)
    RR = ArbField(precision(CC))
    m = length(split_polynomial) - 1
    x_length = maximum(length, split_polynomial)
    entry_size = sizeof(acb_struct)
    coefficient_table = acb_vec((m + 1)*x_length)
    row_lengths = zeros(Int, m + 1)
    for j in 0:m, i in 0:x_length-1
      entry = coefficient_table + (j*x_length + i)*entry_size
      if i < length(split_polynomial[j+1])
        c = split_polynomial[j+1][i+1]
        ccall((:acb_set, libflint), Nothing, (Ptr{acb_struct}, Ref{AcbFieldElem}), entry, c)
        iszero(c) || (row_lengths[j+1] = i + 1)
      else
        ccall((:acb_zero, libflint), Nothing, (Ptr{acb_struct},), entry)
      end
    end
    workspace = new(split_polynomial, Ky, m, Ky([CC() for _ in split_polynomial]), CC(),
                    [CC() for _ in 1:m], [RR() for _ in 1:m], RR(), [RR() for _ in 1:m],
                    RR(), RR(), CC(), CC(), RR(), RR(), RR(),
                    acb_vec(m), acb_vec(m), coefficient_table, x_length, row_lengths,
                    acb_vec(x_length))
    finalizer(workspace) do w
      acb_vec_clear(w.start_values, w.m)
      acb_vec_clear(w.roots, w.m)
      acb_vec_clear(w.coefficient_table, (w.m + 1)*w.x_length)
      acb_vec_clear(w.x_powers, w.x_length)
    end
    return workspace
  end
end

# workspace.fiber_polynomial <- f(x, y); returns it.
function _specialize_x!(workspace::ContinuationWorkspace, x::AcbFieldElem)
  prec = precision(parent(workspace.leading_coefficient))
  entry_size = sizeof(acb_struct)
  GC.@preserve workspace begin
    _acb_powers_ptr!(workspace.x_powers, x, workspace.x_length - 1, prec)
    for j in 0:workspace.m
      # leading_coefficient is used as the buffer; after the last j it holds
      # the y^m coefficient.
      _acb_dot_ptr!(workspace.leading_coefficient,
                    workspace.coefficient_table + j*workspace.x_length*entry_size,
                    workspace.x_powers, workspace.row_lengths[j+1], prec)
      setcoeff!(workspace.fiber_polynomial, j, workspace.leading_coefficient)
    end
  end
  return workspace.fiber_polynomial
end

# The Weierstrass (Durand-Kerner) corrections
#   W_i = f(x, z_i) / (lc * prod_{j != i} (z_i - z_j))
# of the approximations z = fiber w.r.t. workspace.fiber_polynomial, and
# their absolute values and maximum.
function _weierstrass_corrections!(workspace::ContinuationWorkspace, fiber::Vector{AcbFieldElem})
  m = workspace.m
  product = workspace.product
  diff = workspace.diff
  for i in 1:m
    Nemo.one!(product)
    for j in 1:m
      j == i && continue
      sub!(diff, fiber[i], fiber[j])
      mul!(product, product, diff)
    end
    mul!(product, product, workspace.leading_coefficient)
    _acb_poly_evaluate!(workspace.corrections[i], workspace.fiber_polynomial, fiber[i])
    Nemo.div!(workspace.corrections[i], workspace.corrections[i], product)
    Hecke.abs!(workspace.abs_corrections[i], workspace.corrections[i])
    if i == 1 || workspace.abs_corrections[i] > workspace.max_correction
      Hecke.set!(workspace.max_correction, workspace.abs_corrections[i])
    end
  end
  return workspace
end

# Upper bound for the number of bisections (or failed steps in a row).
function _max_bisection_depth()
  return 200
end

################################################################################
#
#  The isolation check
#
################################################################################

# The disks D(z_i, m|W_i|) contain the roots; they isolate them if they are
# pairwise disjoint: m(|W_i| + |W_j|) < |z_i - z_j| for all i < j. (Checked
# per pair, not as 2m max|W_i| < min|z_i - z_j|: when the roots have very
# different sizes, e.g. |y| from 1e-20 to 1e11 far out on a path, the
# large roots have large corrections but are also far apart, and the global
# version forces absurdly small steps.)
# Returns :pass, :bisect or :precision (see _fail_status).
function _isolation_check!(workspace::ContinuationWorkspace, x2::AcbFieldElem,
                           fiber::Vector{AcbFieldElem})
  _specialize_x!(workspace, x2)
  _weierstrass_corrections!(workspace, fiber)
  return _pairwise_check!(workspace, fiber, false)[1]
end

# Checks  mv_i + mv_j + m(|W_i| + |W_j|) < |z_i - z_j|  for all pairs (the
# movement terms mv only if with_movement, from workspace.movement). Returns
# (status, q) with q the largest ratio lhs/rhs (a Float64; ratios that are not
# representable are skipped). worst_lhs and worst_rhs are set to the two sides
# for the pair with the largest ratio (for the error message).
function _pairwise_check!(workspace::ContinuationWorkspace, fiber::Vector{AcbFieldElem},
                          with_movement::Bool)
  m = workspace.m
  lhs = workspace.lhs
  abs_diff = workspace.abs_diff
  status = :pass
  worst_ratio = 0.0
  first = true
  for i in 1:m, j in i+1:m
    add!(lhs, workspace.abs_corrections[i], workspace.abs_corrections[j])
    _arb_mul_si!(lhs, lhs, m)
    if with_movement
      add!(lhs, lhs, workspace.movement[i])
      add!(lhs, lhs, workspace.movement[j])
    end
    sub!(workspace.diff, fiber[i], fiber[j])
    Hecke.abs!(abs_diff, workspace.diff)
    Nemo.div!(workspace.ratio, lhs, abs_diff)
    ratio = _arb_mid_f64(workspace.ratio)
    if first || ratio > worst_ratio || isnan(ratio)
      worst_ratio = isnan(ratio) ? worst_ratio : ratio
      Hecke.set!(workspace.worst_lhs, lhs)
      Hecke.set!(workspace.worst_rhs, abs_diff)
      first = false
    end
    if !(lhs < abs_diff)
      pair_status = _fail_status(lhs, abs_diff)
      (status === :pass || pair_status === :precision) && (status = pair_status)
    end
  end
  return status, worst_ratio
end

# Why a check `a < d` failed. :precision only if a is dominated by its own
# rounding error: then a smaller step does not help. If a is simply too large
# (a far too long step, e.g. the first step of a continuation without history)
# a smaller step does help, even when the absolute radius of a exceeds d.
function _fail_status(a::ArbFieldElem, d::ArbFieldElem)
  4*radius(a) < d && return :bisect
  return 4*radius(a) < abs(Nemo.midpoint(a)) ? :bisect : :precision
end

function _continuation_error(workspace::ContinuationWorkspace, x1, x2, depth::Int, status::Symbol)
  CC32 = AcbField(32)
  RR32 = ArbField(32)
  reason = status === :precision ? "working precision too low to certify the step" :
                                   "maximal bisection depth ($(_max_bisection_depth())) reached"
  error("Analytic continuation failed: $reason.\n" *
        "  x1 = $(CC32(x1)), x2 = $(CC32(x2)), depth = $depth, precision = $(precision(base_ring(workspace.Ky)))\n" *
        "  worst pair of roots: |z_i - z_j| = $(RR32(workspace.worst_rhs)), " *
        "m(|W_i| + |W_j|) (+ movement) = $(RR32(workspace.worst_lhs))\n" *
        "  Increase the precision (or check the radius of x1, x2).")
end

################################################################################
#
#  Root finding
#
################################################################################

# Roots of workspace.fiber_polynomial from the given starting values, into
# workspace.roots, at the precision of the workspace. Returns the number of
# isolated roots (attempts = 0: as many iterations as needed).
function _find_roots_from!(workspace::ContinuationWorkspace, starts::Vector{AcbFieldElem},
                           attempts::Int = 0)
  fillacb!(workspace.start_values, starts)
  return ccall((:acb_poly_find_roots, libflint), Cint,
               (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int),
               workspace.roots, workspace.fiber_polynomial, workspace.start_values, attempts,
               precision(base_ring(workspace.Ky)))
end

# (f_split, Ky) for a ContinuationWorkspace of the model at precision prec.
function _continuation_data(RS::RiemannSurfaceModel, prec::Int)
  f = _embed_mpoly(defining_polynomial(RS), embedding(RS), prec)
  Ky, _ = polynomial_ring(base_ring(f), "y")
  return _split_in_y(f), Ky
end

# A fiber from scratch at full precision (see _accurate_roots).
function _fresh_fiber!(workspace::ContinuationWorkspace, x::AcbFieldElem, prec::Int)
  return _accurate_roots(_specialize_x!(workspace, x), prec)
end

# After a passed check at x2 in `checked` (workspace or low_workspace), with
# the starting values z_i - W_i in checked.corrections: compute the fiber at
# x2. At an intermediate point (not final) of a mixed-precision continuation
# the low precision roots suffice if they converge quickly; otherwise the
# roots are computed at full precision into fiber, and rounded into
# low_fiber. Without low_workspace, low_fiber is fiber.
function _refine_roots!(workspace::ContinuationWorkspace,
                        low_workspace::Union{Nothing, ContinuationWorkspace},
                        checked::ContinuationWorkspace, x2::AcbFieldElem,
                        fiber::Vector{AcbFieldElem}, low_fiber::Vector{AcbFieldElem}, final::Bool)
  m = workspace.m
  entry_size = sizeof(acb_struct)
  if low_workspace !== nothing && !final && checked === low_workspace
    if _find_roots_from!(low_workspace, low_workspace.corrections, 8) == m
      for i in 1:m
        Nemo._acb_set(low_fiber[i], low_workspace.roots + (i - 1)*entry_size)
      end
      return
    end
  end
  checked === workspace || _specialize_x!(workspace, x2)
  number_of_roots = _find_roots_from!(workspace, checked.corrections)
  @assert number_of_roots == m
  for i in 1:m
    root = workspace.roots + (i - 1)*entry_size
    Nemo._acb_set(fiber[i], root)
    low_workspace === nothing || _acb_set_round_ptr!(low_fiber[i], root)
  end
  return
end

function _copy_fiber(CC::AcbField, fiber::Vector{AcbFieldElem})
  result = [CC() for _ in fiber]
  for i in eachindex(fiber)
    Hecke.set!(result[i], fiber[i])
  end
  return result
end

################################################################################
#
#  Continuation by bisection
#
################################################################################

@doc raw"""
    analytic_continuation(RS::RiemannSurfaceModel, path::CPath, abscissae::Vector{ArbFieldElem},
                          start_fiber::Vector{AcbFieldElem} = AcbFieldElem[], prec::Int = 0)
                          -> Vector{AcbFieldElem}, Vector{Vector{AcbFieldElem}}

Continue the fiber over the start of `path` (parametrized by [-1, 1]) along
the path, and return the points x_l of the path at -1, the abscissae and 1,
together with the fibers over them. Without `start_fiber` the start fiber
is computed and sorted by `sheet_ordering`. The precision is the maximum of
`prec` and the precision of `RS`.
"""
function analytic_continuation(RS::RiemannSurfaceModel, path::CPath, abscissae::Vector{ArbFieldElem},
                               start_fiber::Vector{AcbFieldElem} = AcbFieldElem[], prec::Int = 0)
  prec = max(prec, precision(RS))
  RR = ArbField(prec)
  f = _embed_mpoly(defining_polynomial(RS), embedding(RS), prec)
  CC = base_ring(f)
  Ky, y = polynomial_ring(CC, "y")
  m = degree(f, 2)

  parameters = vcat([-one(RR)], abscissae, [one(RR)])
  N = length(parameters)
  x_values = [evaluate(path, t) for t in parameters]
  fibers = Vector{Vector{AcbFieldElem}}(undef, N)
  if isempty(start_fiber)
    fibers[1] = sort!(_accurate_roots(f(x_values[1], y), prec), lt = sheet_ordering)
  else
    fibers[1] = start_fiber
  end

  workspace = ContinuationWorkspace(_split_in_y(f), Ky)
  fiber = _copy_fiber(CC, fibers[1])          # updated in place
  for l in 2:N
    _continue_by_bisection!(workspace, nothing, x_values[l-1], x_values[l], fiber, fiber)
    fibers[l] = _copy_fiber(CC, fiber)
  end
  return x_values, fibers
end

# Continue the fiber from x1 to x2, bisecting the step until the isolation
# check passes. The entries of fiber are overwritten (fiber must own its
# elements). Mixed precision if low_workspace is given: checks and the roots at
# the bisection points in low_workspace (low_fiber), full precision roots
# at x2 (into fiber, rounded into low_fiber) if final. If the low-precision
# check fails only because its balls are too wide (tight clusters of roots),
# the check is redone at full precision instead of bisecting forever. Without
# low_workspace, low_fiber must be fiber.
function _continue_by_bisection!(workspace::ContinuationWorkspace,
                                 low_workspace::Union{Nothing, ContinuationWorkspace},
                                 x1::AcbFieldElem, x2::AcbFieldElem,
                                 fiber::Vector{AcbFieldElem}, low_fiber::Vector{AcbFieldElem},
                                 final::Bool = true, depth::Int = 0)
  checked = low_workspace === nothing ? workspace : low_workspace
  status = _isolation_check!(checked, x2, low_fiber)
  if status === :precision && low_workspace !== nothing
    checked = workspace
    status = _isolation_check!(workspace, x2, low_fiber)
  end

  if status === :pass
    for i in 1:workspace.m
      sub!(checked.corrections[i], low_fiber[i], checked.corrections[i])  # starting values z_i - W_i
    end
    _refine_roots!(workspace, low_workspace, checked, x2, fiber, low_fiber, final)
    return fiber
  elseif status === :bisect && depth < _max_bisection_depth()
    midpoint = (x1 + x2)//2
    _continue_by_bisection!(workspace, low_workspace, x1, midpoint, fiber, low_fiber, false, depth + 1)
    return _continue_by_bisection!(workspace, low_workspace, midpoint, x2, fiber, low_fiber, final, depth + 1)
  else
    _continuation_error(checked, x1, x2, depth, status)
  end
end

# One step x1 -> x2 without the isolation check and without certification,
# for paths to infinity (Abel-Jacobi map): there the roots grow without bound
# and the check would bisect forever; the caller checks the result
# heuristically. Durand-Kerner steps z_i <- z_i - W_i as long as the
# corrections shrink and max|W_i|^2 > tolerance, then acb_poly_find_roots.
# Returns (fiber at x2, stalled): if target_tolerance > 0 and the corrections
# stopped shrinking above it, stalled = true (with the unrefined fiber) and the
# caller takes smaller steps.
function _continue_unchecked!(workspace::ContinuationWorkspace, x1::AcbFieldElem,
                              x2::AcbFieldElem, fiber::Vector{AcbFieldElem},
                              tolerance::ArbFieldElem,
                              target_tolerance::ArbFieldElem = parent(tolerance)(-1))
  m = workspace.m
  CC = base_ring(workspace.Ky)
  RR = parent(tolerance)
  new_fiber = _copy_fiber(CC, fiber)          # updated in place below

  _specialize_x!(workspace, x2)
  _weierstrass_corrections!(workspace, new_fiber)
  next_error = workspace.max_correction^2
  last_error = RR(Inf)

  while next_error > tolerance && next_error < last_error
    for i in 1:m
      sub!(new_fiber[i], new_fiber[i], workspace.corrections[i])
    end
    _weierstrass_corrections!(workspace, new_fiber)
    last_error = next_error
    next_error = workspace.max_correction^2
  end

  if target_tolerance > RR(0) && next_error > target_tolerance && next_error >= last_error
    return new_fiber, true
  end

  number_of_roots = _find_roots_from!(workspace, new_fiber)
  @assert number_of_roots == m
  return array(CC, workspace.roots, m), false
end

################################################################################
#
#  Adaptive predictor-corrector continuation (period matrix, monodromy)
#
#  1. Predictor. The check is done at the secant prediction
#         zp_i = z_i(x1) + (z_i(x1) - z_i(x0)) * (x2 - x1)/(x1 - x0)
#     (x0 = previous accepted point). Its error is O(h * h_prev * z''), so
#     |W_i(zp)| is much smaller, larger steps pass, and acb_poly_find_roots
#     starts closer to the roots (fewer iterations).
#
#  2. Step control. The step size is kept across abscissae (and across the
#     intervals of a chunk). After a pass it grows, after a fail it shrinks,
#     by a factor computed from q = (2m max|W_i|) / d.
#
#  Certification. The Weierstrass check at zp shows: the disks D(zp_i, m|W_i|)
#  are disjoint and each contains exactly one root at x2. In addition we
#  require (per pair, see _adaptive_check!)
#         2 max|zp_i - z_i(x1)| + 2m max|W_i|  <  min_{i<j} |z_i(x1) - z_j(x1)|,
#  i.e. every root moved less than half the separation at x1. Without a
#  predictor (zp = z) this is the condition of the bisection method; with a
#  predictor it gives the same conclusion: a bijection between the fibers with
#  |y_i(x2) - z_i(x1)| < d(x1)/2. (Like Neurohr's method, this is a check
#  between two points, not along the whole segment.)
#
#  The trial points are exact (ball midpoints) points on the segment from x1
#  to the target.
#
################################################################################

mutable struct AdaptiveContinuationState
  x0::AcbFieldElem                        # previous accepted point
  x1::AcbFieldElem                        # current point
  x2::AcbFieldElem                        # scratch: trial point
  fiber0::Vector{AcbFieldElem}            # fiber at x0 (at the precision of the checks)
  predicted_fiber::Vector{AcbFieldElem}   # predicted fiber zp at x2
  diff::AcbFieldElem                      # scratch
  ratio::AcbFieldElem                     # scratch
  abs_value::ArbFieldElem                 # scratch
  step::Float64                           # step length |x2 - x1| to try next
  has_previous::Bool                      # x0 and fiber0 are set
  target_ratio::Float64                   # aim for q = 2m max|W| / d around this value

  function AdaptiveContinuationState(CC::AcbField, m::Int; target_ratio::Float64 = 0.25)
    RR = ArbField(precision(CC))
    return new(CC(), CC(), CC(), [CC() for _ in 1:m], [CC() for _ in 1:m], CC(), CC(),
               RR(), Inf, false, target_ratio)
  end
end

# Start (or restart) at the point x: forget the history.
function _adaptive_reset!(state::AdaptiveContinuationState, x::AcbFieldElem)
  Hecke.set!(state.x1, x)
  state.has_previous = false
  state.step = Inf
  return state
end

# state.predicted_fiber <- secant prediction at x2 from the fiber at x1.
function _predict!(state::AdaptiveContinuationState, fiber::Vector{AcbFieldElem}, x2::AcbFieldElem)
  state.has_previous || return _no_prediction!(state, fiber)
  sub!(state.diff, x2, state.x1)
  sub!(state.ratio, state.x1, state.x0)
  # Previous step not resolvable at this precision (e.g. double exponential
  # abscissae piling up at an endpoint): no prediction, check at the fiber.
  contains_zero(state.ratio) && return _no_prediction!(state, fiber)
  Nemo.div!(state.ratio, state.diff, state.ratio)              # (x2 - x1)/(x1 - x0)
  predicted = state.predicted_fiber
  for i in eachindex(fiber)
    sub!(state.diff, fiber[i], state.fiber0[i])
    mul!(state.diff, state.diff, state.ratio)
    add!(predicted[i], fiber[i], state.diff)
    _acb_get_mid!(predicted[i], predicted[i])                  # exact approximation
    isfinite(predicted[i]) || return _no_prediction!(state, fiber)
  end
  return predicted
end

function _no_prediction!(state::AdaptiveContinuationState, fiber::Vector{AcbFieldElem})
  for i in eachindex(fiber)
    Hecke.set!(state.predicted_fiber[i], fiber[i])
  end
  return state.predicted_fiber
end

# Isolation check at the predicted fiber, plus the movement condition, both
# per pair of roots (see _isolation_check!):
#   isolation at zp:  m(|W_i| + |W_j|) < |zp_i - zp_j|
#   movement:         |zp_i - z_i| + |zp_j - z_j| + m(|W_i| + |W_j|) < |z_i - z_j|,
#                     z = fiber1, the fiber at x1.
# Returns (status, q) with q ~ how much of the budget is used (a pass needs q < 1).
function _adaptive_check!(workspace::ContinuationWorkspace, state::AdaptiveContinuationState,
                          x2::AcbFieldElem, fiber1::Vector{AcbFieldElem})
  predicted = state.predicted_fiber
  _specialize_x!(workspace, x2)
  _weierstrass_corrections!(workspace, predicted)
  status_isolation, ratio_isolation = _pairwise_check!(workspace, predicted, false)
  for i in 1:workspace.m
    sub!(workspace.diff, predicted[i], fiber1[i])
    Hecke.abs!(workspace.movement[i], workspace.diff)
  end
  status_movement, ratio_movement = _pairwise_check!(workspace, fiber1, true)
  ratio = max(ratio_isolation, ratio_movement)
  status_isolation === :pass || return status_isolation, ratio
  return status_movement, ratio
end

_step_grow(state, q) = !(q > 0) ? 2.0 : clamp(0.9*sqrt(state.target_ratio/q), 1.0, 2.0)
_step_shrink(state, q) = !(q > 0) ? 0.5 : clamp(0.9*sqrt(state.target_ratio/q), 0.25, 0.5)

# Continue the fiber from state.x1 to x_target.
#   low_workspace === nothing: fiber is updated in place, low_fiber must be fiber.
#   otherwise: mixed precision as in _continue_by_bisection!: checks and
#              intermediate roots in low_workspace (low_fiber), full precision
#              roots at x_target in workspace (fiber).
# The state must be at the precision of the checks.
function _continue_adaptive!(state::AdaptiveContinuationState, workspace::ContinuationWorkspace,
                             low_workspace::Union{Nothing, ContinuationWorkspace},
                             x_target::AcbFieldElem,
                             fiber::Vector{AcbFieldElem}, low_fiber::Vector{AcbFieldElem})
  m = workspace.m
  check_workspace = low_workspace === nothing ? workspace : low_workspace
  failures = 0
  while true
    sub!(state.diff, x_target, state.x1)
    Hecke.abs!(state.abs_value, state.diff)
    remaining = _arb_mid_f64(state.abs_value)
    if !(remaining > 0)
      # Either x_target = x1, or |x_target - x1| underflows in Float64 (double
      # exponential abscissae near the endpoints at high precision are far
      # closer than 1e-308): then go to x_target in one step, which is still
      # checked.
      _acb_get_mid!(state.ratio, state.diff)
      iszero(state.ratio) && return fiber                        # already there
      remaining = 0.0
    end
    final = !(state.step < remaining * (1 - 1e-9))              # this step reaches x_target
    if final
      x2 = x_target
    else
      Nemo._arb_set(state.abs_value, state.step / remaining)
      mul!(state.diff, state.diff, state.abs_value)
      add!(state.x2, state.x1, state.diff)
      _acb_get_mid!(state.x2, state.x2)
      x2 = state.x2
    end

    _predict!(state, low_fiber, x2)
    checked = check_workspace
    status, ratio = _adaptive_check!(checked, state, x2, low_fiber)
    if status === :precision && low_workspace !== nothing
      checked = workspace                       # tight cluster: check at full precision
      status, ratio = _adaptive_check!(checked, state, x2, low_fiber)
    end

    if status === :pass
      for i in 1:m
        sub!(checked.corrections[i], state.predicted_fiber[i], checked.corrections[i])  # zp_i - W_i
        Hecke.set!(state.fiber0[i], low_fiber[i])
      end
      Hecke.set!(state.x0, state.x1)
      Hecke.set!(state.x1, x2)
      state.has_previous = true
      _refine_roots!(workspace, low_workspace, checked, x2, fiber, low_fiber, final)
      if final
        state.step = max(state.step, remaining * _step_grow(state, ratio))
        return fiber
      end
      state.step *= _step_grow(state, ratio)
      failures = 0
    elseif status === :bisect && failures < _max_bisection_depth()
      failures += 1
      state.step = (final ? remaining : state.step) * _step_shrink(state, ratio)
    else
      _continuation_error(checked, state.x1, x2, failures, status)
    end
  end
end
