################################################################################
#
#  Analytic Continuation
#
################################################################################

mutable struct ContinuationWorkspace
  F::Vector{Vector{AcbFieldElem}}   # from _split_in_y(f)
  Ky::AcbPolyRing
  m::Int
  fx::AcbPolyRingElem               # f(x, .) for the current x
  lc::AcbFieldElem
  W::Vector{AcbFieldElem}
  P::AcbFieldElem
  t::AcbFieldElem
  a::ArbFieldElem
  dmin::ArbFieldElem
  wmax::ArbFieldElem
  absW::Vector{ArbFieldElem}        # |W_i|
  mv::Vector{ArbFieldElem}          # scratch: movement |zp_i - z_i| per root
  b::ArbFieldElem                   # scratch
  c::ArbFieldElem                   # scratch
  r::ArbFieldElem                   # scratch
  start_vec::Ptr{acb_struct}
  res_vec::Ptr{acb_struct}
  # contiguous copy of F for acb_dot: row j (0-based) = x-coefficients of y^j
  coef::Ptr{acb_struct}             # (m+1) x nx, row-major
  nx::Int
  rowlen::Vector{Int}               # row lengths without trailing zeros
  xpow::Ptr{acb_struct}             # 1, x, ..., x^(nx-1)
 
  function ContinuationWorkspace(F::Vector{Vector{AcbFieldElem}}, Ky::AcbPolyRing)
    CC = base_ring(Ky)
    RR = ArbField(precision(CC))
    m = length(F) - 1
    nx = maximum(length, F)
    sz = sizeof(acb_struct)
    coef = acb_vec((m + 1)*nx)
    rowlen = zeros(Int, m + 1)
    for j in 0:m, i in 0:nx-1
      p = coef + (j*nx + i)*sz
      if i < length(F[j+1])
        c = F[j+1][i+1]
        ccall((:acb_set, libflint), Nothing, (Ptr{acb_struct}, Ref{AcbFieldElem}), p, c)
        iszero(c) || (rowlen[j+1] = i + 1)
      else
        ccall((:acb_zero, libflint), Nothing, (Ptr{acb_struct},), p)
      end
    end
    ws = new(F, Ky, m, Ky([CC() for _ in F]), CC(), [CC() for _ in 1:m], CC(), CC(),
             RR(), RR(), RR(), [RR() for _ in 1:m], [RR() for _ in 1:m], RR(), RR(), RR(),
             acb_vec(m), acb_vec(m), coef, nx, rowlen, acb_vec(nx))
    finalizer(ws) do w
      acb_vec_clear(w.start_vec, w.m)
      acb_vec_clear(w.res_vec, w.m)
      acb_vec_clear(w.coef, (w.m + 1)*w.nx)
      acb_vec_clear(w.xpow, w.nx)
    end
    return ws
  end
end

#Let gamma be the path [-1,1] -> P^1 and let pi: RS -> P^1 
#be the projection given by (x,y) -> x
#This function performs analytic continuation along the path gamma
#by iteratively lifting the path along pi. It keeps track of all the
#different lifts y. 
#The output will be returned as a list of tuples 
#[(x0, [y_i]_0), ... (xn, [y_i]_n)] where the y_i correspond to all the lifts 
#over the respective x value. The xj correspond to the preimages of the input
#abscissae

function analytic_continuation(RS::RiemannSurfaceModel, path::CPath, abscissae::Vector{ArbFieldElem},
  start_ys::Vector{AcbFieldElem}=AcbFieldElem[], prec = 0)
  v = embedding(RS)
  if prec < precision(RS)
    prec = precision(RS)
  end

  RR = ArbField(prec)

  #Embed the polynomial in CC
  f = embed_mpoly(defining_polynomial(RS), v, prec)
  CC = base_ring(f)

  f = change_base_ring(CC, f, parent = parent(f))

  m = degree(f, 2)

  #Add start and end point to the abscissae
  u = vcat([-one(RR)], abscissae, [one(RR)])
  N = length(u)

  x_vals = Vector{AcbFieldElem}(undef, N)
  y_vals = [Vector{AcbFieldElem}(undef, m) for i in (1:N)]

  z = Vector{AcbFieldElem}(undef, m)

  #Compute x0
  x_vals[1] = evaluate(path, u[1])

  Kxy = parent(f)
  Ky, y = polynomial_ring(base_ring(Kxy), "y")

  # If we are given initial values we use those. If we don't we compute the
  # roots of f(x0, y)  0 and sort them.
  if length(start_ys) == 0
    y_vals[1] = sort!(_accurate_roots(f(x_vals[1], y), prec), lt = sheet_ordering)
  else
    y_vals[1] = start_ys
  end

  # For every tiny path piece from x_vals[l-1] to x_vals[l] we compute how
  # the ys that we lifted move along with them using recursive continuation.
  # We do this until we reach the end of the path
  ws = ContinuationWorkspace(_split_in_y(f), Ky)
  for l in 2:N
    x_vals[l] = evaluate(path, u[l])
    z .= y_vals[l-1]
    y_vals[l] .= recursive_continuation!(ws, x_vals[l-1], x_vals[l], z)
  end
  return x_vals, y_vals
end

function analytic_continuation(ws::ContinuationWorkspace, path::CPath,
                               abscissae::Vector{ArbFieldElem}, start_ys::Vector{AcbFieldElem})
  RR = parent(abscissae[1])
  u = vcat([-one(RR)], abscissae, [one(RR)])
  N = length(u)
  m = ws.m
  x_vals = Vector{AcbFieldElem}(undef, N)
  y_vals = [Vector{AcbFieldElem}(undef, m) for _ in 1:N]
  z = Vector{AcbFieldElem}(undef, m)
  x_vals[1] = evaluate(path, u[1])
  y_vals[1] = start_ys
  for l in 2:N
    x_vals[l] = evaluate(path, u[l])
    z .= y_vals[l-1]
    y_vals[l] .= recursive_continuation!(ws, x_vals[l-1], x_vals[l], z)
  end
  return x_vals, y_vals
end

# ws.fx <- f(x, y), ws.lc <- leading coefficient
function _specialize_x!(ws::ContinuationWorkspace, x::AcbFieldElem)
  prec = precision(parent(ws.lc))
  sz = sizeof(acb_struct)
  GC.@preserve ws begin
    _acb_powers_ptr!(ws.xpow, x, ws.nx - 1, prec)
    for j in 0:ws.m
      _acb_dot_ptr!(ws.lc, ws.coef + j*ws.nx*sz, ws.xpow, ws.rowlen[j+1], prec)
      setcoeff!(ws.fx, j, ws.lc)
    end
  end
  return ws.fx            # ws.lc now holds the y^m coefficient
end

# Fills ws.W with the Weierstrass corrections of z w.r.t. ws.fx and sets
# ws.dmin = min_{i<j} |z_i - z_j|, ws.wmax = max_i |W_i|.
function _weierstrass_corrections!(ws::ContinuationWorkspace, z::Vector{AcbFieldElem})
  m = ws.m
  first = true
  for i in 1:m
    Nemo.one!(ws.P)
    for j in 1:m
      j == i && continue
      sub!(ws.t, z[i], z[j])
      mul!(ws.P, ws.P, ws.t)
      if j > i
        Hecke.abs!(ws.a, ws.t)
        if first || ws.a < ws.dmin
          Hecke.set!(ws.dmin, ws.a)
          first = false
        end
      end
    end
    mul!(ws.P, ws.P, ws.lc)
    _acb_poly_evaluate!(ws.W[i], ws.fx, z[i])
    Nemo.div!(ws.W[i], ws.W[i], ws.P)
    Hecke.abs!(ws.a, ws.W[i])
    Hecke.set!(ws.absW[i], ws.a)
    if i == 1 || ws.a > ws.wmax
      Hecke.set!(ws.wmax, ws.a)
    end
  end
  return ws
end
 
function _max_bisection_depth()
  return 200
end

# The disks D(z_i, m|W_i|) contain the roots; they isolate them if they are
# pairwise disjoint: m(|W_i| + |W_j|) < |z_i - z_j| for all i < j. (Checked
# per pair, not as 2m max|W_i| < min|z_i - z_j|: when the roots have very
# different sizes, e.g. |y| from 1e-20 to 1e11 far out on a path, the
# large roots have large corrections but are also far apart, and the global
# version forces absurdly small steps.)
function _isolation_check!(ws::ContinuationWorkspace, x2::AcbFieldElem,
                           z::Vector{AcbFieldElem})
  _specialize_x!(ws, x2)
  _weierstrass_corrections!(ws, z)
  return _pairwise_check!(ws, z, false)[1]
end

# Checks  mv_i + mv_j + m(|W_i| + |W_j|) < |z_i - z_j|  for all pairs (the mv
# terms only if with_move, from ws.mv). Returns (status, q) with q the largest
# ratio lhs/rhs (Float64, NaN if not representable). ws.a and ws.dmin are set
# to lhs and rhs of the worst pair (for the step control and error messages).
function _pairwise_check!(ws::ContinuationWorkspace, z::Vector{AcbFieldElem}, with_move::Bool)
  m = ws.m
  status = :pass
  q = 0.0
  first = true
  for i in 1:m, j in i+1:m
    add!(ws.b, ws.absW[i], ws.absW[j])
    _arb_mul_si!(ws.b, ws.b, m)
    if with_move
      add!(ws.b, ws.b, ws.mv[i])
      add!(ws.b, ws.b, ws.mv[j])
    end
    sub!(ws.t, z[i], z[j])
    Hecke.abs!(ws.c, ws.t)
    Nemo.div!(ws.r, ws.b, ws.c)
    r = _arb_mid_f64(ws.r)
    if first || r > q || isnan(r)
      q = isnan(r) ? q : r
      Hecke.set!(ws.a, ws.b)
      Hecke.set!(ws.dmin, ws.c)
      first = false
    end
    if !(ws.b < ws.c)
      st = _fail_status(ws.b, ws.c)
      (status === :pass || st === :precision) && (status = st)
    end
  end
  return status, q
end

# Why a check `a < d` failed. :precision only if a is dominated by its own
# rounding error: then a smaller step does not help. If a is simply too large
# (a far too long step, e.g. the first step of a continuation without history)
# a smaller step does help, even when the absolute radius of a exceeds d.
function _fail_status(a::ArbFieldElem, d::ArbFieldElem)
  4*radius(a) < d && return :bisect
  return 4*radius(a) < abs(Nemo.midpoint(a)) ? :bisect : :precision
end

function _continuation_error(ws::ContinuationWorkspace, x1, x2, depth::Int, st::Symbol)
  C = AcbField(32); R = ArbField(32)
  reason = st === :precision ? "working precision too low to certify the step" :
                               "maximal bisection depth ($(_max_bisection_depth())) reached"
  error("Analytic continuation failed: $reason.\n" *
        "  x1 = $(C(x1)), x2 = $(C(x2)), depth = $depth, precision = $(precision(base_ring(ws.Ky)))\n" *
        "  worst pair of roots: |z_i - z_j| = $(R(ws.dmin)), m(|W_i| + |W_j|) (+ movement) = $(R(ws.a))\n" *
        "  Increase the precision (or check the radius of x1, x2).")
end

function recursive_continuation!(ws::ContinuationWorkspace, x1::AcbFieldElem,
                                 x2::AcbFieldElem, z::Vector{AcbFieldElem}, depth::Int = 0)
  m = ws.m
  CC = base_ring(ws.Ky)
  st = _isolation_check!(ws, x2, z)
  if st === :pass
    for i in 1:m
      sub!(ws.W[i], z[i], ws.W[i])            # start from z_i - W_i
    end
    dd = _find_roots_from!(ws, ws.W)
    @assert dd == m
    z .= array(CC, ws.res_vec, m)             # fresh elements: y_vals keeps them
    return z
  elseif st === :bisect && depth < _max_bisection_depth()
    midpoint = (x1 + x2)//2
    recursive_continuation!(ws, x1, midpoint, z, depth + 1)
    return recursive_continuation!(ws, midpoint, x2, z, depth + 1)
  else
    _continuation_error(ws, x1, x2, depth, st)
  end
end

#Recursive continuation without checking the proper bound that ensures
#we are close enough to ensure we are able to isolate roots properly
#and without using arb for the analytic continuation.
#This is useful when values start converging to infinity and checking
#bounds would get us into an infinite loop.

function recursive_continuation_manual!(ws::ContinuationWorkspace, x1::AcbFieldElem,
                                        x2::AcbFieldElem, z::Vector{AcbFieldElem},
                                        err::ArbFieldElem,
                                        target_error::ArbFieldElem = parent(err)(-1))
  m = ws.m
  CC = base_ring(ws.Ky)
  RR = parent(err)
 
  # private copy: the iteration below updates the entries in place
  zc = [CC() for _ in 1:m]
  for i in 1:m
    Hecke.set!(zc[i], z[i])
  end
 
  _specialize_x!(ws, x2)                 # f(x2, y) into ws.fx, no MPoly evaluation
  _weierstrass_corrections!(ws, zc)      # ws.W, ws.wmax = max |W_i|
  next_error = ws.wmax^2                 # same (squared) measure as the old code
  last_error = RR(1/0)
 
  # Durand-Kerner steps z_i <- z_i - W_i, as long as the corrections shrink
  while next_error > err && next_error < last_error
    for i in 1:m
      sub!(zc[i], zc[i], ws.W[i])
    end
    _weierstrass_corrections!(ws, zc)
    last_error = next_error
    next_error = ws.wmax^2
  end
 
  if target_error > RR(0) && next_error > target_error && next_error >= last_error
    return zc, true
  end
 
  fillacb!(ws.start_vec, zc)
  dd = ccall((:acb_poly_find_roots, libflint), Cint,
             (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int),
             ws.res_vec, ws.fx, ws.start_vec, 0, precision(CC))
  @assert dd == m
  return array(CC, ws.res_vec, m), false
end

################################################################################
#
#  Adaptive predictor-corrector continuation (used by the period matrix).
#
#  1. Predictor. Check at the secant prediction
#         zp_i = z_i(x1) + (z_i(x1) - z_i(x0)) * (x2 - x1)/(x1 - x0)
#     (x0 = previous accepted point). Its error is O(h * h_prev * z''), so
#     |W_i(zp)| is much smaller, larger steps pass, and acb_poly_find_roots
#     starts closer to the roots (fewer iterations).
#
#  2. Step control. The step size is kept across abscissae (and across the
#     intervals of a chunk). After a pass it grows, after a fail it shrinks by
#     a factor from q = (2m max|W_i|) / d, instead of always halving and
#     restarting at the full interval.
#
#  Certification. The Weierstrass check at zp shows: the disks D(zp_i, m|W_i|)
#  are disjoint and each contains exactly one root at x2. In addition we
#  require
#         2 max|zp_i - z_i(x1)| + 2m max|W_i|  <  min_{i<j} |z_i(x1) - z_j(x1)|,
#  i.e. every root moved less than half the separation at x1. Without a
#  predictor (zp = z) this is exactly the old condition, and with a predictor
#  it gives the same conclusion as before: a bijection between the fibers
#  with |y_i(x2) - z_i(x1)| < d(x1)/2. So the result is not less certified
#  than with the current method (it is still the heuristic check between two
#  points, as in Neurohr's method).
#
#  Intermediate points are exact (ball midpoints) points on the segment
#  x1 -> x_b; the bisection midpoints were also points on that segment.
#
################################################################################

mutable struct AdaptiveContinuationState
  x0::AcbFieldElem              # previous accepted point
  x1::AcbFieldElem              # current point
  x2::AcbFieldElem              # scratch: trial point
  z0::Vector{AcbFieldElem}      # fiber at x0 (check precision)
  zp::Vector{AcbFieldElem}      # predicted fiber at x2
  r::AcbFieldElem               # scratch
  t::AcbFieldElem               # scratch
  move::ArbFieldElem            # max |zp_i - z_i(x1)|
  dmin1::ArbFieldElem           # min |z_i(x1) - z_j(x1)|
  a::ArbFieldElem               # scratch
  h::Float64                    # step length |x2 - x1| to try next
  has_prev::Bool
  target::Float64               # aim for q = 2m max|W| / d around this value
  nchecks::Int                  # statistics
  nfail::Int

  function AdaptiveContinuationState(CL::AcbField, m::Int; target::Float64 = 0.25)
    RL = ArbField(precision(CL))
    return new(CL(), CL(), CL(), [CL() for _ in 1:m], [CL() for _ in 1:m], CL(), CL(),
               RL(), RL(), RL(), Inf, false, target, 0, 0)
  end
end

# Start (or restart) at the point x with fiber z: forget the history.
function _adaptive_reset!(st::AdaptiveContinuationState, x::AcbFieldElem,
                          z::Vector{AcbFieldElem})
  Hecke.set!(st.x1, x)
  st.has_prev = false
  st.h = Inf
  _min_dist!(st, z)
  return st
end

function _min_dist!(st::AdaptiveContinuationState, z::Vector{AcbFieldElem})
  m = length(z)
  first = true
  for i in 1:m, j in i+1:m
    sub!(st.t, z[i], z[j])
    Hecke.abs!(st.a, st.t)
    if first || st.a < st.dmin1
      Hecke.set!(st.dmin1, st.a)
      first = false
    end
  end
  return st.dmin1
end

# st.zp <- secant prediction at x2, st.move <- max |zp_i - z_i|
function _predict!(st::AdaptiveContinuationState, z::Vector{AcbFieldElem}, x2::AcbFieldElem)
  Nemo.zero!(st.move)
  if !st.has_prev
    for i in eachindex(z)
      Hecke.set!(st.zp[i], z[i])
    end
    return st.zp
  end
  sub!(st.t, x2, st.x1)
  sub!(st.r, st.x1, st.x0)
  # Previous step not resolvable at this precision (e.g. double exponential
  # abscissae piling up at an endpoint): no prediction, check at z itself.
  if contains_zero(st.r)
    return _no_prediction!(st, z)
  end
  Nemo.div!(st.r, st.t, st.r)                     # (x2 - x1)/(x1 - x0)
  for i in eachindex(z)
    sub!(st.t, z[i], st.z0[i])
    mul!(st.t, st.t, st.r)
    add!(st.zp[i], z[i], st.t)
    _acb_get_mid!(st.zp[i], st.zp[i])             # exact approximation
    isfinite(st.zp[i]) || return _no_prediction!(st, z)
    sub!(st.t, st.zp[i], z[i])
    Hecke.abs!(st.a, st.t)
    st.a > st.move && Hecke.set!(st.move, st.a)
  end
  return st.zp
end

function _no_prediction!(st::AdaptiveContinuationState, z::Vector{AcbFieldElem})
  Nemo.zero!(st.move)
  for i in eachindex(z)
    Hecke.set!(st.zp[i], z[i])
  end
  return st.zp
end

# Isolation check at the predicted fiber, plus the movement condition.
# Returns (status, q) with q ~ how much of the budget is used (pass needs q < 1).
# Both per pair of roots (see _isolation_check!):
#   isolation at zp:  m(|W_i| + |W_j|) < |zp_i - zp_j|
#   movement:         |zp_i - z_i| + |zp_j - z_j| + m(|W_i| + |W_j|) < |z_i - z_j|,
#                     z = the fiber at x1
function _adaptive_check!(ws::ContinuationWorkspace, st::AdaptiveContinuationState,
                          x2::AcbFieldElem, z1::Vector{AcbFieldElem})
  _specialize_x!(ws, x2)
  _weierstrass_corrections!(ws, st.zp)
  st_iso, q_iso = _pairwise_check!(ws, st.zp, false)
  for i in 1:ws.m
    sub!(ws.t, st.zp[i], z1[i])
    Hecke.abs!(ws.mv[i], ws.t)
  end
  st_move, q_move = _pairwise_check!(ws, z1, true)
  q = max(q_iso, q_move)
  st_iso === :pass || return st_iso, q
  return st_move, q
end

_step_grow(st, q) = !(q > 0) ? 2.0 : clamp(0.9*sqrt(st.target/q), 1.0, 2.0)
_step_shrink(st, q) = !(q > 0) ? 0.5 : clamp(0.9*sqrt(st.target/q), 0.25, 0.5)

# Continue the fiber from st.x1 to xb.
#   lo === nothing: z is the fiber (updated in place), zl must be z.
#   otherwise:      mixed precision as in recursive_continuation_mixed!: checks
#                   and intermediate roots in `lo` (zl), full precision roots
#                   at xb in `hi` (z).
function continue_adaptive!(st::AdaptiveContinuationState, hi::ContinuationWorkspace,
                            lo::Union{Nothing, ContinuationWorkspace}, xb::AcbFieldElem,
                            z::Vector{AcbFieldElem}, zl::Vector{AcbFieldElem})
  m = hi.m
  wsc = lo === nothing ? hi : lo
  fails = 0
  while true
    sub!(st.t, xb, st.x1)
    Hecke.abs!(st.a, st.t)
    rem = _arb_mid_f64(st.a)
    if !(rem > 0)
      # Either xb = x1, or |xb - x1| underflows in Float64 (double exponential
      # abscissae near the endpoints at high precision are far closer than
      # 1e-308): then go to xb in one step, which is still checked.
      _acb_get_mid!(st.r, st.t)
      iszero(st.r) && return z                    # already at xb
      rem = 0.0
    end
    final = !(st.h < rem * (1 - 1e-9))            # this step reaches xb
    if final
      x2 = xb
    else
      Nemo._arb_set(st.a, st.h / rem)
      mul!(st.t, st.t, st.a)
      add!(st.x2, st.x1, st.t)
      _acb_get_mid!(st.x2, st.x2)
      x2 = st.x2
    end

    _predict!(st, zl, x2)
    ws = wsc
    status, q = _adaptive_check!(ws, st, x2, zl)
    if status === :precision && lo !== nothing
      ws = hi                                     # tight cluster: check at full precision
      status, q = _adaptive_check!(ws, st, x2, zl)
    end
    st.nchecks += 1

    if status === :pass
      for i in 1:m
        sub!(ws.W[i], st.zp[i], ws.W[i])          # starting values zp_i - W_i
        Hecke.set!(st.z0[i], zl[i])                # history
      end
      Hecke.set!(st.x0, st.x1)
      Hecke.set!(st.x1, x2)
      st.has_prev = true

      done = false
      if lo !== nothing && !final && ws === lo
        if _find_roots_from!(lo, lo.W, 8) == m    # intermediate point: low precision
          for i in 1:m
            Nemo._acb_set(zl[i], lo.res_vec + (i - 1)*sizeof(acb_struct))
          end
          done = true
        end
      end
      if !done
        ws === hi || _specialize_x!(hi, x2)
        dd = _find_roots_from!(hi, ws.W)
        @assert dd == m
        for i in 1:m
          p = hi.res_vec + (i - 1)*sizeof(acb_struct)
          Nemo._acb_set(z[i], p)
          lo === nothing || _acb_set_round_ptr!(zl[i], p)
        end
      end
      # separation at the new point without recomputing it: the roots lie in
      # the disks D(zp_i, m|W_i|), so  d(x2) >= d(zp) - 2m max|W_i|
      sub!(st.dmin1, ws.dmin, ws.a)

      if final
        st.h = max(st.h, rem * _step_grow(st, q))
        return z
      end
      st.h *= _step_grow(st, q)
      fails = 0
    elseif status === :bisect && fails < _max_bisection_depth()
      st.nfail += 1
      fails += 1
      st.h = (final ? rem : st.h) * _step_shrink(st, q)
    else
      _continuation_error(ws, st.x1, x2, fails, status)
    end
  end
end

# In-place variant of recursive_continuation!: overwrites the entries of z
# instead of allocating m new AcbFieldElems per step. z must own its elements
# (not share them with anything that has to stay unchanged).
function recursive_continuation_inplace!(ws::ContinuationWorkspace, x1::AcbFieldElem,
                                         x2::AcbFieldElem, z::Vector{AcbFieldElem},
                                         depth::Int = 0)
  m = ws.m
  st = _isolation_check!(ws, x2, z)
  if st === :pass
    for i in 1:m
      sub!(ws.W[i], z[i], ws.W[i])
    end
    dd = _find_roots_from!(ws, ws.W)
    @assert dd == m
    for i in 1:m
      Nemo._acb_set(z[i], ws.res_vec + (i - 1)*sizeof(acb_struct))
    end
    return z
  elseif st === :bisect && depth < _max_bisection_depth()
    midpoint = (x1 + x2)//2
    recursive_continuation_inplace!(ws, x1, midpoint, z, depth + 1)
    return recursive_continuation_inplace!(ws, midpoint, x2, z, depth + 1)
  else
    _continuation_error(ws, x1, x2, depth, st)
  end
end

################################################################################
#
#  Optional mixed-precision continuation.
#
#  All isolation checks and the roots at bisection midpoints are computed in a
#  low-precision workspace `lo`; full precision (`hi`) is only used for the
#  roots at the target point of each top-level step (abscissae and chunk
#  boundaries). The check itself is still done in ball arithmetic, so it is
#  certified for the (low-precision) approximations it is applied to; whether
#  the chain of midpoint steps is fully rigorous in the sense of (4.19) still
#  has to be checked. Controlled by IntegrationParameters.midpoint_precision.
#
################################################################################

# Roots of ws.fx from the given starting values, into ws.res_vec, at the
# workspace's precision. Returns the number of isolated roots.
function _find_roots_from!(ws::ContinuationWorkspace, starts::Vector{AcbFieldElem}, attempts::Int = 0)
  fillacb!(ws.start_vec, starts)
  return ccall((:acb_poly_find_roots, libflint), Cint,
               (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int),
               ws.res_vec, ws.fx, ws.start_vec, attempts, precision(base_ring(ws.Ky)))
end

# A fiber from scratch at full precision (see _accurate_roots).
function _fresh_fiber!(ws::ContinuationWorkspace, x::AcbFieldElem, prec::Int)
  return _accurate_roots(_specialize_x!(ws, x), prec)
end

# Mixed precision, non-adaptive version (adaptive = false). If the
# low-precision check fails only because its balls are too wide (tight
# clusters of roots), the check is redone at full precision instead of
# bisecting forever.
function recursive_continuation_mixed!(lo::ContinuationWorkspace, hi::ContinuationWorkspace,
                                       x1::AcbFieldElem, x2::AcbFieldElem,
                                       z::Vector{AcbFieldElem}, zl::Vector{AcbFieldElem},
                                       final::Bool, depth::Int = 0)
  m = lo.m
  ws = lo
  st = _isolation_check!(lo, x2, zl)
  if st === :precision
    ws = hi
    st = _isolation_check!(hi, x2, zl)
  end

  if st === :pass
    for i in 1:m
      sub!(ws.W[i], zl[i], ws.W[i])           # starting values z_i - W_i
    end
    if !final && ws === lo
      if _find_roots_from!(lo, lo.W, 8) == m  # midpoint: low precision suffices
        for i in 1:m
          Nemo._acb_set(zl[i], lo.res_vec + (i - 1)*sizeof(acb_struct))
        end
        return zl
      end
    end
    ws === hi || _specialize_x!(hi, x2)
    dd = _find_roots_from!(hi, ws.W)
    @assert dd == m
    for i in 1:m
      p = hi.res_vec + (i - 1)*sizeof(acb_struct)
      Nemo._acb_set(z[i], p)
      _acb_set_round_ptr!(zl[i], p)
    end
    return zl
  elseif st === :bisect && depth < _max_bisection_depth()
    midpoint = (x1 + x2)//2
    recursive_continuation_mixed!(lo, hi, x1, midpoint, z, zl, false, depth + 1)
    return recursive_continuation_mixed!(lo, hi, midpoint, x2, z, zl, final, depth + 1)
  else
    _continuation_error(ws, x1, x2, depth, st)
  end
end
