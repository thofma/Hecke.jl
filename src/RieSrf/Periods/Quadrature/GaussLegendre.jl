################################################################################
#
#  RieSrf/Periods/Quadrature/GaussLegendre.jl : Gauss-Legendre quadrature
#
#  The integrals along the paths are computed with Gauss-Legendre quadrature
#  where the integrand is holomorphic on a large enough ellipse around the
#  path (Neurohr, Chapter 3 and Section 4.7). For every path this file
#  computes the ellipse parameter r (no discriminant point inside the image of
#  the ellipse E_r with foci -1 and 1), splits lines where that pays off, and
#  provides the nodes and the number of nodes for a given r.
#
#  Entry points: _gauss_legendre_path_parameters!, _gauss_legendre_parameters,
#  _gauss_legendre_nodes, _gauss_chebyshev_nodes.
#
################################################################################

@doc raw"""
    _gauss_legendre_nodes(N::IntegerUnion, prec::Int = 100)
      -> Vector{ArbFieldElem}, Vector{ArbFieldElem}

The abscissae and weights of the Gauss-Legendre quadrature with N nodes on
[-1, 1], at precision `prec` (Neurohr, Section 3.2.2).
"""
function _gauss_legendre_nodes(N::IntegerUnion, prec::Int = 100)
  RR = ArbField(prec)
  N = Int(N)
  half = floor(Int, (N + 1)//2)
  nodes = zeros_array(RR, half)
  weights = zeros_array(RR, half)
  Threads.@threads for l in 0:half-1
    ccall((:arb_hypgeom_legendre_p_ui_root, libflint), Nothing,
          (Ref{ArbFieldElem}, Ref{ArbFieldElem}, UInt, UInt, Int), nodes[l+1], weights[l+1], N, l, prec)
  end
  # the roots come as the positive half, the middle one (N odd) is 0
  if isodd(N)
    return vcat(-nodes, reverse(nodes[1:half-1])), vcat(weights, reverse(weights[1:half-1]))
  else
    return vcat(-nodes, reverse(nodes)), vcat(weights, reverse(weights))
  end
end

# The number of nodes N for which the error bound of Gauss-Legendre
# quadrature for integrands holomorphic on E_r and bounded by `bound` there is
# below `error` (Neurohr, Chapter 3).
function _gauss_legendre_parameters(r::ArbFieldElem, error::ArbFieldElem,
                                    bound::ArbFieldElem = parent(r)(10^5))
  @req isfinite(bound) "The bound for the integrand is not finite."
  @req r > 1 "The ellipse parameter r must be larger than 1 (got $r)."
  return Hecke.upper_bound(ZZRingElem, (log(64*(bound/15)) - log(error) -
                                        log(1 - exp(acosh(r))^(-2)))/(2*acosh(r)))
end

# The ellipse parameter of a path (and the subpaths of a line, see
# _split_line_segment!) with respect to the points (the discriminant points).
function _gauss_legendre_path_parameters!(points::Vector{AcbFieldElem}, path::CPath,
                                          error::ArbFieldElem)
  if is_line(path)
    set_subpaths!(path, _split_line_segment!(points, path, error))
  elseif is_arc(path)
    set_quadrature_parameter!(path, _gauss_legendre_arc_parameter!(points, path))
    set_subpaths!(path, [path])
  elseif is_circle(path)
    set_quadrature_parameter!(path, _gauss_legendre_circle_parameter!(points, path))
    set_subpaths!(path, [path])
  end
end

# Neurohr, Section 4.7.5: if a point is close to the line (r < 1.2), split the
# line at the point of the line closest to it (but at most 3/4 of the way to
# an end) if the two pieces together need at least 10 nodes fewer. Recursive;
# returns the pieces.
function _split_line_segment!(points::Vector{AcbFieldElem}, path::CPath, error::ArbFieldElem)
  if !isdefined(path, :quadrature_parameter)
    set_quadrature_parameter!(path, _gauss_legendre_line_parameter!(points, path))
  end
  quadrature_parameter(path) < 1.2 || return [path]

  prec = precision(parent(points[1]))
  RR = ArbField(prec)
  CC = AcbField(prec)
  t = closest_disc_point_parameter(path)
  if abs(real(t)) < 3/4
    x = evaluate(path, real(t))
  else
    x = evaluate(path, RR(sign(Int, real(t))*3/4))
  end
  first_piece = line_path(start_point(path), x, CC)
  second_piece = line_path(x, end_point(path), CC)
  set_quadrature_parameter!(first_piece, _gauss_legendre_line_parameter!(points, first_piece))
  set_quadrature_parameter!(second_piece, _gauss_legendre_line_parameter!(points, second_piece))

  N = _gauss_legendre_parameters(quadrature_parameter(path), error)
  N1 = _gauss_legendre_parameters(quadrature_parameter(first_piece), error)
  N2 = _gauss_legendre_parameters(quadrature_parameter(second_piece), error)
  set_number_of_nodes!(path, N)
  set_number_of_nodes!(first_piece, N1)
  set_number_of_nodes!(second_piece, N2)

  N - N1 - N2 >= 10 || return [path]
  return vcat(_split_line_segment!(points, first_piece, error),
              _split_line_segment!(points, second_piece, error))
end

# (|t + 1| + |t - 1|)/2: the parameter r of the ellipse E_r through t.
_ellipse_parameter(t) = (abs(t + 1) + abs(t - 1)) / 2

# The ellipse parameter r_0 of a path: the largest r <= 5 such that no point
# lies inside the image of E_r under the path. The parameter t of the closest
# point is stored in the path (the integrand bound is sampled near it). If no
# point is closer than r = 5, the path gets the fixed integrand bound 1
# (_ellipse_bound_heuristic! then gives it the scheme with the largest r).
function _gauss_legendre_line_parameter!(points::Vector{AcbFieldElem}, path::CPath)
  CC = parent(points[1])
  RR = ArbField(precision(CC))
  r_0 = RR(5)
  a = start_point(path)
  b = end_point(path)
  for p in points
    t_p = (2*p - a - b)//(b - a)             # path(t_p) = p
    r_p = _ellipse_parameter(t_p)
    @req r_p > 1 "A discriminant point lies on a path of integration."
    if r_p < r_0
      r_0 = r_p
      set_closest_disc_point_parameter!(path, t_p)
    end
  end
  r_0 == RR(5) && push!(path.bounds, RR(1))
  return r_0
end

# The same for arcs and circles. The points are the discriminant points (at a
# high precision, e.g. 600 bits), but r_0 and t_p are only used to choose the
# quadrature and to place the sample points of the heuristic bounds, so they
# are computed at _arc_parameter_precision() bits (t_p needs a log per point);
# only a point for which r_p cannot be separated from 1 there (a point
# extremely close to the path) is done again at full precision.
_arc_parameter_precision() = 128

function _gauss_legendre_arc_circle_parameter!(points::Vector{AcbFieldElem}, path::CPath)
  CC = parent(points[1])
  RR = ArbField(precision(CC))
  r_0 = RR(5)
  c = center(path)
  low_prec = min(precision(CC), _arc_parameter_precision())
  parameter_low = _arc_parameter_function(path, AcbField(low_prec))
  parameter_high = nothing
  for p in points
    contains(c - p, zero(CC)) && continue
    t_p = parameter_low(p)
    r_p = _ellipse_parameter(t_p)
    if !(r_p > 1) && low_prec < precision(CC)
      parameter_high === nothing && (parameter_high = _arc_parameter_function(path, CC))
      t_p = parameter_high(p)
      r_p = _ellipse_parameter(t_p)
    end
    @req r_p > 1 "A discriminant point lies on a path of integration."
    if r_p < r_0
      r_0 = RR(r_p)
      set_closest_disc_point_parameter!(path, CC(t_p))
    end
  end
  r_0 == RR(5) && push!(path.bounds, RR(1))
  return r_0
end

_gauss_legendre_arc_parameter!(points::Vector{AcbFieldElem}, path::CPath) =
  _gauss_legendre_arc_circle_parameter!(points, path)

_gauss_legendre_circle_parameter!(points::Vector{AcbFieldElem}, path::CPath) =
  _gauss_legendre_arc_circle_parameter!(points, path)

# The abscissae and weights of the Gauss-Chebyshev quadrature with N nodes
# (used by the algorithm for superelliptic curves).
function _gauss_chebyshev_nodes(N::IntegerUnion, prec::Int = 100)
  RR = ArbField(prec)
  pi_over_2N = const_pi(RR)//(2*N)
  half = floor(Int, N//2)
  nodes = zeros_array(RR, half)
  for l in 1:half
    nodes[l] = cos(pi_over_2N * (2*l - 1))
  end
  abscissae = isodd(N) ? vcat(-nodes, [zero(RR)], reverse(nodes)) : vcat(-nodes, reverse(nodes))
  return abscissae, fill(const_pi(RR)//N, N)
end
