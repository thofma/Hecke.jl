################################################################################
#
#  RieSrf/Paths/CPath.jl : paths and chains in the complex plane
#
#  The x-plane is connected by paths (lines, arcs, circles; types in
#  Types.jl), parametrized over [-1, 1]. The quadrature integrates along them
#  in this parametrization. Chains are sequences of connected paths; the
#  loops around the discriminant points (Topology.jl) are closed chains.
#
#  Each path also carries the data computed for it: the permutation of the
#  sheets along it (monodromy), the quadrature parameters and the matrix of
#  the integrals of the differentials along its lifts. The reverse path
#  shares these (with the inverse permutation, minus the permuted integrals).
#
################################################################################

################################################################################
#
#  Constructors
#
################################################################################

@doc raw"""
    line_path(start_point::AcbFieldElem, end_point::AcbFieldElem, CC = parent(start_point)) -> CPath

The line from `start_point` to `end_point`; its points have the precision
of `CC`.
"""
line_path(start_point::AcbFieldElem, end_point::AcbFieldElem, CC::AcbField = parent(start_point)) =
  CPath(:line, start_point, end_point, CC)

@doc raw"""
    arc_path(start_point, end_point, center, CC = parent(start_point); orientation = 1) -> CPath

The arc around `center` from `start_point` to `end_point`, counterclockwise
for `orientation = 1` and clockwise for `orientation = -1`. If the start and
end point are the same, the full circle.
"""
function arc_path(start_point::AcbFieldElem, end_point::AcbFieldElem, center::AcbFieldElem,
                  CC::AcbField = parent(start_point); orientation::Int = 1)
  radius = abs(start_point - center)
  if contains(end_point, start_point) && contains(start_point, end_point)
    return CPath(:circle, start_point, start_point, CC; center = center, radius = radius,
                 orientation = orientation)
  end
  return CPath(:arc, start_point, end_point, CC; center = center, radius = radius,
               orientation = orientation)
end

@doc raw"""
    circle_path(start_point, center, CC = parent(start_point); orientation = 1) -> CPath

The circle around `center` that starts and ends at `start_point`.
"""
circle_path(start_point::AcbFieldElem, center::AcbFieldElem, CC::AcbField = parent(start_point);
            orientation::Int = 1) =
  arc_path(start_point, start_point, center, CC; orientation = orientation)

# A path that stays at one point: the neutral element for concatenating.
point_path(point::AcbFieldElem, CC::AcbField = parent(point)) =
  CPath(:point, point, point, CC; center = point)

@doc raw"""
    line_to_infinity(start_point::AcbFieldElem) -> CPath

The ray from `start_point` (not 0) to infinity, x(t) = 2 start_point/(1 - t).
"""
function line_to_infinity(start_point::AcbFieldElem, CC::AcbField = parent(start_point))
  @req !iszero(start_point) "The line to infinity cannot start at zero."
  return CPath(:line_to_infinity, start_point, start_point, CC)
end

################################################################################
#
#  Type, getters and setters
#
################################################################################

path_type(path::CPath) = path.path_type
is_line(path::CPath) = path.path_type === :line
is_arc(path::CPath) = path.path_type === :arc
is_circle(path::CPath) = path.path_type === :circle

start_point(path::CPath) = path.start_point
end_point(path::CPath) = path.end_point
start_angle(path::CPath) = path.start_angle
end_angle(path::CPath) = path.end_angle
orientation(path::CPath) = path.orientation
length(path::CPath) = path.length

function center(path::CPath)
  @req is_arc(path) || is_circle(path) "The path is not an arc or a circle."
  return path.center
end

function radius(path::CPath)
  @req is_arc(path) || is_circle(path) "The path is not an arc or a circle."
  return path.radius
end

permutation(path::CPath) = path.permutation

# The permutation along the reverse path is the inverse one.
function set_permutation!(path::CPath, sigma::Perm{Int})
  path.permutation = sigma
  isdefined(path, :reverse_path) && (path.reverse_path.permutation = inv(sigma))
  return path
end

function set_integral_matrix!(path::CPath, M::AcbMatrix)
  path.integral_matrix = M
  isdefined(path, :reverse_path) && _set_reverse_integral!(path)
  return path
end

# Along the reverse path the lift starting on sheet sigma(s) is the reverse
# of the lift starting on sheet s: its integrals are minus the permuted ones.
function _set_reverse_integral!(path::CPath)
  M = path.integral_matrix
  if isdefined(path, :permutation) && nrows(M) == parent(path.permutation).n
    path.reverse_path.integral_matrix = path.permutation * -M
  end
  return path
end

closest_disc_point_parameter(path::CPath) = path.closest_disc_point_parameter
set_closest_disc_point_parameter!(path::CPath, t::AcbFieldElem) = (path.closest_disc_point_parameter = t; path)

quadrature_parameter(path::CPath) = path.quadrature_parameter
set_quadrature_parameter!(path::CPath, r::ArbFieldElem) = (path.quadrature_parameter = r; path)

set_number_of_nodes!(path::CPath, N::ZZRingElem) = (path.number_of_nodes = N; path)

subpaths(path::CPath) = path.subpaths
set_subpaths!(path::CPath, paths::Vector{CPath}) = (path.subpaths = paths; path)

################################################################################
#
#  IO
#
################################################################################

function show(io::IO, path::CPath)
  CC = AcbField(30)
  RR = ArbField(30)
  x0 = start_point(path)
  x1 = end_point(path)
  if is_line(path) || path_type(path) === :line_to_infinity
    print(io, "Line from $(CC(x0)) to $(CC(x1)).")
  elseif path_type(path) === :point
    print(io, "Point at $(CC(x0)).")
  elseif is_arc(path)
    print(io, "Arc around $(CC(center(path))) with radius $(RR(radius(path))) starting at $(CC(x0)) and ending at $(CC(x1)).")
  else
    print(io, "Circle around $(CC(center(path))) with radius $(RR(radius(path))) starting at $(CC(x0)).")
  end
end

################################################################################
#
#  Reverse path
#
################################################################################

@doc raw"""
    reverse(path::CPath) -> CPath

The reverse path t -> path(-t). It is created once and linked to `path`;
the permutation and the integrals of either are passed on to the other.
"""
function reverse(path::CPath)
  isdefined(path, :reverse_path) && return path.reverse_path
  CC = parent(path.start_point)
  @req is_line(path) || is_arc(path) || is_circle(path) "Only lines, arcs and circles can be reversed."
  if is_line(path)
    reversed = line_path(path.end_point_high, path.start_point_high, CC)
  else
    reversed = arc_path(path.end_point_high, path.start_point_high, path.center_high, CC;
                        orientation = -orientation(path))
  end
  reversed.reverse_path = path
  path.reverse_path = reversed
  isdefined(path, :permutation) && (reversed.permutation = inv(path.permutation))
  isdefined(path, :integral_matrix) && _set_reverse_integral!(path)
  return reversed
end

################################################################################
#
#  Evaluation
#
################################################################################

@doc raw"""
    evaluate(path::CPath, t::FieldElem) -> FieldElem

The point x(t) of the path (t in [-1, 1]; see CPath for the parametrizations).
"""
function evaluate(path::CPath, t::FieldElem)
  a = start_point(path)
  type = path_type(path)
  if type === :line
    b = end_point(path)
    return (a + b)//2 + (b - a)//2 * t
  elseif type === :point
    return a
  elseif type === :line_to_infinity
    return 2 * a / (1 - t)
  end
  phi_a = path.start_angle
  phi_b = path.end_angle
  i = onei(parent(a))
  if type === :arc
    return path.center + path.radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * t))
  end
  # circle
  pi = real(const_pi(parent(a)))
  return path.center - path.radius * exp(i * (phi_a + path.orientation * pi * t))
end

@doc raw"""
    evaluate_derivative(path::CPath, t::FieldElem) -> FieldElem

The derivative dx/dt of the path at t.
"""
function evaluate_derivative(path::CPath, t::FieldElem)
  a = start_point(path)
  type = path_type(path)
  if type === :line
    return (end_point(path) - a)//2
  elseif type === :point
    return zero(parent(a))
  elseif type === :line_to_infinity
    return 2 * a / (1 - t)^2
  end
  phi_a = path.start_angle
  phi_b = path.end_angle
  i = onei(parent(a))
  if type === :arc
    return i * (phi_b - phi_a)//2 * path.radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * t))
  end
  # circle
  pi = real(const_pi(parent(a)))
  return -path.orientation * i * pi * path.radius * exp(i * (phi_a + path.orientation * pi * t))
end

# For an arc or a circle: the function x -> t with path(t) = x, where the
# parametrization is continued to complex t (for a point x off the path, t
# tells how far x is from the path in the parameter domain). Computed in CC,
# which may have a lower precision than the path. trim_zero: the log is
# ambiguous for points on the real or imaginary axis; the ambiguity drops
# out of the absolute values and imaginary parts that are taken afterwards.
function _arc_parameter_function(path::CPath, CC::AcbField)
  RR = ArbField(precision(CC))
  I = onei(CC)
  a = RR(start_angle(path))
  b = RR(end_angle(path))
  c = CC(center(path))
  r = RR(radius(path))
  o = orientation(path)
  if is_circle(path)
    E = r * exp(I * a)
    scale = -o / const_pi(RR) * I
    return x -> scale * log(trim_zero((c - CC(x)) / E))
  else
    E = r * exp(I * (b + a) / 2)
    scale = o / (b - a) * (-2 * I)
    return x -> scale * log(trim_zero((CC(x) - c) / E))
  end
end

################################################################################
#
#  Equality
#
################################################################################

# Same type and geometry (an arc also equals the reverse of the arc with the
# opposite orientation; a circle does not depend on its start point).
function ==(path1::CPath, path2::CPath)
  path_type(path1) === path_type(path2) || return false
  same_ends = start_point(path1) == start_point(path2) && end_point(path1) == end_point(path2)
  if is_line(path1)
    return same_ends
  elseif is_arc(path1)
    same_arc = center(path1) == center(path2)
    return same_arc && ((same_ends && orientation(path1) == orientation(path2)) ||
                        (start_point(path1) == end_point(path2) && end_point(path1) == start_point(path2) &&
                         orientation(path1) == -orientation(path2)))
  elseif is_circle(path1)
    return center(path1) == center(path2) && radius(path1) == radius(path2) &&
           orientation(path1) == orientation(path2)
  end
  return start_point(path1) == start_point(path2)
end

################################################################################
#
#  Lines and circles
#
################################################################################

# The orthogonal projection of the point c onto the line through the line path.
function orthogonal_projection(line::CPath, c::AcbFieldElem)
  @req is_line(line) "The first argument must be a line."
  a = start_point(line)
  direction = end_point(line) - a
  return a + ((real(c - a) * real(direction) + imag(c - a) * imag(direction)) /
              (direction * conjugate(direction))) * direction
end

# Whether the line path meets the disk bounded by the circle path (with the
# projection of the center onto the line between the end points). Returns
# (true, projection of the center) or (false, 0).
function line_intersect_circle(line::CPath, circle::CPath)
  c = center(circle)
  projection = orthogonal_projection(line, c)
  CC = parent(projection)
  RR = ArbField(precision(CC))
  line_length = length(line)
  projection_distance = abs(start_point(line) - projection)
  if projection_distance <= line_length
    point = evaluate(line, 2*projection_distance/line_length - 1)
    if contains(abs(point - projection), zero(RR)) && abs(c - projection) <= radius(circle)
      return true, projection
    end
  end
  return false, CC(0)
end

# The intersection points of the line path with the circle path, ordered by
# their distance from the start of the line: (true, [p1, p2]) or
# (false, []). (If the start of the line lies on the circle, p1 is the start.)
function intersection_points(line::CPath, circle::CPath)
  @req is_line(line) && is_circle(circle) "The arguments must be a line and a circle."
  intersects, projection = line_intersect_circle(line, circle)
  intersects || return false, AcbFieldElem[]
  a = start_point(line)
  r = radius(circle)
  RR = parent(r)
  line_length = length(line)
  # Pythagoras: the intersection points lie at distance sqrt(r^2 - d^2) from
  # the projection of the center (d the distance of the center to the line)
  center_distance = abs(center(circle) - projection)
  projection_distance = abs(a - projection)
  half_chord = sqrt(r^2 - center_distance^2)
  points = AcbFieldElem[]
  first_distance = projection_distance - half_chord
  if contains(abs(first_distance), zero(RR))
    push!(points, a)
  else
    push!(points, evaluate(line, 2*first_distance/line_length - 1))
  end
  second_distance = projection_distance + half_chord
  push!(points, evaluate(line, 2*second_distance/line_length - 1))
  if abs(points[1] - a) <= abs(points[2] - a)
    return true, points
  end
  return true, reverse(points)
end

################################################################################
#
#  Chains
#
################################################################################

# Whether the paths are connected (each one starts where the previous one
# ends) and whether the chain they form is closed: (is_connected, is_closed).
function test_chain(paths::Vector{CPath})
  CC = paths[1].field
  for i in 1:length(paths) - 1
    contains(end_point(paths[i]) - start_point(paths[i + 1]), zero(CC)) || return false, false
  end
  return true, contains(start_point(paths[1]) - end_point(paths[end]), zero(CC))
end

length(chain::CChain) = length(chain.paths)
permutation(chain::CChain) = chain.permutation
start_point(chain::CChain) = chain.start_point
end_point(chain::CChain) = chain.end_point
center(chain::CChain) = chain.center
is_closed(chain::CChain) = chain.is_closed
points(chain::CChain) = chain.points::Vector{RiemannSurfacePoint}

# The integral matrix of a chain from those of its paths. After a path the
# sheets are permuted, so the matrix of the next path is added with its rows
# permuted: row s of the chain matrix collects the integrals along the lift
# that starts on sheet s.
function _set_chain_integral!(chain::CChain)
  paths = chain.paths
  symmetric_group = parent(chain.permutation)
  m = symmetric_group.n
  CC = base_ring(paths[1].integral_matrix)
  g = ncols(paths[1].integral_matrix)
  prec = precision(CC)
  chain_integral = zero_matrix(CC, m, g)
  sigma = one(symmetric_group)
  rows = matrix(ZZ, m, 1, collect(1:m))
  for path in paths
    # inv(sigma) * M: row r of it is row source_rows[r] of M. Added in place,
    # without the generic product with a permutation and without copying the
    # entries (this took 13% of the time for f19).
    source_rows = inv(sigma) * rows
    M = path.integral_matrix
    GC.@preserve chain_integral M for r in 1:m
      k = Int(source_rows[r, 1])
      for j in 1:g
        entry = _acb_mat_entry_ptr(chain_integral, r, j)
        ccall((:acb_add, libflint), Nothing, (Ptr{acb_struct}, Ptr{acb_struct}, Ptr{acb_struct}, Int),
              entry, entry, _acb_mat_entry_ptr(M, k, j), prec)
      end
    end
    sigma *= permutation(path)
  end
  chain.integral_matrix = chain_integral
  return chain
end

function show(io::IO, chain::CChain)
  n = length(chain)
  CC = AcbField(30)
  if n == 0
    print(io, "Empty chain.")
  elseif is_closed(chain)
    x0 = start_point(chain)
    if isdefined(chain, :center)
      print(io, "Closed chain consisting of $(n) paths starting at $(CC(x0)) around $(CC(center(chain))).\n")
    else
      print(io, "Closed chain consisting of $(n) paths starting at $(CC(x0)).\n")
    end
  else
    print(io, "Chain consisting of $(n) paths starting at $(CC(start_point(chain))) and ending at $(CC(end_point(chain))).\n")
  end
  isdefined(chain, :permutation) && print(io, "With permutation $(permutation(chain)).")
end

# The loop around infinity as the product of the inverses of the loops around
# all discriminant points (in reverse order), freely reduced: a path followed
# by its reverse cancels. The reduced word is the walk around the spanning tree
# (every line piece twice, every arc once), instead of the sum of all chains,
# where the pieces near the base point occur once per discriminant point
# behind them; this matters for the radius of its integral. The loops with
# trivial monodromy do not change the permutation, and their integrals vanish.
function make_inf_chain(chains::Vector{CChain})
  paths = CPath[]
  CC = parent(start_point(chains[1].paths[1]))
  for chain in reverse(chains), path in reverse(chain.paths)
    if !isempty(paths) && paths[end] === path
      pop!(paths)                          # path followed by reverse(path)
    else
      push!(paths, reverse(path))
    end
  end
  inf_chain = CChain(paths)
  inf_chain.center = CC(1/0)
  return inf_chain
end

*(chain1::CChain, chain2::CChain) = CChain(vcat(chain1.paths, chain2.paths))

function ^(chain::CChain, k::Int)
  @req abs(k) <= 1 || is_closed(chain) "Only closed chains can be raised to powers other than -1, 0, 1."
  k == 0 && return CChain([point_path(start_point(chain))])
  k < 0 && return inv(chain)^(-k)
  result = chain
  for _ in 2:k
    result *= chain
  end
  return result
end

inv(chain::CChain) = CChain(reverse([reverse(path) for path in chain.paths]))
