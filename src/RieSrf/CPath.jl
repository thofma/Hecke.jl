################################################################################
#
#          RieSrf/CPath.jl : Paths in C
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export CPath

export c_line, c_arc, start_point, end_point, path_type, reverse, assign_permutation, permutation,
start_arc, end_arc, get_int_param_r, set_int_param_r, set_t_of_closest_d_point,
get_t_of_closest_d_point, evaluate_d

################################################################################
#
#  Constructors
#
################################################################################

#The class Cpath represents a path in the complex plane. It can be either
# a line, an arc, a circle, a point or a line to infinity.

mutable struct CPath

  path_type::Int
  #Path type index:
  #0 is a line
  #1 is an arc
  #2 is a circle
  #3 is a point

  #The field in which the path lies
  C::AcbField

  #The start point and the end point of the path
  start_point::AcbFieldElem
  end_point::AcbFieldElem

  #The start point and the end point of the path with higher precision
  start_point_high::AcbFieldElem
  end_point_high::AcbFieldElem

  #If the path is an arc or a circle, it will be described by the center,
  #the radius, and the start and end angles. (c + r*e^(ix))
  center::AcbFieldElem
  radius::ArbFieldElem
  start_arc::ArbFieldElem
  end_arc::ArbFieldElem

  center_high::AcbFieldElem
  radius_high::ArbFieldElem
  start_arc_high::ArbFieldElem
  end_arc_high::ArbFieldElem

  #The orientation determines how we move from start point to end point
  #If the orientation is 1 we move counterclockwise and if the orientation
  # is -1 we move clockwise.
  orientation::Int

  #The length of the path
  length::ArbFieldElem
  length_high::ArbFieldElem


  #Let f be the equation defining a plane curve in RiemannSurface.jl
  #Let x_0 = gamma(start_point) and let (y_1, ..., y_d) be the roots
  #of the equation f(x_0, y) sorted by the sheet_ordering function
  #from Auxiliary.jl. Using analytic continuation along the path gamma
  #to x_end = gamma(end_point) gives us a new set of roots (z_1, ..., z_d)
  #solving f(x_end, y). Sorting these once again using the sheet_ordering
  #function gives us a permutation (z_sigma(1), ..., z_sigma(d)). The variable
  #sigma stores this permutation. In the case that gamma is a closed path,
  #sigma will tell us exactly how the sheets got permuted.
  permutation::Perm{Int}

  sheets::Vector{AcbFieldElem}

  #For the purposes of integrating along a path to compute the period matrix
  #we store additional properties. Here is a description
  #of their meanings. Most of these are discussed in  Chapter 3
  #of Neurohr's thesis.

  #For integration we want the function f we integrate along gamma to be
  #bounded. For this we take an ellipsoid e_r with focal points -1,1
  #paramatrized by r*cos(t) + i*sqrt(1-r^2) which contains the path gamma.
  #And then we determine an M such that |gamma(e_r)|< M.
  #During computations we determine an optimal r to find proper error bounds
  #This r is stored with the path and called int_param_r.
  int_param_r::ArbFieldElem

  #Let D be the set of points where disc(f) = 0. Let P be the point in D
  #for which the distance between gamma and P is minimal. Now
  #t_of_closest_d_point is the variable t0 for which gamma(t0) = P.
  t_of_closest_d_point::AcbFieldElem

  #The number of abscissae of the path
  int_params_N::Int

  #The bounds M computed
  bounds::Vector{ArbFieldElem}

  #The index of the integration scheme that should be used to compute the
  #integral along this path
  integration_scheme_index::Int

  #If the path is long it, splitting it it into subpaths and computing
  #integrals along those subpaths may be faster.
  sub_paths::Vector{CPath}

  #Let X be a Riemann surface X defined by an equation f(x,y) = 0.
  #Let g be the genus of X, and let m be the degree of the map pi:X -> P^1
  #given by (x,y)-> x. Then integral_matrix will is the m x g matrix one gets
  #by integrating the g differential forms forming a basis of H^0(X, K_X)
  #(computed in RiemannSurface.jl) along the m distinct paths that are lifts
  #of gamma along pi.
  integral_matrix::AcbMatrix


  #Constructor of CPath.
  function CPath(a::AcbFieldElem, b::AcbFieldElem, path_type::Int, CC_low::AcbField = parent(a), c::AcbFieldElem = zero(parent(a)), radius::ArbFieldElem = real(zero(parent(a))), orientation::Int = 1)

    P = new()
    RR_low = ArbField(precision(CC_low))
    CC = parent(a)
    P.C = CC

    P.start_point_high = a
    P.end_point_high = b

    A = CC_low(a)
    B = CC_low(b)

    P.start_point = A
    P.end_point = B
    
    P.path_type = path_type

    P.center_high = c
    P.radius_high = radius


    P.center = CC_low(c)
    P.radius = RR_low(radius)
    P.orientation = orientation
    P.bounds = ArbFieldElem[]

    RR = ArbField(precision(CC))

    if path_type == 0
      length = abs(B - A)
    end

    if path_type == 3
      length = RR_low(0)
    end

    if path_type == 4
      P.end_point = CC(1/0)
      length = RR(1/0)
    end
  
    #If the path is not a line we need some additional constants to compute
    #length, parametrization, etc.
    i = onei(CC)
    piC = real(const_pi(CC))

    #Round real or imaginary part to zero to compute angle if necessary
    #zero_sens = floor(Int, prec*log(2)/log(10)) - 5

    a_diff = trim_zero(a - c)
    b_diff = trim_zero(b - c)

    #a_diff = trim_zero(a - c, zero_sens)
    #b_diff = trim_zero(b - c, zero_sens)

    phi_a = mod2pi(angle(a_diff))
    phi_b = mod2pi(angle(b_diff))


    if orientation == 1
      if phi_b < phi_a
        phi_b += 2*piC
      end
    elseif orientation == - 1
       if phi_a < phi_b
        phi_a += 2*piC
      end
    end

    P.start_arc = phi_a
    P.end_arc = phi_b

    #If the path is an arc
    if path_type == 1
      length = abs((phi_b - phi_a)) * radius
    end

    #If the path is a circle
    if path_type == 2
      length = 2 * piC * radius
    end

    P.length = length
    return P
  end
end

@doc raw"""
c_line(start_point::AcbFieldElem, end_point::AcbFieldElem) -> CPath

Construct a line in C from start_point to end_point.
"""
function c_line(start_point::AcbFieldElem, end_point::AcbFieldElem, CC::AcbField = parent(start_point))
  return CPath(start_point, end_point, 0, CC)
end

@doc raw"""
c_arc(start_point::AcbFieldElem, end_point::AcbFieldElem, center::AcbFieldElem; orientation::Int = 1)
  -> CPath

Construct an arc around ''center'' in C from ''start_point'' to
''end_point''. If orientation is 1 the path goes counterclockwise.
If it is -1 it goes clockwise. If start_point and end_point are identical
a circle is created instead.
"""
function c_arc(start_point::AcbFieldElem, end_point::AcbFieldElem, center::AcbFieldElem, CC::AcbField = parent(start_point);
  orientation::Int = 1)
  #TODO: We might need a check that start point and end_point are equally
  #far away from center.
  if contains(end_point, start_point) && contains(start_point, end_point)
    return CPath(start_point, start_point, 2, CC, center, abs(start_point - center), orientation)
  else
    return CPath(start_point, end_point, 1, CC, center, abs(start_point - center), orientation)
  end
end

@doc raw"""
c_circle(start_point::AcbFieldElem, center::AcbFieldElem; orientation::Int = 1)
  -> CPath

Construct a circle around ''center'' in C beginning and ending at ''start_point''
If orientation is 1 the path goes counterclockwise. If it is -1 it goes clockwise. 
"""
function c_circle(start_point::AcbFieldElem, center::AcbFieldElem, CC::AcbField = parent(start_point); orientation::Int = 1)
  return c_arc(start_point, start_point, CC, center, orientation = orientation)
end

@doc raw"""
c_point(point::AcbFieldElem)
  -> CPath

Construct path that is just a point. This is only useful as an initial element when 
concatenating paths.
"""
function c_point(point::AcbFieldElem, CC::AcbField)
  return CPath(point, point, 3,CC, point)
end

@doc raw"""
c_infinite_line(point::AcbFieldElem)
  -> CPath

Construct a path in C from ''start_point'' to infinity.
"""
function c_infinite_line(start_point::AcbFieldElem, CC::AcbField = parent(start_point))
  CC = parent(start_point)
  @req start_point != CC(0) "Line to infinity cannot start from zero."
  return CPath(start_point, start_point, 4, CC)
end

################################################################################
#
#  IO
#
################################################################################


function show(io::IO, gamma::CPath)
  CC = AcbField(30)
  RR = ArbField(30)
  p_type = path_type(gamma)
  if p_type< 0 || p_type > 4
    error("Path type does not exist")
  end

  x0 = start_point(gamma)
  x1 = end_point(gamma)
  if p_type == 0 || p_type == 4
    print(io, "Line from $(CC(x0)) to $(CC(x1)).")
  elseif p_type ==3
    print(io, "Point at  $(CC(x0)).")
  else
    r = radius(gamma)
    c = center(gamma)
    if p_type == 1
      print(io, "Arc around $(CC(c)) with radius $(RR(r)) starting at $(CC(x0)) and ending at $(CC(x1)).")
    elseif p_type == 2
      print(io, "Circle around $(CC(c)) with radius $(RR(r)) starting at $(CC(x0)).")
    end
  end
end

################################################################################
#
#  Reverse path
#
################################################################################

@doc raw"""
reverse(G::CPath) -> CPath

Given a path G:[-1,1] -> C returns the reverse of the path
G_rev:[-1,1] -> C defined by G_rev(t) = G(-t).
"""
function reverse(G::CPath)

  p_type = path_type(G)

  if p_type == 0
    G_rev = c_line(end_point(G), start_point(G))
  else #Circle or arc
    G_rev = c_arc(end_point(G), start_point(G), center(G), orientation = -orientation(G))
  end
  
  if isdefined(G, :permutation)
    assign_permutation(G_rev, inv(permutation(G)))
  end

  if isdefined(G, :integral_matrix)
    G_rev.integral_matrix =  permutation(G) * -G.integral_matrix
  end

  return G_rev
end

################################################################################
#
#  Getters and setters
#
################################################################################


function path_type(G::CPath)
  return G.path_type
end

function start_point(G::CPath)
  return G.start_point
end

function end_point(G::CPath)
  return G.end_point
end

function start_arc(G::CPath)
  return G.start_arc
end

function end_arc(G::CPath)
  return G.end_arc
end


function center(G::CPath)
  if 1 <= path_type(G) <= 2
    return G.center
  else
    error("Path is not a circle or an arc")
  end
end

function radius(G::CPath)
  if 1 <= path_type(G) <= 2
    return G.radius
  else
    error("Path is not a circle or an arc")
  end
end

function length(G::CPath)
  return G.length
end

function orientation(G::CPath)
  return G.orientation
end

function assign_permutation(G::CPath, permutation::Perm{Int})
  G.permutation = permutation
end

function permutation(G::CPath)
  return G.permutation
end

function set_t_of_closest_d_point(G::CPath, t::AcbFieldElem)
  G.t_of_closest_d_point = t
end

function get_t_of_closest_d_point(G::CPath)
  return G.t_of_closest_d_point
end

function set_int_param_r(G::CPath, r::ArbFieldElem)
  G.int_param_r = r
end

function get_int_param_r(G::CPath)
  return G.int_param_r
end

function set_int_params_N(G::CPath, N::Int)
  G.int_params_N = N
end

function get_int_params_N(G::CPath)
  return G.int_params_N
end

function set_subpaths(G::CPath, paths::Vector{CPath})
  G.sub_paths = paths
end

function get_subpaths(G::CPath)
  return G.sub_paths
end


################################################################################
#
#  Path evaluation
#
################################################################################

@doc raw"""
evaluate(G::CPath, t::FieldElem) -> FieldElem

Given a path G:[-1,1] -> C and a t in C, returns the value G(t).
"""
function evaluate(G::CPath, t::FieldElem)
  A = start_point(G)
  B = end_point(G)
  path_type = G.path_type
  #If the path is a line
  if path_type == 0
    return (A + B)//2 + (B - A)//2 * t
  end

  if path_type == 3
    return A
  end

  if path_type == 4
    c1 = 1/(1-t)
    c2 = 2 * A * c1
    return c2
  end

  phi_a = G.start_arc
  phi_b = G.end_arc
  orientation = G.orientation
  radius = G.radius
  c = G.center

  CC = parent(A)
  i = onei(CC)
  

  if path_type == 1
    return c + radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * orientation * t))
  end
    #If the path is a circle
  if path_type == 2
    piC = real(const_pi(CC))
    return c - radius * exp(i * (phi_a + orientation * piC * t ))
  end
end

@doc raw"""
evaluate_d(G::CPath, t::FieldElem) -> FieldElem

Given a path G:[-1,1] -> C and a t in C, returns the value dG/dt(t).
"""
function evaluate_d(G::CPath, t::FieldElem)
  A = start_point(G)
  B = end_point(G)
  path_type = G.path_type

  if path_type == 0
    return (B - A)//2
  end

  if path_type == 3
    return 0
  end

  if path_type == 4
    c1 = 1/(1-t)
    c2 = 2 * A * c1
    return c2*c1
  end

  phi_a = G.start_arc
  phi_b = G.end_arc
  orientation = G.orientation
  radius = G.radius
  c = G.center

  CC = parent(A)
  i = onei(CC)
  
  if path_type == 1
    return i * (phi_b - phi_a)//2 * orientation * radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * orientation * t))
  end

#If the path is a circle
  if path_type == 2
    piC = real(const_pi(CC))
    return orientation * i * (piC ) * (-1) * radius * exp(i * (phi_a + orientation * piC * t ))
  end
end

################################################################################
#
#  Equality
#
################################################################################

function ==(G1::CPath, G2::CPath)
  type = path_type(G1)
  if type != path_type(G2)
    return false
  end
  if type == 0
    return (start_point(G1) == start_point(G2)) && (end_point(G1) == end_point(G2))
  elseif type == 1
    return (start_point(G1) == start_point(G2)) && (end_point(G1) == end_point(G2)) && (center(G1) == center(G2)) && (orientation(G1) == orientation(G2)) ||
           ((start_point(G1) == end_point(G2)) && (end_point(G1) == start_point(G2)) && (center(G1) == center(G2)) && (orientation(G1) == -orientation(G2)))
  elseif type == 2
    return (center(G1) == center(G2)) && (radius(G1) == radius(G2)) && (orientation(G1) == orientation(G2))
  else
    return (start_point(G1) == start_point(G2))
  end
end

################################################################################
#
#  Complex plane geometry
#
################################################################################

#Project the center of the circle onto the line that is an extension of ''line''.
#Returns the projection.
function orthogonal_projection(line::CPath, c::AcbFieldElem)
  @req path_type(line) == 0 "First argument needs to be a line."
  a = start_point(line)
  b = end_point(line)
  return a + (( real(c - a) * real(b - a) + imag(c - a) * imag(b - a))/((b - a) * conjugate(b - a))) * (b - a)
end

#Checks if line intersects the circle.
#Returns either true or false. In case it returns true,
#this also returns the orthogonal projection of the center onto the line.
function line_intersect_circle(line::CPath, circle::CPath)
  c = center(circle)
  orth_proj = orthogonal_projection(line, c)
  CC = parent(orth_proj)
  prec = precision(CC)
  RR = ArbField(prec)
  max_dist = length(line)
  proj_dist = abs(start_point(line) - orth_proj)
  if proj_dist <= max_dist
    ratio = proj_dist/max_dist
    value = evaluate(line, 2*ratio-1)
    if contains(abs(value - orth_proj), RR(0))
      distance_to_center = abs(c - orth_proj)
      if distance_to_center <= radius(circle)
        return true, orth_proj
      end
    end
  end
  return false, CC(0)
end

#Checks if line intersects the circle.
#Returns either true or false. In case it returns true,
#this also returns the intersection points of the line with the circle
function intersection_points(line::CPath,circle::CPath)
  @req path_type(line) == 0 && path_type(circle)==2 "First argument needs to be a line and second argument needs to be a circle."
  
  #Find orthogonal projection of the center on the line
  intersect_test, orth_proj = line_intersect_circle(line, circle)
  a = start_point(line)
  b = end_point(line)
  c = center(circle)
  r = radius(circle)

  RR = parent(r)

  if intersect_test
    intersection_points = []
    center_dist = abs(c - orth_proj)
    orth_proj_dist = abs(a - orth_proj)
    D = sqrt(r^2 - center_dist^2)


    #Use Pythagoras to find the intersection points
    first_point_dist = orth_proj_dist - D
    max_dist = length(line)
    if contains(abs(first_point_dist), RR(0))
      push!(intersection_points, a)
    else
      R1 = first_point_dist/max_dist
      push!(intersection_points, evaluate(line, (2*R1-1)))
    end

    second_point_dist = orth_proj_dist + D
    R2 = second_point_dist/max_dist
    push!(intersection_points, evaluate(line, (2*R2-1)))

    if abs(intersection_points[1] - a) <= abs(intersection_points[2]-a)
      return true, intersection_points
    else
      return true, reverse(intersection_points)
    end
  else
    return false, AcbFieldElem[]
  end
end

#The class CChain represents a concatenation of CPaths.

mutable struct CChain
  paths::Vector{CPath}
  permutation::Perm{Int}
  sheets::Vector{AcbFieldElem}
  is_closed::Bool
  start_point::AcbFieldElem
  end_point::AcbFieldElem
  integral_matrix::AcbMatrix
  center::AcbFieldElem
  points

  #Constructor of CChain.
  function CChain(paths::Vector{CPath})

    is_connected, is_closed = test_chain(paths)

    @req is_connected "A chain should consist of a connected sequence of paths."

    C = new()
    C.paths = paths
    C.is_closed = is_closed
    C.start_point = start_point(paths[1])
    C.end_point = end_point(paths[end])

    if all([isdefined(path, :permutation) for path in paths])
      C.permutation = prod(map(permutation, paths))
      s_m = parent(C.permutation)
      m = s_m.n
      if all([isdefined(path, :integral_matrix) for path in paths])
        CC = base_ring(paths[1].integral_matrix)
        g = ncols(paths[1].integral_matrix)
        chain_integral = zero_matrix(CC, m, g)
        sigma = one(s_m)
        for path in paths
          # Sheets are permuted after moving along path, so we need to add a
          # permuted matrix.
          chain_integral += inv(sigma) * change_base_ring(CC,path.integral_matrix)
          sigma *= permutation(path)
        end
        C.integral_matrix = chain_integral
      end
    end
    return C
  end

  function CChain(paths::Vector{CPath}, c::AcbFieldElem)
    C = CChain(paths)
    C.center = c
    return C
  end

end

function length(chain::CChain)
  return length(chain.paths)
end

function permutation(chain::CChain)
  return chain.permutation
end

function integrals(chain::CChain)
  return chain.integrals
end

function start_point(chain::CChain)
  return chain.start_point
end

function end_point(chain::CChain)
  return chain.end_point
end

function center(chain::CChain)
  return chain.center
end

points(chain::CChain) = chain.points::Vector{RiemannSurfacePoint}

function test_chain(paths::Vector{CPath})
  n = length(paths)
  CC = paths[1].C
  for i in (1:n-1)
    if !contains(end_point(paths[i]) - start_point(paths[i+1]), zero(CC))
      return false, false
     end
  end
  if !contains(start_point(paths[1]) - end_point(paths[end]), zero(CC))
    return true, false
  else
    return true, true
  end
end

function is_closed(chain::CChain)
  return chain.is_closed
end

function show(io::IO, chain::CChain)
  n = length(chain)
  CC = AcbField(30)
  if length(chain) == 0
    print(io, "Empty chain.")
  elseif is_closed(chain)
    x0 = start_point(chain)
    if isdefined(chain, :center)
      c = center(chain)
      print(io, "Closed chain consisting of $(n) paths starting at $(CC(x0)) around $(CC(c)).\n")
    else
      print(io, "Closed chain consisting of $(n) paths starting at $(CC(x0)).\n")
    end
  else
    x0 = start_point(chain)
    x1 = end_point(chain)
    print(io, "Chain consisting of $(n) paths starting at $(CC(x0)) and ending at $(CC(x1)).\n")
  end
  if isdefined(chain, :permutation)
    perm = permutation(chain)
    print(io, "With Permutation $(perm).")
  end
  if isdefined(chain, :integrals)
    ints = integrals(chain)
    print(io, "With Integrals $(ints).")
  end
end

function make_inf_chain(chains::Vector{CChain})
  paths = CPath[]
  CC = parent(start_point(chains[1].paths[1]))
  for chain in reverse(chains)
    new_paths = reverse([reverse(p) for p in chain.paths ])
    paths = vcat(paths, new_paths)
  end

  inf_chain = CChain(paths)
  inf_chain.center = CC(1/0)
  return inf_chain

end

function *(chain1::CChain, chain2::CChain) 
  return concatenated_chain = CChain(vcat(chain1.paths, chain2.paths))
end

function ^(chain::CChain, k::Int)
  @req (abs(k) == 1 || chain.is_closed) "Only closed chains can be taken to integers powers of absolute value > 1."
  if k == 0
    result = CChain([c_point(start_point(C))])
  end
  result = chain
  for j in (1:k-1)
    result *= chain
  end
  return result
end

function inv(chain::CChain)
  inv_chain = CChain(reverse([reverse(p) for p in chain.paths ]))
  return inv_chain
end
