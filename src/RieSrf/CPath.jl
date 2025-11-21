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
# a line, an arc or a circle.

mutable struct CPath

  path_type::Int
  #Path type index:
  #0 is a line
  #1 is an arc
  #2 is a circle
  
  #The field in which the path lies
  C::AcbField

  #The start point and the end point of the path
  start_point::AcbFieldElem
  end_point::AcbFieldElem

  #If the path is an arc or a circle, it will be described by the center,
  #the radius, and the start and end angles. (c + r*e^(ix))
  center::AcbFieldElem
  radius::ArbFieldElem
  start_arc::ArbFieldElem
  end_arc::ArbFieldElem

  #The orientation determines how we move from start point to end point
  #If the orientation is 1 we move counterclockwise and if the orientatoin
  # is -1 we move clockwise.
  orientation::Int
  
  #The length of the path
  length::ArbFieldElem

  #A map gamma:[-1, 1] -> CC parametrizing the path
  gamma::Any
  #The derivative of gamma
  dgamma::Any


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
  function CPath(a::AcbFieldElem, b::AcbFieldElem, path_type::Int, c::AcbFieldElem = zero(parent(a)), radius::ArbFieldElem = real(zero(parent(a))), orientation::Int = 1)
  
    P = new()
    P.C = parent(a)
    P.start_point = a
    P.end_point = b
    P.path_type = path_type
    P.center = c
    P.radius = radius
    P.orientation = orientation
    P.bounds = []
    
    #If the path is a line 
    if path_type == 0
      gamma = function(t::FieldElem)
        return (a + b)//2 + (b - a)//2 * t
      end
      dgamma = function(t::FieldElem)
        return (b - a)//2
      end
      length = abs(b - a)
    end
    
    #If the path is not a line we need some additional constants to compute
    #length, parametrization, etc.
    Cc = P.C
    i = onei(Cc)
    piC = real(const_pi(Cc))
    
    #Round real or imaginary part to zero to compute angle if necessary
    prec = precision(Cc)
    zero_sens = floor(Int, prec*log(2)/log(10)) - 5
    
    a_diff = trim_zero(a - c, zero_sens)
    b_diff = trim_zero(b - c, zero_sens)
    
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
      gamma = function(t::FieldElem)
        return c + radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * orientation * t))
      end
      dgamma = function(t::FieldElem)
        return i * (phi_b - phi_a)//2 * orientation * radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * orientation * t))
      end

      length = abs((phi_b - phi_a)) * radius
      
    end
    
    #If the path is a circle
    if path_type == 2
      gamma = function(t::FieldElem)
        #Minus radius as gamma(-1) = a
        return c - radius * exp(i * (phi_a + orientation * piC * t ))
      end
      dgamma = function(t::FieldElem)
        return orientation * i * (piC ) * (-1) * radius * exp(i * (phi_a + orientation * piC * t )) 
      end

      length = 2 * piC * radius
    end
    
    P.gamma = gamma
    P.dgamma = dgamma
    P.length = length
    return P
  end

end

@doc raw"""
c_line(start_point::AcbFieldElem, end_point::AcbFieldElem) -> CPath

Constructs a line in C from start_point to end_point.
"""
function c_line(start_point::AcbFieldElem, end_point::AcbFieldElem)
  return CPath(start_point, end_point, 0)
end

@doc raw"""
c_arc(start_point::AcbFieldElem, end_point::AcbFieldElem, center::AcbFieldElem; orientation::Int = 1) 
  -> CPath

Constructs an arc around ''center'' in C from ''start_point'' to 
''end_point''. If orientation is 1 the path goes counterclockwise.
If it is -1 it goes clockwise. If start_point and end_point are identical
a circle is created instead. 
"""
function c_arc(start_point::AcbFieldElem, end_point::AcbFieldElem, center::AcbFieldElem; 
  orientation::Int = 1)
  #TODO: We might need a check that start point and end_point are equally
  #far away from center.
  if contains(end_point, start_point) && contains(start_point, end_point)
    return CPath(start_point, start_point, 2, center, abs(start_point - center), orientation)
  else
    return CPath(start_point, end_point, 1, center, abs(start_point - center), orientation)
  end
end

################################################################################
#
#  IO
#
################################################################################


function show(io::IO, gamma::CPath)
  p_type = path_type(gamma)
  if p_type< 0 || p_type > 2
    error("Path type does not exist")
  end
  
  x0 = start_point(gamma)
  x1 = end_point(gamma)
  if p_type == 0
    print(io, "Line from $(x0) to $(x1).")
  else
    r = radius(gamma)
    c = center(gamma)
    if p_type == 1
      print(io, "Arc around $(c) with radius $(r) starting at $(x0) and ending at $(x1).")
    elseif p_type == 2
      print(io, "Circle around $(c) with radius $(r) starting at $(x0).")
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
  assign_permutation(G_rev, inv(permutation(G)))

  if isdefined(G, :integral_matrix)
    G_rev.integral_matrix =  permutation(G_rev) * -G.integral_matrix
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
  return G.gamma(t)
end

@doc raw"""
evaluate_d(G::CPath, t::FieldElem) -> FieldElem

Given a path G:[-1,1] -> C and a t in C, returns the value dG/dt(t).
"""
function evaluate_d(G::CPath, t::FieldElem)
  return G.dgamma(t)
end

