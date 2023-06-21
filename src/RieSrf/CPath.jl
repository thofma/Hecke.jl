################################################################################
#
#          RieSrf/CPath.jl : Paths in C
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export CPath

export c_line, c_arc, start_point, end_point, path_type, reverse, assign_permutation, permutation

################################################################################
#
#  Constructors
#
################################################################################

mutable struct CPath

  path_type::Int
  start_point::acb
  end_point::acb
  C::AcbField
  
  center::acb
  radius::arb
  
  length::arb
  gamma::Any
  orientation::Int
  permutation::Perm{Int}
  
  int_params::arb
  t_of_closed_D_point::acb
  bounds::Array{Int}
  
  #Path type index:
  #0 is a line
  #1 is an arc
  #2 is a circle
  
  function CPath(a::acb, b::acb, path_type::Int, c::acb = zero(parent(a)), radius::arb = real(zero(parent(a))), orientation::Int = 1)
  
    P = new()
    P.C = parent(a)
    P.start_point = a
    P.end_point = b
    P.path_type = path_type
    P.center = c
    P.radius = radius
    P.orientation = orientation
    P.bounds = []
    
    #Line
    if path_type == 0
      gamma = function(t::arb)
        return (a + b)//2 + (b - a)//2 * t
      end
      length = abs(b - a)
    end
    
    Cc = P.C
    
    i = onei(Cc)
    piC = real(const_pi(Cc))
    
    #Round real or imag part to zero to compute angle if necessary
    prec = precision(Cc)
    zero_sens = floor(prec*log(2)/log(10)) - 5
    
    a_diff = a - c
    
    if abs(real(a_diff)) < 10^(-zero_sens)
      a_diff = Cc(imag(a_diff))*i
    end
    
    if abs(imag(a_diff)) < 10^(-zero_sens)
      a_diff = Cc(real(a_diff))
    end
    
    b_diff = b - c
    
    if abs(real(b_diff)) < 10^(-zero_sens)
      b_diff = Cc(imag(b_diff))*i
    end
    
    if abs(imag(b_diff)) < 10^(-zero_sens)
      b_diff = Cc(real(b_diff))
    end
    
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
   
    #Arc
    if path_type == 1
      gamma = function(t::arb)
        return c + radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * orientation * t))
      end
      
      length = abs((phi_b - phi_a)) * radius
      
    end
    
    #Full circle
    if path_type == 2
      gamma = function(t::arb)
        #Minus radius as gamma(-1) = a
        return c - radius * exp(i * (phi_a + piC * t ))
      end
      length = 2 * piC * radius
    end
    
    P.gamma = gamma
    P.length = length
    return P
  end

end


function c_line(start_point::acb, end_point::acb)
  return CPath(start_point, end_point, 0)
end

function c_arc(start_point::acb, end_point::acb, center::acb; orientation::Int = 1)
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


function reverse(G::CPath)
  
  p_type = path_type(G)
  
  if p_type == 0
    G_rev = c_line(end_point(G), start_point(G))
  else #Circle or arc
    G_rev = c_arc(end_point(G), start_point(G), center(G), orientation = -orientation(G))
  end
  assign_permutation(G_rev, inv(permutation(G)))
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

function set_t_of_closest_d_point(G::CPath, t::acb)
  G.t_of_closest_d_point = t
end

function get_t_of_closest_d_point(G::CPath, t::acb)
  G.t_of_closest_d_point = t
end

################################################################################
#
#  Path evaluation
#
################################################################################

function evaluate(G::CPath, t::arb)
  return G.gamma(t)
end

