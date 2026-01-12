################################################################################
#
#          RieSrf/Auxiliary.jl : Auxiliary Methods for Riemann Surfaces
#
# (C) 2025 Jeroen Hanselman
# This is a port of the Riemann surfaces package written by
# Christian Neurohr. It is based on his Phd thesis
# https://www.researchgate.net/publication/329100697_Efficient_integration_on_Riemann_surfaces_applications
# Neurohr's package can be found on https://github.com/christianneurohr/RiemannSurfaces
#
################################################################################

export TretkoffEdge

export  is_terminated, branch, set_position, terminate, edge_level, isequal,
 get_position, set_label, get_label, PQ, get_subpaths, sheet_ordering, reverse, start_point,
end_point

###############################################################################
#
#  Edges for Tretkoff Algorithm
#
###############################################################################

#The edges of the tree graph in the Tretkoff algorithm.
# - Each edge has a start point and an end point.
# - Each edge has a level. The first vertex has level 1. The odd levels
#   correspond to ramification points and the even levels correspond to sheets.
# - An edge is labeled terminated if the algorithm is done with this edge
# - A branch of the graph is a sequence of edges that ends traces back to the
#   starting vertex.
# - In the algorithm the Tretkoff edges get sorted by the function
#   compare_branches. The position variable gives the position of the
#  terminated edges in this ordering
# - For "even" edges the label gives the position in the list of ordered even
#   edges. The "odd" edges have the same label as their even counterpart
# (with start point and end point reversed).

mutable struct TretkoffEdge
  start_point::Int
  end_point::Int
  level::Int
  terminated::Bool
  branch::Vector{Int}
  position::Int
  label::Int

  function TretkoffEdge(a::Int, b::Int, L::Int = 0,  B::Vector{Int} = [a, b], term::Bool = false)
    TE = new()
    TE.start_point = a
    TE.end_point = b
    TE.level = L
    TE.terminated = term
    TE.branch = B

    return TE
  end
end

function start_point(e::TretkoffEdge)
  return e.start_point
end

function end_point(e::TretkoffEdge)
  return e.end_point
end

function isequal(e1::TretkoffEdge, e2::TretkoffEdge)
  return start_point(e1) == start_point(e2) && end_point(e1) == end_point(e2)
end

function edge_level(e::TretkoffEdge)
  return e.level
end

function terminate(e::TretkoffEdge)
  e.terminated = true
end

function is_terminated(e::TretkoffEdge)
  return e.terminated
end

function branch(e::TretkoffEdge)
  return e.branch
end

function set_position(e::TretkoffEdge, s::Int)
  e.position = s
end

function get_position(e::TretkoffEdge)
  return e.position
end

function PQ(e::TretkoffEdge)
  return start_point(e) < end_point(e)
end

function reverse(e::TretkoffEdge)
  return TretkoffEdge(end_point(e), start_point(e))
end

function set_label(e::TretkoffEdge,l::Int)
  e.label = l
end

function get_label(e::TretkoffEdge)
  return e.label
end

################################################################################
#
#  Auxiliary functions for computation over the complex numbers
#
################################################################################


#Ensures that the output is between 0 and 2pi.
function Base.mod2pi(x::ArbFieldElem)
  pi2 = 2*const_pi(parent(x))
  while x < 0
    x += pi2
  end

  while x > pi2
    x -= pi2
  end

  return x
end

@doc raw"""
    embed_poly(f::PolyRingElem{AbsSimpleNumFieldElem}, v::Plc, prec::Int) -> PolyRingElem{AcbField}

Embed a polynomial into the polynomial ring over the complex numbers using the given place.
"""
function embed_poly(f::PolyRingElem{AbsSimpleNumFieldElem}, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  coeffs = coefficients(f)
  coeffs = map(t -> evaluate(t, v.embedding, prec), coeffs)

  Cx, x = polynomial_ring(AcbField(prec), "x")

  return sum(coeffs[i]*x^(i - 1) for i in (1:length(coeffs)))
end

@doc raw"""
    embed_mpoly(f::MPolyRingElem{AbsSimpleNumFieldElem}, v::Plc, prec::Int) -> PolyRingElem{AcbField}

Embed a polynomial into the polynomial ring over the complex numbers using the given place.
"""
function embed_mpoly(f::MPolyRingElem, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  return map_coefficients(x -> evaluate(x, v.embedding, prec), f)
end

#TODO: Might need to be made more rigorous due to dealing with arb balls
@doc raw"""
    sheet_ordering(z1::AcbFieldElem,z2::AcbFieldElem) -> Bool

An ordering on the complex numbers. The number z2 = x2 + y2 is greater
than z1 = x1 + y1 if x2 > x1. In case of equality z2 is greater than z1 if y2 > y1.
"""
function sheet_ordering(z1::AcbFieldElem,z2::AcbFieldElem)
  if real(z1) < real(z2)
    return true
  elseif real(z1) > real(z2)
    return false
  elseif imag(z1) < imag(z2)
    return true
  elseif imag(z2) < imag(z1)
    return false
  end
end

#This is mainly useful when plugging an acb ball centered around zero into a
#function like arg where its output would suddenly have a radius of length pi.
@doc raw"""
    trim_zero(x::AcbFieldElem, n::Int) -> Bool

Sets the real or imaginary parts of a complex number to zero if it is smaller than 10^(-N).
"""
function trim_zero(x::AcbFieldElem, n::Int)
  Cc = parent(x)
  prec = precision(Cc)
  Rc = ArbField(prec)
  i = onei(Cc)
  if abs(real(x)) < Rc(10)^(-n)
    x = Cc(imag(x))*i
  end

  if abs(imag(x)) < Rc(10)^(-n)
    x = Cc(real(x))
  end

  return x
end


################################################################################
#
#  Convex hull
#
################################################################################

@doc raw"""
    inner_faces(f::MPolyRingElem) -> Array

Compute the inner faces of the Newton polygon corresponding to the multivariate
polynomial f(x,y). The Newton polygon is the convex hull of the points (i,j)
for which x^i * y^j is a monomial of f.
"""
function inner_faces(f)
  points = [degrees(mon) for mon in monomials(f)]
  ordered_vertices = convex_hull(points)
  n = length(ordered_vertices)
  edges = vcat([line_equation(ordered_vertices[i-1], ordered_vertices[i]) for i in (2:n)], line_equation(ordered_vertices[end], ordered_vertices[1]))
  center = sum(ordered_vertices)//n

  result = []
  d = total_degree(f)-3
	for i in (0:d)
		for j in (0:d-i)
      if  all([(sign(g(i + 1, j + 1)) == sign(g(center[1], center[2]))) for g in edges])
			  push!(result, [i + 1, j + 1])
			end
		end
	end

  return result
end

@doc raw"""
    convex_hull(points::Vector{Vector{Int}}) -> Vector{Vector{Int}}

Computes the convex hull of the points [i,j] in the plane.
The convex hull is returned as a list of points that form the
vertices of the polygon. The edges of the polygon correspond to the
lines connecting the succesive vertices.
"""
function convex_hull(points::Vector{Vector{Int}})
  orig_points = copy(points)

  points = sort(points)

  # Take care of trivial case with 1 or 2 elements
  if length(points) == 1
    error("Convex hull of 1 point is not defined")
  elseif length(points) == 2
    P = Polygon([Line((points[1], points[2]))])
  else
    points_lower_convex_hull = Vector{Int}[points[1]]
    i = 2
    while i<= length(points)
      y = points_lower_convex_hull[end]
      sl = [_slope(y, x) for x = points[i:end]]
      min_sl = minimum(sl)
      p = findlast(x->x == min_sl, sl)::Int
      push!(points_lower_convex_hull, points[p+i-1])
      i += p
    end

    points = reverse(points)
    points_upper_convex_hull = Vector{Int}[points[1]]
    i = 2
    while i<= length(points)
      y = points_upper_convex_hull[end]
      sl = [_slope(y, x) for x = points[i:end]]
      min_sl = minimum(sl)
      p = findlast(x->x == min_sl, sl)::Int
      push!(points_upper_convex_hull, points[p+i-1])
      i += p
    end
    return vcat(points_lower_convex_hull[1:end-1], points_upper_convex_hull[1:end-1])
  end
end

function _slope(a::Vector{Int}, b::Vector{Int})
  if b[1] == a[1]
    return inf
  end
  return QQFieldElem(b[2]-a[2], b[1]-a[1])
end

@doc raw"""
    line_equation(a::Vector{Int}, b::Vector{Int}) -> MPolyRingElem

Returns the equation of the line in the plane connecting the points a and b.
"""
function line_equation(a::Vector{Int}, b::Vector{Int})
  Qxy, (x,y) = polynomial_ring(QQ, ["x","y"])
  if b[1] == a[1]
    return x - a[1]
  end
  c = _slope(a,b)
  return  c*x - y - c*b[1] + b[2]
end
