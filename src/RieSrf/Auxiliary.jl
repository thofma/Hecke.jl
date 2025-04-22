################################################################################
#
#          RieSrf/Auxiliary.jl : Auxiliary Methods for Riemann Surfaces
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export TretkoffEdge

export  is_terminated, branch, set_position, terminate, edge_level, get_position, set_label, get_label, PQ

################################################################################
#
#  Edges for Tretkoff Algorithm
#
################################################################################

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
#  Auxiliary functions
#
################################################################################

function Base.mod2pi(x::arb)
  pi2 = 2*const_pi(parent(x))
  while x < 0
    x += pi2
  end
  
  while x > pi2
    x -= pi2
  end
  
  return x
end

function embed_poly(f::PolyRingElem{nf_elem}, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  coeffs = coefficients(f)
  coeffs = map(t -> evaluate(t, v.embedding, prec), coeffs)
  
  Cx, x = polynomial_ring(AcbField(prec), "x")
  
  return sum(coeffs[i]*x^(i - 1) for i in (1:length(coeffs)))
end

function embed_mpoly(f::MPolyRingElem, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  return map_coefficients(x -> evaluate(x, v.embedding, prec), f)
end

#Might need to be made more rigorous due to dealing with arb balls
function sheet_ordering(z1::acb,z2::acb)
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
