type ModAlgAss{S, T}
  base_ring::S
  action::Vector{T}
  dimension::Int
  isirreducible::Int
  dimension_splitting_field::Int
  
  function ModAlgAss{S, T}(action::Vector{T}) where {S, T}
    z = new{S, T}()
    z.action = action
    z.dimension = cols(action[1])
    z.base_ring = base_ring(action[1])
    if z.dimension == 1
      z.isirreducible = 1
      z.dimension_splitting_field = 1
    else 
      z.isirreducible = 0
      z.dimension_splitting_field = 0
    end
    return z
  end
end

function ModAlgAss(action::Vector{T}) where {T}
  @assert length(action) > 0
  S = typeof(base_ring(action[1]))
  return ModAlgAss{S, T}(action)
end

function isirreducible_known(M::ModAlgAss)
  return M.isirreducible != 0
end

function isirreducible(M::ModAlgAss)
  if M.isirreducible != 0
    return M.isirreducible == 1
  else
    error("Not implemented yet")
  end
end

function dimension(M::ModAlgAss)
  return M.dimension
end

function base_ring(M::ModAlgAss)
  return M.base_ring
end
