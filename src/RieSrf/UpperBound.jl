function arb_maximum(vectofarbs::Vector{RealFieldElem})::Tuple{RealFieldElem,Bool}
  if length(vectofarbs) <= 1
    if length(vectofarbs) == 0
      error("Empty list")
      return (0,false)
    else
      return (vectofarbs[1],true)
    end
  end
  midpoint_vect = []
  for i in 1:length(vectofarbs)
    push!(midpoint_vect,midpoint(vectofarbs[i]))
  end
  maxpoint = 1
  for i in 2:length(vectofarbs)
    if midpoint_vect[i] > midpoint_vect[maxpoint]
      maxpoint = i
    end
  end
  for i in 1:length(vectofarbs)
    if i != maxpoint && overlaps(vectofarbs[i],vectofarbs[maxpoint])
      return (vectofarbs[maxpoint],false)
    end
  end
  return (vectofarbs[maxpoint],true)
end