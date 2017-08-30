function _closing_under_generators_naive(S, op = nothing, id = nothing, eq = ==)
  list = push!(copy(S), id)
  stable = false
  while !stable
    stable = true
    for g in list
      for s in S
        m = op(g, s)
        if !(m in list)
          push!(list, m)
          stable = false
        end
      end
    end
  end
  return list
end

function _closing_under_generators_dimino(S, op = nothing, id = nothing, eq = ==)
  t = 2
  order = 1
  elements = [id]
  g = S[1]

  while g != id
    order = order +1
    push!(elements, g)
    g = op(g, S[1])
  end

  for i in 2:t
    if !(S[i] in elements)
      previous_order = order
      order = order + 1
      push!(elements, S[i])
      for j in 2:previous_order
        order = order + 1
        push!(elements, op(elements[j], S[i]))
      end

      rep_pos = previous_order + 1
      while rep_pos <= order
        for k in 1:i
          s = S[k]
          elt = op(elements[rep_pos], s)
          if !(elt in elements)
            order = order + 1
            push!(elements, elt)
            for j in 2:previous_order
              order = order + 1
              push!(elements, op(elements[j], elt))
            end
          end
        end
        rep_pos = rep_pos + previous_order
      end
    end
  end
  return elements
end

mutable struct Perm
end
