export closure, small_generating_set

function small_generating_set(G, op = nothing, id = nothing)
  orderG = length(G)

  if length(G) == 1
    return G
  end

  function non_trivial_randelem()
    x = rand(G)
    while (x == id)
      x = rand(G)
    end
    return x
  end

  firsttry = 10
  secondtry = 20
  # First try one element
  for i in 1:firsttry
    gen = non_trivial_randelem()
    if length(closure([gen], op, id)) == orderG
      return [gen]
    end
  end

  for i in 1:secondtry
    gens = [non_trivial_randelem(), non_trivial_randelem()]
    if length(closure(gens, op, id)) == orderG
      return unique(gens)
    end
  end

  # Now use that unconditionally log_2(|G|) elements generate G

  b = ceil(Int, log(2, orderG))
  @assert orderG <= 2^b

  j = 0
  while true
    if j > 2^20
      error("Something wrong with generator search")
    end
    j = j + 1
    gens = [non_trivial_randelem() for i in 1:b]
    if length(closure(gens, op, id)) == orderG
      return unique(gens)
    end
  end
end

function closure(S, op = nothing, id = nothing)
  if length(S) == 0
    return [id]
  elseif length(S) == 1
    return _closing_under_one_generator(S[1], op, id)
  else
    return _closing_under_generators_dimino(S, op, id)
  end
end

function _closing_under_generators_naive(S, op = nothing, id = nothing)
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

function _closing_under_one_generator(x, op = nothing, id = nothing)
  elements = [x]
  y = x
  while !(y == id)
    y = op(y, x)
    push!(elements, y)
  end
  return elements
end

function _closing_under_generators_dimino(S, op = nothing, id = nothing)
  t = length(S)
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
