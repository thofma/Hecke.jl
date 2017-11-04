export closure, small_generating_set

function find_identity(S, op = nothing)
  @assert length(S) > 0
  g = S[1]
  h = g
  while true
    hh = op(h, g)
    if hh == g
      return h
    end
    h = hh
  end
end

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

function multiplication_table(G, op = nothing)
  l = length(G)
  z = Matrix{Int}(l, l)
  for i in 1:l
    for j in 1:l
      p = op(G[i], G[j])
      for k in 1:l
        if p == G[k]
          z[i, j] = k
          break
        end
      end
    end
  end
  return z
end

function mul(i, j, m)
  return m[i, j]
end

function defines_abelian_group(m)
  return issymmetric(m)
end

function defines_group_isomorphic_to_16T7(m)
  ordershape = [ (1, 1), (2, 3), (4, 12) ]
  # Use algorithm of Tarjahn (or something like that)
  # 16T7 has the following presentation:
  #
  #  $.1^4 = Id($)
  #  $.2^4 = Id($)
  #  $.3^2 = Id($)
  #  $.2^-1 * $.1^2 * $.2^-1 = Id($)
  #  $.1^-1 * $.2^-1 * $.1 * $.2^-1 = Id($)
  #  $.1^-1 * $.3 * $.1 * $.3 = Id($)
  #  $.2^-1 * $.3 * $.2 * $.3 = Id($)

  relations = [[(2, -1), (1, 2), (2, -1)],
               [(1, -1), (2, -1), (1, 1), (2, -1)], 
               [(1, -1), (3, 1), (1, 1), (3, 1)],
               [(2, -1), (3, 1), (2, 1), (3, 1)]]

  l = size(m, 1)

  if l != 16
    return false
  end

  if defines_abelian_group(m)
    return false
  end

  elements_by_orders = Dict{Int, Array{Int, 1}}()

  for i in 1:l
    o = order(i, m)
    if haskey(elements_by_orders, o)
      push!(elements_by_orders[o], i)
    else
      elements_by_orders[o] = [i]
    end
  end

  for (o, no) in ordershape
    if !haskey(elements_by_orders, o)
      return false
    else
      elts = elements_by_orders[o]
      if length(elts) != no
        return false
      end
    end
  end

  id = find_identity(m)

  img_of_gens = Iterators.product(elements_by_orders[4],
                                  elements_by_orders[4],
                                  elements_by_orders[2])

  mult = (i, j) -> mul(i, j, m)

  for (g1, g2, g3) in img_of_gens
    g2inv = inv(g2, m)
    g1inv = inv(g1, m)
    #  $.2^-1 * $.1^2 * $.2^-1 = Id($)
    z = g2inv
    z = mult(z, g1)
    z = mult(z, g1)
    z = mult(z, g2inv)
    if z != id
      continue
    end
    #  $.1^-1 * $.2^-1 * $.1 * $.2^-1 = Id($)
    z = g1inv
    z = mult(z, g2inv)
    z = mult(z, g1)
    z = mult(z, g2inv)
    if z != id
      continue
    end
    #  $.1^-1 * $.3 * $.1 * $.3 = Id($)
    z = g1inv
    z = mult(z, g3)
    z = mult(z, g1)
    z = mult(z, g3)
    if z != id
      continue
    end
    #  $.2^-1 * $.3 * $.2 * $.3 = Id($)
    z = g2inv
    z = mult(z, g3)
    z = mult(z, g2)
    z = mult(z, g3)
    if z != id
      continue
    end

    cl = closure([g1, g2, g3], mult, id)

    if length(cl) < 16
      continue
    end
    return true
  end
  return false
end

function order(i::Int, m::Array{Int, 2})
  k = 2
  j = mul(i, i, m) 
  while j != i
    j = mul(i, j, m)
    k = k + 1
  end
  return k - 1
end

function find_identity(m::Array{Int, 2})
  return find_identity([1], (i, j) -> mul(i, j, m))
end

function inv(i::Int, m::Array{Int, 2})
  l = size(m, 1)
  id = find_identity(m)
  for j in 1:l
    if mul(i, j, m) == id
      return j
    end
  end
  error("Not possible")
end

# some transitive groups of degree 16

const _16T1 = reshape([ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       2, 4, 1, 6, 3, 8, 5, 10, 7, 12, 9, 14, 11, 16, 13, 15,
                       3, 1, 5, 2, 7, 4, 9, 6, 11, 8, 13, 10, 15, 12, 16, 14,
                       4, 6, 2, 8, 1, 10, 3, 12, 5, 14, 7, 16, 9, 15, 11, 13,
                       5, 3, 7, 1, 9, 2, 11, 4, 13, 6, 15, 8, 16, 10, 14, 12,
                       6, 8, 4, 10, 2, 12, 1, 14, 3, 16, 5, 15, 7, 13, 9, 11,
                       7, 5, 9, 3, 11, 1, 13, 2, 15, 4, 16, 6, 14, 8, 12, 10,
                       8, 10, 6, 12, 4, 14, 2, 16, 1, 15, 3, 13, 5, 11, 7, 9,
                       9, 7, 11, 5, 13, 3, 15, 1, 16, 2, 14, 4, 12, 6, 10, 8,
                       10, 12, 8, 14, 6, 16, 4, 15, 2, 13, 1, 11, 3, 9, 5, 7,
                       11, 9, 13, 7, 15, 5, 16, 3, 14, 1, 12, 2, 10, 4, 8, 6,
                       12, 14, 10, 16, 8, 15, 6, 13, 4, 11, 2, 9, 1, 7, 3, 5,
                       13, 11, 15, 9, 16, 7, 14, 5, 12, 3, 10, 1, 8, 2, 6, 4,
                       14, 16, 12, 15, 10, 13, 8, 11, 6, 9, 4, 7, 2, 5, 1, 3,
                       15, 13, 16, 11, 14, 9, 12, 7, 10, 5, 8, 3, 6, 1, 4, 2,
                       16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1 ],
                      (16, 16))

const _16T2 = reshape([ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       2, 1, 6, 7, 8, 3, 4, 5, 12, 13, 14, 9, 10, 11, 16, 15,
                       3, 6, 1, 9, 10, 2, 12, 13, 4, 5, 15, 7, 8, 16, 11, 14,
                       4, 7, 9, 11, 1, 12, 14, 2, 15, 3, 5, 16, 6, 8, 10, 13,
                       5, 8, 10, 1, 11, 13, 2, 14, 3, 15, 4, 6, 16, 7, 9, 12,
                       6, 3, 2, 12, 13, 1, 9, 10, 7, 8, 16, 4, 5, 15, 14, 11,
                       7, 4, 12, 14, 2, 9, 11, 1, 16, 6, 8, 15, 3, 5, 13, 10,
                       8, 5, 13, 2, 14, 10, 1, 11, 6, 16, 7, 3, 15, 4, 12, 9,
                       9, 12, 4, 15, 3, 7, 16, 6, 11, 1, 10, 14, 2, 13, 5, 8,
                       10, 13, 5, 3, 15, 8, 6, 16, 1, 11, 9, 2, 14, 12, 4, 7,
                       11, 14, 15, 5, 4, 16, 8, 7, 10, 9, 1, 13, 12, 2, 3, 6,
                       12, 9, 7, 16, 6, 4, 15, 3, 14, 2, 13, 11, 1, 10, 8, 5,
                       13, 10, 8, 6, 16, 5, 3, 15, 2, 14, 12, 1, 11, 9, 7, 4,
                       14, 11, 16, 8, 7, 15, 5, 4, 13, 12, 2, 10, 9, 1, 6, 3,
                       15, 16, 11, 10, 9, 14, 13, 12, 5, 4, 3, 8, 7, 6, 1, 2,
                       16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1 ],
                       (16, 16))

const _16T3 = reshape([ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       2, 1, 6, 7, 8, 3, 4, 5, 12, 13, 14, 9, 10, 11, 16, 15,
                       3, 6, 1, 9, 10, 2, 12, 13, 4, 5, 15, 7, 8, 16, 11, 14,
                       4, 7, 9, 1, 11, 12, 2, 14, 3, 15, 5, 6, 16, 8, 10, 13,
                       5, 8, 10, 11, 1, 13, 14, 2, 15, 3, 4, 16, 6, 7, 9, 12,
                       6, 3, 2, 12, 13, 1, 9, 10, 7, 8, 16, 4, 5, 15, 14, 11,
                       7, 4, 12, 2, 14, 9, 1, 11, 6, 16, 8, 3, 15, 5, 13, 10,
                       8, 5, 13, 14, 2, 10, 11, 1, 16, 6, 7, 15, 3, 4, 12, 9,
                       9, 12, 4, 3, 15, 7, 6, 16, 1, 11, 10, 2, 14, 13, 5, 8,
                       10, 13, 5, 15, 3, 8, 16, 6, 11, 1, 9, 14, 2, 12, 4, 7,
                       11, 14, 15, 5, 4, 16, 8, 7, 10, 9, 1, 13, 12, 2, 3, 6,
                       12, 9, 7, 6, 16, 4, 3, 15, 2, 14, 13, 1, 11, 10, 8, 5,
                       13, 10, 8, 16, 6, 5, 15, 3, 14, 2, 12, 11, 1, 9, 7, 4,
                       14, 11, 16, 8, 7, 15, 5, 4, 13, 12, 2, 10, 9, 1, 6, 3,
                       15, 16, 11, 10, 9, 14, 13, 12, 5, 4, 3, 8, 7, 6, 1, 2,
                       16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1 ],
                       (16, 16))

const _16T4 = reshape([ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       2, 6, 7, 1, 8, 4, 12, 13, 14, 3, 5, 10, 11, 16, 9, 15,
                       3, 7, 9, 10, 1, 12, 14, 2, 5, 15, 4, 16, 6, 8, 11, 13,
                       4, 1, 10, 6, 11, 2, 3, 5, 15, 12, 13, 7, 8, 9, 16, 14,
                       5, 8, 1, 11, 9, 13, 2, 14, 3, 4, 15, 6, 16, 7, 10, 12,
                       6, 4, 12, 2, 13, 1, 10, 11, 16, 7, 8, 3, 5, 15, 14, 9,
                       7, 12, 14, 3, 2, 10, 16, 6, 8, 9, 1, 15, 4, 13, 5, 11,
                       8, 13, 2, 5, 14, 11, 6, 16, 7, 1, 9, 4, 15, 12, 3, 10,
                       9, 14, 5, 15, 3, 16, 8, 7, 1, 11, 10, 13, 12, 2, 4, 6,
                       10, 3, 15, 12, 4, 7, 9, 1, 11, 16, 6, 14, 2, 5, 13, 8,
                       11, 5, 4, 13, 15, 8, 1, 9, 10, 6, 16, 2, 14, 3, 12, 7,
                       12, 10, 16, 7, 6, 3, 15, 4, 13, 14, 2, 9, 1, 11, 8, 5,
                       13, 11, 6, 8, 16, 5, 4, 15, 12, 2, 14, 1, 9, 10, 7, 3,
                       14, 16, 8, 9, 7, 15, 13, 12, 2, 5, 3, 11, 10, 6, 1, 4,
                       15, 9, 11, 16, 10, 14, 5, 3, 4, 13, 12, 8, 7, 1, 6, 2,
                       16, 15, 13, 14, 12, 9, 11, 10, 6, 8, 7, 5, 3, 4, 2, 1 ],
                       (16, 16))

const _16T5 = reshape([ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       2, 6, 7, 1, 8, 11, 5, 12, 4, 3, 15, 16, 10, 9, 14, 13,
                       3, 7, 9, 10, 1, 5, 4, 2, 13, 14, 8, 6, 15, 16, 12, 11,
                       4, 1, 10, 9, 7, 2, 3, 5, 14, 13, 6, 8, 16, 15, 11, 12,
                       5, 8, 1, 7, 6, 12, 2, 11, 3, 4, 16, 15, 9, 10, 13, 14,
                       6, 11, 5, 2, 12, 15, 8, 16, 1, 7, 14, 13, 3, 4, 9, 10,
                       7, 5, 4, 3, 2, 8, 1, 6, 10, 9, 12, 11, 14, 13, 16, 15,
                       8, 12, 2, 5, 11, 16, 6, 15, 7, 1, 13, 14, 4, 3, 10, 9,
                       9, 4, 13, 14, 3, 1, 10, 7, 15, 16, 2, 5, 12, 11, 6, 8,
                       10, 3, 14, 13, 4, 7, 9, 1, 16, 15, 5, 2, 11, 12, 8, 6,
                       11, 15, 8, 6, 16, 14, 12, 13, 2, 5, 9, 10, 7, 1, 4, 3,
                       12, 16, 6, 8, 15, 13, 11, 14, 5, 2, 10, 9, 1, 7, 3, 4,
                       13, 10, 15, 16, 9, 3, 14, 4, 12, 11, 7, 1, 6, 8, 5, 2,
                       14, 9, 16, 15, 10, 4, 13, 3, 11, 12, 1, 7, 8, 6, 2, 5,
                       15, 14, 12, 11, 13, 9, 16, 10, 6, 8, 4, 3, 5, 2, 1, 7,
                       16, 13, 11, 12, 14, 10, 15, 9, 8, 6, 3, 4, 2, 5, 7, 1 ],
                       (16, 16))

const _16T8 = reshape([ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       2, 6, 9, 1, 10, 4, 11, 12, 5, 3, 8, 7, 15, 16, 14, 13,
                       3, 7, 6, 8, 1, 5, 4, 2, 13, 14, 15, 16, 10, 9, 12, 11,
                       4, 1, 10, 6, 9, 2, 12, 11, 3, 5, 7, 8, 16, 15, 13, 14,
                       5, 8, 1, 7, 6, 3, 2, 4, 14, 13, 16, 15, 9, 10, 11, 12,
                       6, 4, 5, 2, 3, 1, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15,
                       7, 5, 13, 3, 14, 8, 15, 16, 1, 6, 2, 4, 12, 11, 9, 10,
                       8, 3, 14, 5, 13, 7, 16, 15, 6, 1, 4, 2, 11, 12, 10, 9,
                       9, 11, 4, 12, 2, 10, 1, 6, 15, 16, 14, 13, 3, 5, 7, 8,
                       10, 12, 2, 11, 4, 9, 6, 1, 16, 15, 13, 14, 5, 3, 8, 7,
                       11, 10, 15, 9, 16, 12, 14, 13, 2, 4, 6, 1, 7, 8, 5, 3,
                       12, 9, 16, 10, 15, 11, 13, 14, 4, 2, 1, 6, 8, 7, 3, 5,
                       13, 15, 8, 16, 7, 14, 3, 5, 12, 11, 9, 10, 6, 1, 4, 2,
                       14, 16, 7, 15, 8, 13, 5, 3, 11, 12, 10, 9, 1, 6, 2, 4,
                       15, 14, 12, 13, 11, 16, 9, 10, 7, 8, 5, 3, 4, 2, 1, 6,
                       16, 13, 11, 14, 12, 15, 10, 9, 8, 7, 3, 5, 2, 4, 6, 1 ],
                       (16, 16))

mutable struct Perm
end
