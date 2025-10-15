#########################################################################
#
# This file provides an iterator 'partition_with_condition(n, k, l)'. This
# iterator enumerates all possible k-tuples [ a_0, ..., a_{k-1} ] of non-
# negative integers satisfying a_0 + a_1 + ... + a_{k-1} = n and, further-
# more, 0*a_0 + 1*a_1 + 2*a_2 + ... + (k-1)*a_{k-1} = l.
#
# Example
# julia> for i in partition_with_condition(5, 3, 7) println(i) end
# [5, 0, 0]
# [0, 3, 2]
# [1, 1, 3]
#
#########################################################################

struct partition_with_condition
  n::Int
  k::Int
  l::Int
  function partition_with_condition(n::Int, k::Int, l::Int)
    # Catch non-meaningful input
    @req n>=0 "n should be >= 0"
    @req k>0 "k should be > 0"
    @req l>=0 "l should be >= 0"
    return new(n, k, l)
  end
end

function Base.iterate(parti::partition_with_condition)
  if parti.k == 1
    # If k is 1, the problem is trivial
    if parti.l == 0
      return Int[parti.n], Int[]
    else
      return nothing
    end
  end
  # The iterators hidden output 'iter' is a tuple of two integer vectors of the same size.
  # The first vector is the last non-hidden output, i.e. the vector [a_0, ..., a_{k-1}].
  # The second vector is of the form [W, S, a_2, a_3, ..., a_{k-1}], where S = a_2 + ... + a_{k-1}
  # and W = 2*a_2 + 3*a_3 + ... + (k-1)*a_{k-1}.
  firstlist = zeros(Int, parti.k-1)
  pushfirst!(firstlist, parti.n)
  iter = (firstlist, pushfirst!(pushfirst!(firstlist[3:end], Int(0)), Int(0)))
  return firstlist, iter
end

function Base.iterate(parti::partition_with_condition, iter::Tuple{Vector{Int}, Vector{Int}})
  if parti.k == Int(1)
    return nothing
  end
  current_position = Int(3)
  weighted_sum = iter[2][1]
  sum = iter[2][2]
  # For every choice of integers a_2, a_3, ... a_{k-1} there exists a unique pair of integers
  # (a_0, a_1) fulfilling the two equations. Hence, we can iterate over all such choices and
  # calculate the corresponding pair (a_0, a_1) and check, whether a_0 and a_1 are both >= 0.
  while current_position < parti.k+1
    sum += 1
    weighted_sum += current_position - 1
    @inbounds iter[2][current_position] += 1
    a1 = parti.l - weighted_sum
    if a1 >= 0
      a0 = parti.n - sum - a1
      if a0 >= 0
        iter[1][3:end] = view(iter[2], 3:parti.k)
        @inbounds iter[1][2] = a1
        @inbounds iter[1][1] = a0
        @inbounds iter[2][1] = weighted_sum
        @inbounds iter[2][2] = sum
        return iter[1], iter
      end
    else
      @inbounds sum -= iter[2][current_position]
      @inbounds weighted_sum -= (current_position - 1) * iter[2][current_position]
      @inbounds iter[2][current_position] = 0
      current_position += 1
    end
  end
  return nothing
end
