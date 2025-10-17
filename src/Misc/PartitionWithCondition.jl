@doc raw"""
  partition_with_condition(
    n::Int,
    k::Int,
    l::Int
  ) -> iterator
  
  This code provides an iterator ``partition_with_condition(n, k, l)``. This
  iterator enumerates all possible ``k``-tuples ``[ a_0, ..., a_{k-1} ]`` of
  nonnegative integers satisfying ``a_0 + a_1 + ... + a_{k-1} = n`` and,
  furthermore, ``0*a_0 + 1*a_1 + 2*a_2 + ... + (k-1)*a_{k-1} = l``.

  # Examples
  ```jldoctest
  julia> for i in partition_with_condition(5, 3, 7) println(i) end
  [0, 3, 2]
  [1, 1, 3]

  julia> for i in partition_with_condition(2, 1, 0) println(i) end
  [2]

  julia> for i in partition_with_condition(2, 1, 1) println(i) end

  julia> for i in partition_with_condition(7, 4, 12) println(i) end
  [0, 2, 5, 0]
  [1, 0, 6, 0]
  [1, 3, 0, 3]
  [2, 1, 1, 3]
  [3, 0, 0, 4]
  ```
"""
mutable struct PartitionWithCondition
  n::Int
  k::Int
  l::Int
  sum::Int
  weighted_sum::Int
  vect::Vector{Int}

  function PartitionWithCondition(n::Int, k::Int, l::Int)
    # Catch non-meaningful input
    @req n>=0 "n should be >= 0"
    @req k>0 "k should be > 0"
    @req l>=0 "l should be >= 0"
    return new(n, k, l, 0, 0, zeros(Int, k))
  end

end

partition_with_condition(n::Int, k::Int, l::Int) = PartitionWithCondition(n, k, l)

function Base.iterate(parti::PartitionWithCondition)
  if parti.k == 1
    # If k is 1, the problem is trivial
    if parti.l == 0
      return Int[parti.n], nothing
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
  parti.sum = 0
  parti.weighted_sum = 0
  if parti.l == 0
    return firstlist, nothing
  else
    return iterate(parti, nothing)
  end
end

function Base.iterate(parti::PartitionWithCondition, xxx::Nothing)
  if parti.k == Int(1)
    return nothing
  end
  current_position = Int(3)
  # For every choice of integers a_2, a_3, ... a_{k-1} there exists a unique pair of integers
  # (a_0, a_1) fulfilling the two equations. Hence, we can iterate over all such choices and
  # calculate the corresponding pair (a_0, a_1) and check, whether a_0 and a_1 are both >= 0.
  while current_position < parti.k+1
    parti.sum += 1
    parti.weighted_sum += current_position - 1
    parti.vect[current_position] += 1
    a1 = parti.l - parti.weighted_sum
    if a1 >= 0
      a0 = parti.n - parti.sum - a1
      if a0 >= 0
        @inbounds parti.vect[1] = a0
        @inbounds parti.vect[2] = a1
        return parti.vect, nothing
      end
    else
      @inbounds parti.sum -= parti.vect[current_position]
      @inbounds parti.weighted_sum -= (current_position - 1) * parti.vect[current_position]
      parti.vect[current_position] = 0
      current_position += 1
    end
  end
  return nothing
end
