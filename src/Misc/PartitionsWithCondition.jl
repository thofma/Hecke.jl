mutable struct PartitionsWithCondition
  n::Int
  k::Int
  l::Int
  sum::Int
  weighted_sum::Int
  vect::Vector{Int}
  isdone::Bool
  # The struct stores an integer vector, i.e. the vector [a_0, ..., a_{k-1}], together with
  # sum = a_2 + ... + a_{k-1} and weighted_sum = 2*a_2 + 3*a_3 + ... + (k-1)*a_{k-1}.
  # This yields faster computations.

  function PartitionsWithCondition(n::Int, k::Int, l::Int)
    # Catch non-meaningful input
    @req n>=0 "n should be >= 0"
    @req k>=0 "k should be >= 0"
    isdone = false
    if k<=1 && l>0
      isdone = true
    end
    return new(n, k, l, 0, 0, zeros(Int, k), isdone)
  end

end

@doc raw"""
    partitions_with_condition(
      n::Int,
      k::Int,
      l::Int
    ) -> iterator

Return a statful inplace iterator which enumerates all possible `k`-tuples ``[ a_0, ..., a_{k-1} ]`` of
nonnegative integers satisfying ``a_0 + a_1 + ... + a_{k-1} = n`` and,
furthermore, ``0*a_0 + 1*a_1 + 2*a_2 + ... + (k-1)*a_{k-1} = l``.

# Examples

```jldoctest
julia> for i in partitions_with_condition(5, 3, 7) println(i) end
[0, 3, 2]
[1, 1, 3]

julia> for i in partitions_with_condition(2, 1, 0) println(i) end
[2]

julia> for i in partitions_with_condition(2, 1, 1) println(i) end

julia> for i in partitions_with_condition(7, 4, 12) println(i) end
[0, 2, 5, 0]
[1, 0, 6, 0]
[1, 3, 0, 3]
[2, 1, 1, 3]
[3, 0, 0, 4]
```
"""
partitions_with_condition(n::Int, k::Int, l::Int) = PartitionsWithCondition(n, k, l)

function Base.iterate(parti::PartitionsWithCondition)
  if parti.k <= 1
    # If k is 0, 1, the problem is trivial
    if parti.k==1 && parti.l==0
      parti.isdone = true
      return Int[parti.n], nothing
    elseif parti.k==0 && parti.l==0
      return Int[], nothing
    else
      return nothing
    end
  end
  firstlist = parti.vect
  firstlist[1] = parti.n - parti.l
  firstlist[2] = parti.l
  parti.sum = 0
  parti.weighted_sum = 0
  parti.isdone = parti.l==parti.n
  if parti.l <= parti.n
    return firstlist, nothing
  else
    return iterate(parti, nothing)
  end
end

function Base.iterate(parti::PartitionsWithCondition, xxx::Nothing)
  if parti.k == 1
    return nothing
  end
  current_position = 3
  # For every choice of integers a_2, a_3, ... a_{k-1} there exists a unique pair of integers
  # (a_0, a_1) fulfilling the two equations. Hence, we can iterate over all such choices and
  # calculate the corresponding pair (a_0, a_1) and check, whether a_0 and a_1 are both >= 0.
  kp1 = parti.k + 1
  while current_position < kp1
    parti.sum += 1
    parti.weighted_sum += current_position - 1
    @inbounds parti.vect[current_position] += 1
    a1 = parti.l - parti.weighted_sum
    if a1 >= 0
      a0 = parti.n - parti.sum - a1
      if a0 >= 0
        @inbounds parti.vect[1] = a0
        @inbounds parti.vect[2] = a1
        return parti.vect, nothing
      else
        current_position = 3
      end
    else
      @inbounds parti.sum -= parti.vect[current_position]
      @inbounds parti.weighted_sum -= (current_position - 1) * parti.vect[current_position]
      @inbounds parti.vect[current_position] = 0
      current_position += 1
    end
  end
  parti.isdone = true
  return nothing
end

Base.IteratorSize(::PartitionsWithCondition) = Base.SizeUnknown()

Base.eltype(::PartitionsWithCondition) = Vector{Int}
Base.isdone(iter::PartitionsWithCondition) = iter.isdone
