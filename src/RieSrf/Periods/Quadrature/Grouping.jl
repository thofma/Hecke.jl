################################################################################
#
#  RieSrf/Periods/Quadrature/Grouping.jl : grouping the subpaths into schemes
#
#  Every subpath has its own quadrature parameter r, but computing nodes and
#  weights for every r separately is expensive. The subpaths are therefore
#  grouped: one integration scheme per group, with the smallest r of the
#  group (made a bit smaller), and every subpath uses the scheme with the
#  largest r below its own (_scheme_index).
#
#  Entry points: _gl_group_rs, _de_group_rs, _scheme_index.
#
################################################################################

# The r that is used for a group of Gauss-Legendre parameters whose smallest r
# is r: a bit smaller, but still > 1.
function _gl_group_r(r::ArbFieldElem)
  RR = parent(r)
  eps = RR(1//100)
  return r <= 1 + 2*eps ? (r + 1)/2 : r - eps
end

@doc raw"""
    _gl_group_rs(rs, err; c = 1.0, bound = 10^5) -> Vector{ArbFieldElem}

Group the sorted (ascending) GL parameters `rs` so that the total number of
abscissae plus `c` times the size of every scheme is minimal (dynamic
programming over the last group). Returns the parameters of the groups,
ascending.
"""
function _gl_group_rs(rs::Vector{ArbFieldElem}, err::ArbFieldElem;
                      c::Float64 = 1.0, bound = 10^5)
  n = length(rs)
  RR = parent(rs[1])
  B = RR(bound)
  group_r = [_gl_group_r(r) for r in rs]
  N = [Float64(Int(_gauss_legendre_parameters(r, err, B))) for r in group_r]  # decreasing in r

  # best[i + 1]: lowest cost for rs[1:i]; from[i + 1]: start of its last group
  best = fill(Inf, n + 1)
  from = zeros(Int, n + 1)
  best[1] = 0.0
  for i in 1:n
    for j in 1:i                         # last group = rs[j:i], its N is N[j]
      cost = best[j] + (i - j + 1 + c) * N[j]
      if cost < best[i+1]
        best[i+1] = cost
        from[i+1] = j
      end
    end
  end

  starts = Int[]
  i = n
  while i > 0
    j = from[i+1]
    push!(starts, j)
    i = j - 1
  end
  reverse!(starts)

  @debug "GL grouping" ngroups = length(starts) sizes = diff(vcat(starts, n + 1)) N = N[starts] total = Int(best[n+1] - c*sum(N[starts]))
  return group_r[starts]
end

# The parameters of the double exponential schemes for the sorted (ascending)
# DE parameters rs: about n/2 + 1 values evenly spaced between the smallest
# and the largest r, times 19/20 (one value if all r are within 1/20).
function _de_group_rs(rs::Vector{ArbFieldElem})
  RR = parent(rs[1])
  r_min = rs[1]
  r_max = rs[end]
  number_of_steps = max(floor(Int, length(rs)/2), 1)
  if number_of_steps == 1 && abs(r_min - r_max) < RR(1/20)
    return [RR(19/20) * r_min]
  end
  return [RR(19/20) * ((RR(1) - RR(t)/RR(number_of_steps))*r_min + RR(t)/RR(number_of_steps)*r_max)
          for t in 0:number_of_steps]
end

# The scheme for a subpath with parameter r: the last group whose parameter
# is below r (1 if there is none).
function _scheme_index(r::ArbFieldElem, group_rs::Vector{ArbFieldElem})
  index = 1
  for (i, group_r) in enumerate(group_rs)
    r > group_r && (index = i)
  end
  return index
end
