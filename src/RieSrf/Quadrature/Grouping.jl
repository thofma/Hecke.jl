################################################################################
#
#  RieSrf/Quadrature/Grouping.jl : grouping of the Gauss-Legendre parameters
#
################################################################################

# The r that is actually used for a group whose smallest r is r (same rule
# as before: a bit smaller, but still > 1).
function _gl_group_r(r::ArbFieldElem)
  RR = parent(r)
  eps = RR(1//100)
  return r <= 1 + 2*eps ? (r + 1)/2 : r - eps
end

@doc raw"""
    _gl_group_rs(rs, err; c = 1.0, bound = 10^5) -> Vector{ArbFieldElem}

Group the sorted (ascending) GL parameters `rs` so that the total number of
abscissae plus `c` times the size of every scheme is minimal. Returns the
radii of the groups, ascending.
"""
function _gl_group_rs(rs::Vector{ArbFieldElem}, err::ArbFieldElem;
                      c::Float64 = 1.0, bound = 10^5)
  n = length(rs)
  RR = parent(rs[1])
  B = RR(bound)
  reff = [_gl_group_r(r) for r in rs]
  N = [Float64(Int(gauss_legendre_parameters(r, err, B))) for r in reff]  # decreasing in r

  # best[i]: cheapest cost for rs[1:i]; from[i]: start of the last group
  best = fill(Inf, n + 1)
  from = zeros(Int, n + 1)
  best[1] = 0.0                          # index shift: best[i+1] covers rs[1:i]
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
  return reff[starts]
end
