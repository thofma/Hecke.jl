################################################################################
#
#  Unit rank
#
################################################################################

@doc Markdown.doc"""
    unit_rank(O::NfOrd) -> Int

Returns the unit rank of $\mathcal O$, that is, the rank of the unit group
$\mathcal O^\times$.
"""
function unit_rank(O::NfOrd)
  r1, r2 = signature(nf(O))
  return r1 + r2 - 1
end

################################################################################
#
#  Test if units are independent
#
################################################################################

@doc Markdown.doc"""
    isindependent{T}(x::Array{T, 1})

Given an array of non-zero elements in a number field, returns whether they
are multiplicatively independent.
"""
function isindependent(x::Array{T, 1}, p::Int = 32) where T
  return _isindependent(x, p)
end

function _isindependent(x::Array{T, 1}, p::Int = 32) where T
  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  conlog = Vector{Vector{arb}}(undef, length(x))

  # This can be made more memory friendly
  while true
    @assert p != 0

    q = 2
    for i in 1:length(x)
      conlog[i] = conjugates_arb_log(x[i], p)
      for j in 1:rr
        q = max(q, bits(conlog[i][j]))
      end
    end

    A = zero_matrix(ArbField(q, cached = false), length(x), rr)

    for i in 1:length(x)
      for j in 1:rr
        A[i, j] = conlog[i][j]
        @assert radiuslttwopower(A[i, j], -p)
      end
    end

    Ar = base_ring(A)

    B = A*transpose(A)
    @vprint :UnitGroup 1 "Computing det of $(nrows(B))x$(ncols(B)) matrix with precision $(p) ... \n"
    d = det(B)

    y = (Ar(1)//Ar(r))^r * (Ar(21)//Ar(128) * log(Ar(deg))//(Ar(deg)^2))^(2*r)
    if isfinite(d) && ispositive(y - d)
      return false, p
    elseif isfinite(d) && ispositive(d)
      return true, p
    end
    p = 2*p
  end
end


