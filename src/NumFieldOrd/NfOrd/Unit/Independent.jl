################################################################################
#
#  Unit rank
#
################################################################################

@doc raw"""
    unit_group_rank(O::AbsSimpleNumFieldOrder) -> Int

Returns the unit rank of $\mathcal O$, that is, the rank of the unit group
$\mathcal O^\times$.
"""
function unit_group_rank(O::AbsSimpleNumFieldOrder)
  return unit_group_rank(nf(O))
end

################################################################################
#
#  Test if units are independent
#
################################################################################

@doc raw"""
    is_independent{T}(x::Vector{T})

Given an array of non-zero units in a number field, returns whether they
are multiplicatively independent.
"""
function is_independent(x::Vector{T}, p::Int = 32) where T
  return _isindependent(x, p)
end

function _isindependent(x::Vector{T}, p::Int = 32) where T
  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  conlog = Vector{Vector{ArbFieldElem}}(undef, length(x))

  # This can be made more memory friendly
  while true
    @assert p != 0

    q = 2
    for i in 1:length(x)
      @vprintln :UnitGroup 3 "Computing conjugates with precision $p of ($i) $(length(x[i].fac))..."
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
    @vprintln :UnitGroup 1 "Computing det of $(nrows(B))x$(ncols(B)) matrix with precision $(p) ..."
    d = det(B)

    y = (Ar(1)//Ar(r))^r * (Ar(21)//Ar(128) * log(Ar(deg))//(Ar(deg)^2))^(2*r)
    if isfinite(d) && is_positive(y - d)
      return false, p
    elseif isfinite(d) && is_positive(d)
      return true, p
    end
    p = 2*p
  end
end
