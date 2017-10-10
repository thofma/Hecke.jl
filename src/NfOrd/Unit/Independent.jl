################################################################################
#
#  Unit rank
#
################################################################################

doc"""
***
    unit_rank(O::NfOrd) -> Int

> Returns the unit rank of $\mathcal O$, that is, the rank of the unit group
> $\mathcal O^\times$.
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

doc"""
***
    isindependent{T}(x::Array{T, 1})

> Given an array of non-zero elements in a number field, returns whether they
> are multiplicatively independent.
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

  # This can be made more memory friendly
  while true
    @assert p != 0

    conlog = conjugates_arb_log(x[1], p)

    A = zero_matrix(parent(conlog[1]), length(x), rr)

    for i in 1:rr
      A[1, i] = conlog[i]
    end

    Ar = base_ring(A)

    for k in 2:length(x)
      conlog = conjugates_arb_log(x[k], p)
      for i in 1:rr
        A[k, i] = conlog[i]
      end
    end

    B = A*transpose(A)
    @vprint :UnitGroup 1 "Computing det of $(rows(B))x$(cols(B)) matrix with precision $(p) ... \n"
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


