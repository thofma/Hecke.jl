################################################################################
#
#  Free part of the unit group
#
################################################################################

doc"""
***
    regulator(x::Array{T, 1}, abs_tol::Int) -> arb

> Compute the regulator $r$ of the elements in $x$, such that the radius of $r$
> is less then `-2^abs_tol`.
"""
function regulator(x::Array{T, 1}, abs_tol::Int) where T
  K = _base_ring(x[1])
  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  p = 32

  while true
    conlog = conjugates_arb_log(x[1], p)

    A = ArbMatSpace(parent(conlog[1]), r, r)()

    for j in 1:r
      A[1, j] = conlog[j]
    end

    for i in 2:r
      conlog = conjugates_arb_log(x[i], p)
      for j in 1:r
        A[i, j] = conlog[j]
      end
    end

    z = abs(det(A))

    if isfinite(z) && radiuslttwopower(z, -abs_tol)
      return z
    end

    p = 2*p
  end
end

function lower_regulator_bound(K::AnticNumberField)
  return ArbField(64)("0.054")
end
