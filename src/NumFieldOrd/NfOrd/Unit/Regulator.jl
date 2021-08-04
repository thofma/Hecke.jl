################################################################################
#
#  Free part of the unit group
#
################################################################################

@doc Markdown.doc"""
    regulator(x::Array{T, 1}, abs_tol::Int) -> arb

Compute the regulator $r$ of the elements in $x$, such that the radius of $r$
is less then `-2^abs_tol`.
"""
function regulator(x::Array{T, 1}, abs_tol::Int) where T
  K = _base_ring(x[1])
  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  p = 32

  conlog = Vector{Vector{arb}}(undef, r)

  while true
    q = 2
    for i in 1:r
      conlog[i] = conjugates_arb_log(x[i], p)
      for j in 1:r
        q = max(q, bits(conlog[i][j]))
      end
    end

    A = zero_matrix(ArbField(q, cached = false), r, r)

    for i in 1:r
      for j in 1:r
        A[i, j] = conlog[i][j]
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
  return ArbField(64, cached = false)("0.054")
end
