
#########################################################################################
#
#   qAdic Conj structure
#
#########################################################################################

# Honestly the thing that is needed here is a pure Julia implementation of the HenselCtx.
# Field definitions should use a "Krasner criteria" to detect if the extensions are distinct.

################################################################################
# Root contexts for lifting algorithms
################################################################################

mutable struct qAdicRootCtx
  f::fmpz_poly
  p::Int
  n::Int
  Q::Array{FlintQadicField, 1}
  H::Hecke.HenselCtx
  R::Array{qadic, 1} # These are the cached roots.
  function qAdicRootCtx(f::fmpz_poly, p::Int)
    r = new()
    r.f = f
    r.p = p
    r.H = H = Hecke.factor_mod_pk_init(f, p)
    lf = Hecke.factor_mod_pk(H, 1)
    #TODO:XXX: Careful: QadicField ONLY works, currently, in Conway range
    Q = [QadicField(p, x, 1) for x = Set(degree(y) for y = keys(lf))]
    @assert all(isone, values(lf))
    r.Q = Q

    #NOTE: Roots are not computed when initialized, as no precision has been determined.
    return r
  end
end



"""
    qAdicConj(K::AnticNumberField, p::Int)

Creates a data structure to compute the conjugates in a unramified splitting field
over Q_p.
"""
# This structure doesn't compute anything really.

# It mostly just explicitly associates a number field to a Qadic field.

# The work in the initialization is hidden in the HenselCtx step.
# It would make more sense to have some computation precomputed.

# This object doesn't know very much right now.

mutable struct qAdicConj
  K::AnticNumberField
  C::qAdicRootCtx
  cache::Dict{nf_elem, Any}

  function qAdicConj(K::AnticNumberField, p::Int)
    isindex_divisor(maximal_order(K), p) && error("cannot deal with index divisors yet")
    isramified(maximal_order(K), p) && error("cannot deal with ramification yet")

    # Check for cached data. If none, update the reference in K to set
    # `D` as the local conjugate data.
    # D = _get_nf_conjugate_data_qAdic(K, false)
    # if D !== nothing
    #   if haskey(D, p)
    #     Dp = D[p]
    #     return new(K, Dp[1], Dp[2])
    #   end
    # else
    #   D = Dict{Int, Tuple{qAdicRootCtx, Dict{nf_elem, Any}}}()
    #   _set_nf_conjugate_data_qAdic(K, D)
    # end

    # Initialize the new structure.  
    Zx = PolynomialRing(FlintZZ, cached = false)[1]
    C = qAdicRootCtx(Zx(K.pol), p)
    r = new()
    r.C = C
    r.K = K

    # cache for conjugates of a given number field element??
    r.cache = Dict{nf_elem, Any}()
    #D[p] = (C, r.cache)
    return r
  end
end

# Display for conjugates data.
function Base.show(io::IO, C::qAdicConj)
  println(io, "data for the $(C.C.p)-adic completions of $(C.K)")
end



#########################################################################################
#
#   Newton lifting and root finding
#
#########################################################################################


"""
    roots(f::fmpz_poly, Q::FlintQadicField; max_roots::Int = degree(f)) -> Array{qadic, 1}
The roots of f in Q, f has to be square-free (at least the roots have to be simple roots).    
"""

import Hecke.roots
function roots(C::qAdicRootCtx, n::Int = 10)
  if isdefined(C, :R) && all(x -> x.N >= n, C.R)
    return [setprecision(x, n) for x = C.R]
  end
  lf = factor_mod_pk(C.H, n)
  rt = qadic[]
  for Q = C.Q
    Q.prec_max = n
    for x = keys(lf)
      if degree(x) == degree(Q)
        push!(rt, Hecke.any_root(x, Q)[1])
      end
    end
  end
  if isdefined(C, :R)
    st = qadic[]
    for r = C.R
      p = findfirst(x -> degree(parent(r)) == degree(parent(x)) && iszero(x-r), rt)
      push!(st, rt[p])
    end
    rt = st
  end
  C.R = rt
  return rt
end

