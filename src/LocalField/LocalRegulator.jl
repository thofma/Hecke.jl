
#########################################################################################
#
#   Stuff for regulators
#
#########################################################################################

#=
@doc Markdown.doc"""
    conjugates_log(a::nf_elem, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []
    conjugates_log(a::FacElem{nf_elem, AnticNumberField}, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []

Returns an array of the logarithms of the q-adic conjugates of $a$: Let $p Z_K = \prod P_i$ for the maximal order
$Z_K$ of the parent of $a$. Then $K \otimes Q_p = \prod K_{P_i}$. For each of the $P_i$
a $q$-adic (unramifed) extension $K_{P_i}$ of $Q_p$ is computed, sth. $a$ has $\deg P_i = \deg K_{P_i}$
many cojugates in $K_{P_i}$.
If {{{all = true}}} and {{{ flat = false}}} then all $n$ logarithms of conjugates are returned.
If {{{all = false}}}, then for each $P_i$ only one logarithm of a conjugate if returned, the others could be 
xomputed using automorphisms (the Frobenius).
If {{{flat = true}}}, then instead of the conjugates, only the $p$-adic coefficients are returned.
"""

function conjugates_log(a::nf_elem, C::qAdicConj, n::Int = 10;
                        all::Bool = false, flat::Bool = true)
  if haskey(C.cache, a)
    b = C.cache[a]
    if b[1,1].N == n
      return expand(b, all = all, flat = flat)
    end
  end
  C.cache[a] = b = _conjugates(a, C, n, iwasawa_log)
  return expand(b, all = all, flat = flat)
end
=#

#=
function conjugates_log(a::FacElem{nf_elem, AnticNumberField}, C::qAdicConj, n::Int = 10;
                        all::Bool = false, flat::Bool = true)
  first = true
  local res::Array{qadic, 1}
  for (k, v) = a.fac
    try 
      y = conjugates_log(k, C, n, flat = false, all = false)
      if first
        res = v .* y
        first = false
      else
        res += v .* y
      end
    catch e
      if isa(e, DivideError) || isa(e, DomainError)
        lp = prime_decomposition(maximal_order(parent(k)), C.C.p)
        @assert Base.all(x -> has_2_elem_normal(x[1]), lp)
        val = map(x -> valuation(k, x[1]), lp)

        # Adjust the valuation of `a` so that it has valuation 0 at all the prime places
        pe = prod(lp[i][1].gen_two^val[i] for i = 1:length(lp) if val[i] != 0)
          aa = k//pe

        # Then take the logarithm again...
        y = conjugates_log(aa, C, n, all = false, flat = false)

        if first
          res = v .* y
          first = false
        else
          res += v .* y
        end
      else
        rethrow(e)
      end
    end
  end
  return expand(res, all = all, flat = flat)
end
=#

# TODO: The special gram matrix does not always faithfully remember the rank of the original matrix.
# However, it would be interesting if we could construct a reasonable square matrix where
# this is the case.
function special_gram(m::Array{Array{qadic, 1}, 1})
  g = Array{padic, 1}[]
  for i = m
    r = padic[]
    for j = m
      k = 1
      S = 0
      while k <= length(i)
        s = i[k] * j[k]
        for l = 1:degree(parent(s))-1
          s += i[k+l] * j[k+l]
        end
        S += coeff(s, 0)
        @assert s == coeff(s, 0)
        k += degree(parent(s))
      end
      push!(r, S)
    end
    push!(g, r)
  end
  return g
end

function special_gram(m::Array{Array{padic, 1}, 1})
  n = matrix(m)
  n = n'*n
  return [[n[i,j] for j=1:ncols(n)] for i = 1:nrows(n)]
end

@doc Markdown.doc"""
    regulator(u::Array{T, 1}, C::qAdicConj, n::Int = 10; flat::Bool = true) where {T<: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}
    regulator(K::AnticNumberField, C::qAdicConj, n::Int = 10; flat::Bool = true)
    regulator(R::NfAbsOrd, C::qAdicConj, n::Int = 10; flat::Bool = true)

Returns the determinant of $m^t m$ where the columns of $m$ are the {{{conjugates_log}}} of the units in either the array, or the fundamental units for $K$ (the maximal order of $K$) or $R$.

If {{{flat = false}}}, then all prime ideals over $p$ need to have the same degree.

In either case, Leopold's conjecture states that the regulator is zero iff the units are dependent.
"""
function regulator(u::Array{T, 1}, C::qAdicConj, n::Int = 10; flat::Bool = true) where {T<: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}
  c = map(x -> conjugates_log(x, C, n, all = !flat, flat = flat), u)
  return det(matrix(special_gram(c)))
end

function regulator(K::AnticNumberField, C::qAdicConj, n::Int = 10; flat::Bool = false)
  return regulator(maximal_order(K), C, n, flat = flat)
end

function regulator(R::NfAbsOrd{AnticNumberField, nf_elem}, C::qAdicConj, n::Int = 10; flat::Bool = false)
  u, mu = unit_group_fac_elem(R)
  return regulator([mu(u[i]) for i=2:ngens(u)], C, n, flat = flat)
end

@doc Markdown.doc"""
    regulator_iwasawa(u::Array{T, 1}, C::qAdicConj, n::Int = 10) where {T<: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}} -> qadic
    regulator_iwasawa(K::AnticNumberField, C::qAdicConj, n::Int = 10) -> qadic
    regulator_iwasawa(R::NfAbsOrd, C::qAdicConj, n::Int = 10) -> qadic

For a totally real field $K$, the regulator as defined by Iwasawa: the determinant of the
matrix containing the logarithms of the conjugates, supplemented by a column containing all $1$.
"""
function regulator_iwasawa(u::Array{T, 1}, p, prec::Int = 10) where {T<: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}

    # Needs to be a bit more robust...
    #k = base_ring(u[1])
    #@assert istotally_real(k)
    #c = map(x -> conjugates_log(x, C, prec, all = true, flat = false), u)


    log_embeddings = map(x->iwasawa_log.(embedding_classes(x,p,prec)), u)

    @info "" log_embeddings

    # TODO: One needs to construct a common embedding into Cp of the various embeddings,
    #       before the conjugates can be properly computed.

    error("Function still in development. The present issue is a lack of `compositum` method.")
    
    log_conjugates = map(x->galois_orbit(x), log_embeddings)

    @info log_conjugates
    
    m = matrix(c)
    m = hcat(m, matrix(base_ring(m), nrows(m), 1, [one(base_ring(m)) for i=1:nrows(m)]))
    return det(m)//degree(k)
end

function regulator_iwasawa(K::AnticNumberField, p, prec::Int = 10)  
  return regulator_iwasawa(maximal_order(K), p, prec)
end

function regulator_iwasawa(R::NfAbsOrd, p, prec::Int = 10)
  # Why factored elements?
  u, mu = unit_group_fac_elem(R)
  return regulator_iwasawa([mu(u[i]) for i=2:ngens(u)], p, prec)
end

function matrix(a::Array{Array{T, 1}, 1}) where {T}
  return matrix(hcat(a...))
end


############################################################################################
#
# New stuff.


