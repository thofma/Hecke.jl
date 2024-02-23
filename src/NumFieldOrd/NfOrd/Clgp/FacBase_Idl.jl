################################################################################
#
#  NfFactorBase : Factor bases for number fields
#  A factor basis is mostly a collection of prime ideals, designed,
#  if possible, to allow for rapid testing if elements are smooth.
#
################################################################################

function NfFactorBase(O::AbsSimpleNumFieldOrder, B::Int, F::Function, complete::Bool = false, degree_limit::Int = 0)
  @vprintln :ClassGroup 2 "Splitting the prime ideals ..."
  lp = prime_ideals_up_to(O, B, F, complete = complete, degree_limit = degree_limit)
  @vprintln :ClassGroup 2 " done"
  return NfFactorBase(O, lp)
end

function NfFactorBase(O::AbsSimpleNumFieldOrder, lp::AbstractVector{Int}, degree_limit::Int = 0)
  @vprintln :ClassGroup 2 "Splitting the prime ideals ..."
  lP = prime_ideals_over(O, lp, degree_limit = degree_limit)
  @vprintln :ClassGroup 2 " done"
  return NfFactorBase(O, lP)
end

function NfFactorBase(O::AbsSimpleNumFieldOrder, B::Int;
                        complete::Bool = true, degree_limit::Int = 5)
  @vprintln :ClassGroup 2 "Splitting the prime ideals ..."
  lp = prime_ideals_up_to(O, B, complete = complete, degree_limit = degree_limit)
  @vprintln :ClassGroup 2 " done"
  return NfFactorBase(O, lp)
end

function NfFactorBase(O::AbsSimpleNumFieldOrder, lp::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  lp = sort(lp, lt = function(a,b) return norm(a, copy = false) > norm(b, copy = false); end)
  FB = NfFactorBase()
  FB.size = length(lp)
  FB.ideals = lp

  # Magic constant 20?
  FB.rw = Array{Int}(undef, 20)
  FB.mx = 20

  fb = Dict{ZZRingElem, Vector{Tuple{Int, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}}()

  for i = 1:length(lp)
    if !haskey(fb, minimum(lp[i]))
      fb[minimum(lp[i])] = [(i, lp[i])]
    else
      push!(fb[minimum(lp[i])], (i, lp[i]))
    end
  end

  FB.fb = Dict{ZZRingElem, FactorBaseSingleP}()
  for (p, v) in fb
    if fits(Int, p)
      FB.fb[p] = FactorBaseSingleP(Int(p), v)
    else
      FB.fb[p] = FactorBaseSingleP(p, v)
    end
  end

  FB.fb_int = FactorBase(Set(keys(FB.fb)); check = false)

  return FB
end

function ring(F::NfFactorBase)
  return order(F.ideals[1])
end

order(F::NfFactorBase) = ring(F)

################################################################################
#
#  Factor number field element over factor base. Put valuations into row i of
#  the relation matrix M. The matrix M needs to have at least as many columns
#  as the FB has ideals.
#
################################################################################

function factor!(M::SMat{T}, i::Int, FB::NfFactorBase, a::AbsSimpleNumFieldElem;
                 error = true, n = abs(norm(a))) where T
  fl, res = _factor(FB, a, error=error, n=n)
  if fl
    push!(M, res)
  end
  return fl
end

function _factor!(FB::NfFactorBase, a::AbsSimpleNumFieldElem,
                    error::Bool = true, n::QQFieldElem = abs(norm(a)), integral::Bool = true)
  T = ZZRingElem
  O = order(FB.ideals[1])
  n = deepcopy(n)

  if integral
    df =numerator(n)
  else
    df = numerator(n)*denominator(a, O)
  end
  if isone(df)
    return true, sparse_row(FlintZZ)
  end

  d = factor(FB.fb_int, df, error)  #careful: if df is non-int-smooth, then error is ignored

  rw = FB.rw
  r = Vector{Tuple{Int, Int}}()
  ret = true
  for p in keys(d)
    vp = valuation!(n, p)
    s::Vector{Tuple{Int, Int}}, vp::Int = fb_doit(a, vp, FB.fb[p], QQFieldElem(p)^vp)
    if !iszero(vp)
      ret = false
      if error
        @assert iszero(vp)
      end
    end
    r = vcat(r, s)
  end
  lg::Int = length(r)
  if lg > 0
    if length(rw) > FB.mx
      FB.mx = length(rw)
    end
    sort!(r, lt=function(a,b) return a[1] < b[1]; end)
    if ret
      @hassert :ClassGroup 9000  ideal(O, a) == prod([FB.ideals[i]^j for (i, j) in r])
    end
    @hassert :ClassGroup 1 length(r) > 0
    return ret, sparse_row(FlintZZ, r)
  else
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false, sparse_row(FlintZZ)
  end
end

function factor(FB::NfFactorBase, a::AbsSimpleNumFieldElem)
  return _factor!(FB, a, true, abs(norm(a)), false)[2]
end

function _factor!(FB::Hecke.NfFactorBase, A::Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},
                    error::Bool = true)
  T = ZZRingElem
  O = order(A)

  n = norm(A)

  # If the ideal is the trivial ideal, return true, and the zero row
  # Otherwise factor will choke
  if isone(n)
    return true, sparse_row(FlintZZ)
  end

  d = factor(FB.fb_int, n) # as above: fails - even if error is false -
  # if the norm is not smooth

  rw = FB.rw
  r = Vector{Tuple{Int, Int}}()
  for p in keys(d)
    vp = valuation(n, p)
    s = Vector{Tuple{Int, Int}}()
    for P=FB.fb[p].lp
      v = valuation(A, P[2])
      if v != 0
        push!(s, (P[1], v))
        vp -= v*P[2].splitting_type[2]
        if iszero(vp)
          break
        end
      end
    end
    if vp != 0
      if error
        @assert vp == 0
      end
      return false, sparse_row(FlintZZ)
    end
    r = vcat(r, s)
  end
  lg::Int = length(r)
  if lg > 0
    if length(rw) > FB.mx
      FB.mx = length(rw)
    end
    sort!(r, lt = (a,b) -> a[1] < b[1])
    res = sparse_row(FlintZZ, r)
    @hassert :ClassGroup 9000 A == prod([FB.ideals[i]^j for (i, j) in r])
    @hassert :ClassGroup 1 length(r) > 0
    return true, res
  else
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false, sparse_row(FlintZZ)
  end
end

