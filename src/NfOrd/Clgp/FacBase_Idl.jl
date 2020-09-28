################################################################################
#
#  NfFactorBase : Factor bases for number fields 
#  A factor basis is mostly a collection of prime ideals, designed,
#  if possible, to allow for rapid testing if elements are smooth.
#
################################################################################

function NfFactorBase(O::NfOrd, B::Int, F::Function, complete::Bool = false, degree_limit::Int = 0)
  @vprint :ClassGroup 2 "Splitting the prime ideals ...\n"
  lp = prime_ideals_up_to(O, B, F, complete = complete, degree_limit = degree_limit)
  @vprint :ClassGroup 2 " done \n"
  return NfFactorBase(O, lp)
end

function NfFactorBase(O::NfOrd, lp::AbstractArray{Int, 1}, degree_limit::Int = 0)
  @vprint :ClassGroup 2 "Splitting the prime ideals ...\n"
  lP = prime_ideals_over(O, lp, degree_limit = degree_limit)
  @vprint :ClassGroup 2 " done \n"
  return NfFactorBase(O, lP)
end

function NfFactorBase(O::NfOrd, B::Int;
                        complete::Bool = true, degree_limit::Int = 5)
  @vprint :ClassGroup 2 "Splitting the prime ideals ...\n"
  lp = prime_ideals_up_to(O, B, complete = complete, degree_limit = degree_limit)
  @vprint :ClassGroup 2 " done \n"
  return NfFactorBase(O, lp)
end  

function NfFactorBase(O::NfOrd, lp::Array{NfOrdIdl, 1})
  lp = sort(lp, lt = function(a,b) return norm(a) > norm(b); end)
  FB = NfFactorBase()
  FB.size = length(lp)
  FB.ideals = lp

  # Magic constant 20?
  FB.rw = Array{Int}(undef, 20)
  FB.mx = 20

  fb = Dict{fmpz, Array{Tuple{Int, NfOrdIdl}, 1}}()

  for i = 1:length(lp)
    if !haskey(fb, minimum(lp[i]))
      fb[minimum(lp[i])] = [(i, lp[i])]
    else
      push!(fb[minimum(lp[i])], (i, lp[i]))
    end
  end

  FB.fb = Dict{fmpz, FactorBaseSingleP}()
  for (p, v) in fb
    FB.fb[p] = FactorBaseSingleP(p, v)
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

function factor!(M::SMat{T}, i::Int, FB::NfFactorBase, a::nf_elem;
                 error = true, n = abs(norm(a))) where T
  fl, res = _factor(FB, a, error=error, n=n)
  if fl
    push!(M, res)
  end
  return fl
end

function _factor!(FB::NfFactorBase, a::nf_elem,
                    error::Bool = true, n::fmpq = abs(norm(a)), integral::Bool = true)
  T = fmpz
  O = order(FB.ideals[1])                  
  n = deepcopy(n)

  if integral
    df =numerator(n)
  else
    df = numerator(n)*denominator(a, O)
  end

  d = factor(FB.fb_int, df, error)  #careful: if df is non-int-smooth, then error is ignored

  rw = FB.rw
  r = Array{Tuple{Int, Int}, 1}()
  ret = true
  for p in keys(d)
    vp = valuation!(n, p)
#    s::Array{Tuple{Int, Int}, 1}, vp::Int = FB.fb[p].doit(a, vp)
    s::Array{Tuple{Int, Int}, 1}, vp::Int = fb_doit(a, vp, FB.fb[p], fmpq(p)^vp)
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
    return ret, SRow{T}(r)
  else 
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false, SRow{T}()
  end
end

function factor(FB::NfFactorBase, a::nf_elem)
  return _factor!(FB, a, true, abs(norm(a)), false)[2]
end

function _factor!(FB::Hecke.NfFactorBase, A::Hecke.NfOrdIdl,
                    error::Bool = true)
  T = fmpz                  
  O = order(A)

  n = norm(A)

  # If the ideal is the trivial ideal, return true, and the zero row
  # Otherwise factor will choke
  if isone(n)
    return true, SRow{T}()
  end

  d = factor(FB.fb_int, n) # as above: fails - even if error is false - 
  # if the norm is not smooth
  
  rw = FB.rw
  r = Array{Tuple{Int, Int}, 1}()
  for p in keys(d)
    vp = valuation(n, p)
    s = Array{Tuple{Int, Int}, 1}()
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
      return false, SRow{T}()
    end
    r = vcat(r, s)
  end
  lg::Int = length(r)
  if lg > 0
    if length(rw) > FB.mx
      FB.mx = length(rw)
    end
    sort!(r, lt = (a,b) -> a[1] < b[1])
    res = SRow{T}(r)
    @hassert :ClassGroup 9000 A == prod([FB.ideals[i]^j for (i, j) in r])
    @hassert :ClassGroup 1 length(r) > 0
    return true, res
  else 
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false, SRow{T}()
  end
end

