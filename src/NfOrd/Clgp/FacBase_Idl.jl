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
  FB.rw = Array{Int}(20)
  FB.mx = 20

  fb = Dict{fmpz, Array{Tuple{Int, NfOrdIdl}, 1}}()

  for i = 1:length(lp)
    if !haskey(fb, lp[i].gen_one)
      fb[lp[i].gen_one] = [(i, lp[i])]
    else
      push!(fb[lp[i].gen_one], (i, lp[i]))
    end
  end

  FB.fb = Dict{fmpz, FactorBaseSingleP}()
  for p in keys(fb)
    FB.fb[p] = FactorBaseSingleP(p, fb[p])
  end

  FB.fb_int = FactorBase(Set(keys(FB.fb)); check = false)

  return FB
end

################################################################################
#
#  Factor number field element over factor base. Put valuations into row i of
#  the relation matrix M. The matrix M needs to have at least as many columns
#  as the FB has ideals.
#
################################################################################

function factor!{T}(M::SMat{T}, i::Int, FB::NfFactorBase, a::nf_elem;
                    error = true, n = abs(norm(a)))
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

  if integral
    df =num(n)
  else
    df = num(n)*den(a, O)
  end

  d = factor(FB.fb_int, df)  #careful: if df is non-int-smooth, then error is ignored

  rw = FB.rw
  r = Array{Tuple{Int, Int}, 1}()
  for p in keys(d)
    vp = valuation(n, p)
    s, vp = FB.fb[p].doit(a, vp)
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
    sort!(r, lt=function(a,b) return a[1] < b[1]; end)
    @hassert :ClassGroup 1 length(r) > 0
    return true, SRow{T}(r)
  else 
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false, SRow{T}()
  end
end

function factor(FB::NfFactorBase, a::nf_elem)
  M = SMat{Int}()
  _factor!(M, 1, FB, a)
  return M
end

function _factor!(FB::Hecke.NfFactorBase, A::Hecke.NfOrdIdl,
                    error::Bool = true)
  T = fmpz                  
  O = order(A)

  n = norm(A)
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
    sort!(r, lt=function(a,b) return a[1] < b[1]; end)
    @hassert :ClassGroup 1 length(r) > 0
    return true, SRow{T}(r)
  else 
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false, SRow{T}()
  end
end

