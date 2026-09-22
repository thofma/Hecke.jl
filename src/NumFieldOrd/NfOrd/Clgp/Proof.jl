# Import the progress bar and Dates for the conversion of seconds
import Dates

# This is a modified showprogress from Pkg.GitTools

PROGRESS_BAR_PERCENTAGE_GRANULARITY = Ref(0.001)

Base.@kwdef mutable struct MiniProgressBar
    max::Float64 = 1.0
    header::String = ""
    color::Symbol = :white
    width::Int = 40
    current::Float64 = 0.0
    prev::Float64 = 0.0
    has_shown::Bool = false
    time_shown::Float64 = 0.0
end

function showprogress(io::IO, p::MiniProgressBar, info)
  perc = max(p.current / p.max * 100, 0.0)
  prev_perc = p.prev / p.max * 100
  # Bail early if we are not updating the progress bar,
  # Saves printing to the terminal
  if p.has_shown && !((perc - prev_perc) > PROGRESS_BAR_PERCENTAGE_GRANULARITY[])
    return
  end
  if !isinteractive()
    t = time()
    if p.has_shown && (t - p.time_shown) < NONINTERACTIVE_TIME_GRANULARITY[]
      return
    end
    p.time_shown = t
  end
  p.time_shown = time()
  p.prev = p.current
  p.has_shown = true
  n_filled = ceil(Int, p.width * perc / 100)
  n_left = p.width - n_filled
  print(io, "    ")
  printstyled(io, p.header, color=p.color, bold=true)
  print(io, " [")
  print(io, "="^n_filled, ">")
  print(io, " "^n_left, "]  ", )
  @printf io "%2.3f %%" perc
  print(io, info)
  print(io, "\r")
end

################################################################################
#
#  Class group verification
#
################################################################################

function _class_group_proof(c, U, primes_checked = nothing)
  if !c.GRH
    return true
  end
  @vprintln :ClassGroupProof 1 "Testing all primes up to $(factor_base_bound_minkowski(order(c)))"
  class_group_proof(c, ZZRingElem(2), factor_base_bound_minkowski(order(c)))
  for (p, _) in factor(c.h)
    primes_checked isa Vector && p in primes_checked && continue

    while saturate!(c, U, Int(p), 3.5)
    end

    if primes_checked isa Vector
      push!(primes_checked, p)
    end
  end
  c.GRH = false
  return true
end

function _class_group_proof_one_primedeal(clg::ClassGrpCtx, clgFB, k, p, np, extra, prec = 100)
  E = class_group_small_real_elements_relation_start(clg, k, limit=10, prec=prec)
  while true
    a = class_group_small_real_elements_relation_next(E)
    n = norm_div(a, norm(k), np)
    if gcd(numerator(n), p) > extra
      # println("a: $a, $(norm(a)), $(norm(k)), $n")
      # println("contains too many conjugates, bad")
      continue
    end
    f, r = is_smooth!(clgFB.fb_int, numerator(n))
    if f
      fl = _factor!(clgFB, a, false, n)[1]
      if fl
        return true
      else
        # println("not smooth, ideal")
      end
    else
      # println("not smooth, int")
    end
  end
  return false
end

function _li_inverse(x)
  y = log(x)
  return x*((log(y) - 2)/y + y + log(y) - 1)
end

function _prime_partition(do_it, nt)
  if nt == 1
    return do_it
  end
  @assert first(do_it) == 1
  ub = last(do_it)
  np = ceil(Int, max(10.0, logarithmic_integral(1.0*ub)))
  primes_per_thread = ceil(Int, np//nt)
  intervals = collect(Iterators.partition(1:np, primes_per_thread))
  res = UnitRange{Int}[]
  for i in 1:length(intervals)
    if i > 1
      x = last(res[end]) + 1
    else
      x = 1
    end
    if i < length(intervals)
      y = ceil(Int, _li_inverse(last(intervals[i])))
    else
      y = ub
    end
    push!(res, x:y)
  end
  @assert length(res) <= nt
  return res
end

function class_group_proof(clg::ClassGrpCtx, lb::ZZRingElem, ub::ZZRingElem; extra::ZZRingElem=ZZRingElem(0), prec::Int = 100, do_it=1:ub, try_parallel = true)

  nt = Threads.nthreads()
  if nt == 1 || try_parallel == false
    return class_group_proof_raw(clg, lb, ub; extra, prec, do_it, clgFB = deepcopy(clg.FB))
  else
    # First idea: partition the primes according to some classes mod N
    # This creates unequal workload (e.g. if the field is abelian and N has something to do with the conductor)
    # so don't do that.
    #
    # New idea: partition 1:N into nt parts containing roughly the
    # same number of primes
    part = _prime_partition(do_it, nt)
    @sync for i in 1:length(part)
        FB = deepcopy(clg.FB)
        _part = part[i]
        Threads.@spawn class_group_proof_raw(clg, ZZ(first(_part)), ZZ(last(_part)); extra, prec, filter = x -> true, clgFB = FB, used_threads = length(part), do_it = first(_part):last(_part))
    end
  end
end

function class_group_proof_raw(clg::ClassGrpCtx, lb::ZZRingElem, ub::ZZRingElem; extra::ZZRingElem=ZZRingElem(0), prec::Int = 100, do_it=1:ub, filter = x -> true, clgFB = clg.FB, used_threads = 1)
  PB = MiniProgressBar(header = "Class group proof")

  #for all prime ideals P with lb <= norm <= ub, find a relation
  #tying that prime to the factor base
  # if extra is useful, assume that the function was already run for all primes
  # up to norm extra

  if extra == 0
    extra = norm(clgFB.ideals[1])
  end
  lb = max(lb, norm(clgFB.ideals[1]))
  #println("expect to need ", Int(floor(li(ub*1.0) - li(lb*1.0))), " primes")
  O = order(clgFB.ideals[1])
  n = degree(O)
  p = next_prime(iroot(lb, n))
  np = Int(floor(log(abs(discriminant(O)))/log(2)/2))
  no_primes = 0
  no_ideals = 0
  if first(do_it) > 1
    p = ZZRingElem(next_prime(first(do_it)))
  end
  r = ZZRingElem()
  _no_of_primes = logarithmic_integral(Float64(ub)) - logarithmic_integral(Float64(lb))
  #gc_enable(false)
  rate = 0.0
  length_eta = 0
  if _no_of_primes < 1000
    interval = 10
  else
    interval = 1000
  end

  while p < last(do_it)
    if !filter(p)
      p = next_prime(p)
      continue
    end
    no_primes += 1

    @v_do :ClassGroupProof if no_primes % interval == 0
      if Threads.nthreads() > 1
        Core.println("Thread ", Threads.threadid(), " ", no_primes, "/", _no_of_primes)
      else
        #println("did $no_primes prime numbers so far, now $p, need to reach $ub (~$(no_primes/_no_of_primes))")
        last_time = PB.time_shown
        cur_time = time()
        prev = PB.prev
        PB.current = min(no_primes/_no_of_primes, 1.0)
        # from PB.current to prev it took cur_time - last_time seconds

        if rate == 0.0
          rate = ((PB.current - PB.prev)/(cur_time - last_time))
        else
          rate = (((PB.current - PB.prev)/(cur_time - last_time)) + rate)/2
        end

        duration = (1 - PB.current)/rate

        duration = round(Int, duration)
        ETA = " (ETA: $(Dates.Time(Dates.Nanosecond(duration * 10^9))))"
        if length(ETA) < length_eta
          ETA = ETA * " "^(length_eta - length(ETA))
        else
          length_eta = length(ETA)
        end

        showprogress(stdout, PB, ETA)
        flush(stdout)
      end
    end

    deg_lim = Int(flog(ub, p))
    if deg_lim == 1
      low_lim = 1
    else
      low_lim = Int(flog(lb, p))
    end
    fac = prime_decomposition(O, Int(p), deg_lim, low_lim)
    for _k in fac
      k = _k[1]
      if norm(k) <= lb
        continue
      end
      no_ideals += 1
      _class_group_proof_one_primedeal(clg, clgFB, k, p, np, extra, prec)
      #if no_ideals % 10 == 0
      #  println("done $no_ideals ideals so far...")
      #  x = Base.gc_num()
      #  println("alloc $(x.malloc)   free $(x.freed)  diff: $(x.malloc - x.freed)")
      #  gc_enable(true)
      #  gc()
      #  gc_enable(false)
      #  x = Base.gc_num()
      #  println("alloc $(x.malloc)   free $(x.freed)  diff: $(x.malloc - x.freed)")
      #end
      #println("to be more precise: $k")
    end
    p = next_prime(p)
  end
  if Threads.nthreads() == 1
    @v_do :ClassGroupProof begin
      PB.current = 1.0
      showprogress(stdout, PB, " (ETA: 00:00:00)" * " "^(max(length_eta - 15, 0)))
      println()
    end
  end
  #println("success: used $no_primes numbers and $no_ideals ideals")
  #gc_enable(true)
end

################################################################################
#
#  Unit group verification
#
################################################################################

function _unit_group_proof(U::UnitGrpCtx, primes_checked)
  if !U.GRH
    return true
  end
  O = order(U)
  tent_reg = tentative_regulator(U)
  low_reg = lower_regulator_bound(Hecke.nf(O))
  #low_reg = 14.3648167022986622831389045132
  @vprintln :ClassGroupProof "Lower regulator bound: $(low_reg)"
  fl, regindexbound = unique_integer(floor(tent_reg/low_reg))
  @vprintln :ClassGroupProof "Making unit group p-maximal for up to $(regindexbound)"
  PB = MiniProgressBar(header = "Unit group proof")
  _no_of_primes = logarithmic_integral(Float64(regindexbound)) - logarithmic_integral(Float64(2))
  #gc_enable(false)
  rate = 0.0
  length_eta = 0
  if _no_of_primes < 1000
    interval = 10
  else
    interval = 1000
  end

  no_primes = 0

  for p in PrimesSet(1, Int(regindexbound))

    @v_do :ClassGroupProof begin
      no_primes += 1
      last_time = PB.time_shown
      cur_time = time()
      prev = PB.prev
      PB.current = min(no_primes/_no_of_primes, 1.0)
      # from PB.current to prev it took cur_time - last_time seconds

      if rate == 0.0
        rate = ((PB.current - PB.prev)/(cur_time - last_time))
      else
        rate = (((PB.current - PB.prev)/(cur_time - last_time)) + rate)/2
      end

      duration = (1 - PB.current)/rate

      duration = round(Int, duration)
      ETA = " (ETA: $(Dates.Time(Dates.Nanosecond(duration * 10^9))))"
      if length(ETA) < length_eta
        ETA = ETA * " "^(length_eta - length(ETA))
      else
        length_eta = length(ETA)
      end

      showprogress(stdout, PB, ETA)
      flush(stdout)
    end

    primes_checked isa Vector && p in primes_checked && continue
    if _is_definitely_saturated(U, p)
      continue
    end
    # not maximal, saturate
    while saturate!(U, Int(p), 3.5)
    end

  end
  U.GRH = false

  @v_do :ClassGroupProof begin
    PB.current = 1.0
    showprogress(stdout, PB, " (ETA: 00:00:00)" * " "^(max(length_eta - 15, 0)))
    println()
  end

  return true
end

function _is_definitely_saturated(U::UnitGrpCtx, p)
  return __is_definitely_saturated(order(U), U.units, p)
end

function __is_definitely_saturated(O, units::Vector, p)
  return __is_definitely_saturated_default(units, p)
end

# this is the new function, but it needs tuning
function __is_definitely_saturated_new(O, units::Vector, p)
  if is_ramified(O, p)
    return __is_definitely_saturated_default(units, p)
  end
  try
    fl, = pRational._schirokauer_map_data_generic(base_ring(units[1]), units, p; OK = O)
    return fl
  catch e
    if !(e isa ErrorException && (e.msg == "Problem in the FLINT-Subsystem" || e.msg == "Impossible inverse in invmod"))
      rethrow(e)
    end
    return __is_definitely_saturated_default(units, p)
  end
end

function __is_definitely_saturated_default(units, p)
  return 0 == nrows(RelSaturate.compute_candidates_for_saturate(units, Int(p), 3.5))
end

module VerifyUnitGroup

using ..Hecke

import Hecke:
  _base_ring

import ..Hecke.pRationalCyclotomic:
  _pick_automorphisms

import ..Hecke.pRational:
  _schirokauer_map_data_minkowski_unit,
  _schirokauer_map_data_generic

struct VerifyContext
  K::AbsSimpleNumField
  OK::AbsSimpleNumFieldOrder
  units::Vector{AbsSimpleNumFieldElem} #= fundamental units =#
  units_fac::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}} #= as factored elements =#
  u::AbsSimpleNumFieldElem #= Minkowski unit =#
  is_normal::Bool
  is_cyclic::Bool
  auts::Vector{NumFieldHom{AbsSimpleNumField, AbsSimpleNumField, Hecke.MapDataFromAnticNumberField{AbsSimpleNumFieldElem}, Hecke.MapDataFromAnticNumberField{AbsSimpleNumFieldElem}, AbsSimpleNumFieldElem}}
  auts_gen::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField, Hecke.MapDataFromAnticNumberField{AbsSimpleNumFieldElem}, Hecke.MapDataFromAnticNumberField{AbsSimpleNumFieldElem}, AbsSimpleNumFieldElem}
  t::Int # torsion units order #
  tent_reg::ArbFieldElem
  exp::ZZRingElem
  contains_subfield_units::Bool
end

#function initialize_verify_context(OK::AbsSimpleNumFieldOrder, units::Vector{AbsSimpleNumFieldElem}; test_normality::Bool = true)
#end


function initialize_verify_context(OK::AbsSimpleNumFieldOrder; test_normality::Bool = true, evaluate_elements::Bool = true)
  K = Hecke.nf(OK)
  OK = lll(maximal_order(K))
  U, mU = unit_group_fac_elem(maximal_order(K); GRH = true)
  if evaluate_elements
    units_fac = [FacElem(evaluate(mU(U[i]))) for i in 2:ngens(U)]
  else
    units_fac = [mU(U[i]) for i in 2:ngens(U)]
  end
  return initialize_verify_context(units_fac; test_normality, evaluate_elements = false)
end

function initialize_verify_context(units_fac::Vector{AbsSimpleNumFieldElem}; test_normality::Bool = true, evaluate_elements::Bool = true)
  return initialize_verify_context(FacElem.(units_fac); test_normality, evaluate_elements)
end

function initialize_verify_context(units_fac::Vector{AbsSimpleNumFieldOrderElem}; test_normality::Bool = true, evaluate_elements::Bool = true)
  return initialize_verify_context(elem_in_nf.(units_fac); test_normality, evaluate_elements)
end

function initialize_verify_context(units_fac::Vector{<:FacElem}; test_normality::Bool = true, evaluate_elements::Bool = true)
  if evaluate_elements
    units_fac = FacElem.(evaluate.(units_fac))
  end
  OK = lll(maximal_order(_base_ring(units_fac[1])))
  K = Hecke.nf(OK)
  t = torsion_units_order(K)
  u = zero(K)
  _is_normal = false
  _is_cyclic = false
  auts = Vector{NumFieldHom{AbsSimpleNumField, AbsSimpleNumField, Hecke.MapDataFromAnticNumberField{AbsSimpleNumFieldElem}, Hecke.MapDataFromAnticNumberField{AbsSimpleNumFieldElem}, AbsSimpleNumFieldElem}}()
  auts_gen = id_hom(K)
  exp = ZZ(0)
  contains_subfield_units = false
  if test_normality && is_normal(K)
    G, mG = automorphism_group(K)
    exp = exponent(G)
    auts =  _pick_automorphisms(K)
    _is_normal = true
    if is_cyclic(G)
      _is_cyclic = true
      g = G[rand(1:order(G))]
      while order(g) != order(G)
        g = G[rand(1:order(G))]
      end
      auts_gen = mG(g)
    end
    # now find a Minkowski unit
    for i in 1:length(units_fac)
      fl, = Hecke._isindependent([a(units_fac[i]) for a in auts])
      if fl
        u = evaluate(units_fac[i])
        break
      end
    end
    if is_zero(u)
      # not found yet
      k = 0
      uu = K(mU(U(rand(0:1, ngens(U)))))
      while !(Hecke._isindependent([a(uu) for a in auts]))
        k += 1
        uu = K(mU(rand(U, 2)))
        if k > 100
          error("something wrong")
        end
      end
      u = evaluate(uu)
    end
  end
  return VerifyContext(K, OK, elem_type(K)[], units_fac, u, _is_normal, _is_cyclic, auts, auts_gen, t, regulator(units_fac), exp, contains_subfield_units)
end

function _is_definitely_saturated(C::VerifyContext, p; strategy = :schirokauer)
  if strategy == :gw
    return Hecke.__is_definitely_saturated_default(C.units_fac, p)
  end

  if is_ramified(C.OK, p) || is_divisible_by(C.t, p)
    return Hecke.__is_definitely_saturated_default(C.units_fac, p)
  end
  if C.is_normal
    fl = try
        fl, _ =  _schirokauer_map_data_minkowski_unit(C.K, C.u, p, C.auts; new = true)
        fl
      catch e
        if !(e isa ErrorException && (e.msg == "Problem in the FLINT-Subsystem" || e.msg == "Impossible inverse in invmod"))
          rethrow(e)
        end
        false
    end
    if fl
      return true
    end
  end
  # try the generic
  fl = try
    fl, _ = _schirokauer_map_data_generic(C.K, C.units_fac, p; OK = C.OK)
    fl
  catch e
    if !(e isa ErrorException && (e.msg == "Problem in the FLINT-Subsystem" || e.msg == "Impossible inverse in invmod"))
      rethrow(e)
    end
    false
  end
  if fl
    return true
  end
  if !fl
    return Hecke.__is_definitely_saturated_default(C.units_fac, p)
  end
end

function Hecke.__is_definitely_saturated_default(units::Vector{<:FacElem}, p)
  return 0 == nrows(Hecke.RelSaturate.compute_candidates_for_saturate(units, Int(p), 7.5))
end

function verify_maximlity_up_to(U::Vector, B::Int; strategy = :schirokauer)
  C = initialize_verify_context(U; test_normality = true, evaluate_elements = true)
  verify_maximlity_up_to(C, B; strategy)
end

function verify_maximlity_up_to(C::VerifyContext, B::Int; strategy = :schirokauer)
  for p in PrimesSet(2, B)
    if !_is_definitely_saturated(C, p; strategy)
      @info p
      error("Asds")
    end
  end
  return true
end

function verify_lower_regulator_bound(C::VerifyContext, r::Float64; strategy = :schirokauer)
  ub = Int(Hecke.upper_bound(ZZRingElem, C.tent_reg / r))
  t = @elapsed verify_maximlity_up_to(C, ub; strategy)
  return t
end

end
