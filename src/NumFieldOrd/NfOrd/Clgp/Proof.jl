# Import the progress bar and Dates for the conversion of seconds
import Dates

add_verbosity_scope(:ClassGroupProof)

# This is a modified showprogress from Pkg.GitTools

PROGRESS_BAR_PERCENTAGE_GRANULARITY = Ref(0.1)

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
  perc = p.current / p.max * 100
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
  @printf io "%2.1f %%" perc
  print(io, info)
  print(io, "\r")
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

