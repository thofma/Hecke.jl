# Import the progress bar and Dates for the conversion of seconds
import Dates

add_verbose_scope(:ClassGroupProof)

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


function class_group_proof(clg::ClassGrpCtx, lb::fmpz, ub::fmpz; extra :: fmpz=fmpz(0), prec::Int = 100, do_it=1:ub)
  PB = MiniProgressBar(header = "Class group proof")

  #for all prime ideals P with lb <= norm <= ub, find a relation
  #tying that prime to the factor base
  # if extra is useful, assume that the function was already run for all primes
  # up to norm extra

  if extra == 0
    extra = norm(clg.FB.ideals[1])
  end
  lb = max(lb, norm(clg.FB.ideals[1]))
  #println("expect to need ", Int(floor(li(ub*1.0) - li(lb*1.0))), " primes")
  O = order(clg.FB.ideals[1])
  n = degree(O)
  p = next_prime(root(lb, n))
  np = Int(floor(log(abs(discriminant(O)))/log(2)/2))
  no_primes = 0
  no_ideals = 0
  if do_it.start > 1
    p = fmpz(next_prime(do_it.start))
  end
  r = fmpz()
  _no_of_primes = logarithmic_integral(Float64(ub)) - logarithmic_integral(Float64(lb))
  #gc_enable(false)
  rate = 0.0
  length_eta = 0
  if _no_of_primes < 1000
    interval = 10
  else
    interval = 1000
  end

  while p < do_it.stop
    no_primes += 1

    @v_do :ClassGroupProof if no_primes % interval == 0
      #println("did $no_primes prime numbers so far, now $p, need to reach $ub (~$(no_primes/_no_of_primes))")
      last_time = PB.time_shown
      cur_time = time()
      prev = PB.prev
      PB.current = no_primes/_no_of_primes
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
      E = class_group_small_real_elements_relation_start(clg, k, limit=10, prec=prec)
      while true
        sucess = false
        a = class_group_small_real_elements_relation_next(E)
        n = norm_div(a, norm(k), np)
        if gcd(numerator(n), p) > extra
#          println("a: $a, $(norm(a)), $(norm(k)), $n")
#          println("contains too many conjugates, bad")
          continue
        end
        f, r = is_smooth!(clg.FB.fb_int, numerator(n))
        if f
          M = SMat{Int}()
          fl = _factor!(clg.FB, a, false, n)[1]
          if fl
            break
          else
#            println("not smooth, ideal")
          end
        else
#          println("not smooth, int")
        end
      end
    end
    p = next_prime(p)
  end
  @v_do :ClassGroupProof begin
    PB.current = 1.0
    showprogress(stdout, PB, " (ETA: 00:00:00)" * " "^(max(length_eta - 15, 0)))
    println()
  end
  #println("success: used $no_primes numbers and $no_ideals ideals")
  #gc_enable(true)
end

