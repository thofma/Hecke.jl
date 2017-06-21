function class_group_proof(clg::ClassGrpCtx, lb::fmpz, ub::fmpz; extra :: fmpz=fmpz(0), prec::Int = 100, do_it=1:ub)
  #for all prime ideals P with lb <= norm <= ub, find a relation
  #tying that prime to the factor base
  # if extra is useful, assume that the function was already run for all primes
  # up to norm extra

  if extra==0
    extra = norm(clg.FB.ideals[1])
  end
  lb = max(lb, norm(clg.FB.ideals[1]))
  println("expect to need ", Int(floor(li(ub*1.0) - li(lb*1.0))), " primes")
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
  gc_enable(false)
  while p < do_it.stop
    no_primes += 1
    if no_primes % 100 == 0
      println("did $no_primes prime numbers so far, now $p, need to reach $ub")
    end
    deg_lim = Int(floor(log(ub)/log(p)))
    low_lim = Int(floor(log(lb)/log(p)))
    fac = prime_decomposition(O, Int(p), deg_lim, low_lim)
    for _k in fac
      k = _k[1]
      if norm(k) <= lb 
        continue
      end
      no_ideals += 1
      if no_ideals % 10 == 0
        println("done $no_ideals ideals so far...")
        x = Base.gc_num()
        println("alloc $(x.malloc)   free $(x.freed)  diff: $(x.malloc - x.freed)")
        gc_enable(true)
        gc()
        gc_enable(false)
        x = Base.gc_num()
        println("alloc $(x.malloc)   free $(x.freed)  diff: $(x.malloc - x.freed)")
      end
      #println("to be more precise: $k")
      E = class_group_small_real_elements_relation_start(clg, k, limit=10, prec=prec)
      while true
        sucess = false
        a = class_group_small_real_elements_relation_next(E)
        n = norm_div(a, norm(k), np)
        if gcd(num(n), p) > extra 
          println("a: $a, $(norm(a)), $(norm(k)), $n")
#          println("contains too many conjugates, bad")
          continue
        end
        f, r = issmooth!(clg.FB.fb_int, num(n))
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
  println("success: used $no_primes numbers and $no_ideals ideals")
  gc_enable(true)
end

