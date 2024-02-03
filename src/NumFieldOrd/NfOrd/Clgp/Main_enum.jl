################################################################################
#
#  Naive relation search: Based on coefficient size only
#
################################################################################

function class_group_random_ideal_relation(clg::ClassGrpCtx, r::Int,
                                           I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem} = rand(clg.FB.ideals))
  s = 1
  if r < 2
    r = 2
  end
  for i = 1:r
    I = I*rand(clg.FB.ideals)
    I, g = reduce_ideal_class(I)
    s *= g
  end
  return s;
end

# Do better: re-use partial hnf, check rank mod p, ...

################################################################################
#
#  Relation matrix processing
#
################################################################################

# a large protion is now outsourced to LinearAlgebra/Module.jl

function class_group_process_relmatrix(clg::ClassGrpCtx)

  @vtime_add_elapsed :ClassGroup 1 clg :hnf_time clg.h = check_index(clg.M)
  clg.hnf_call += 1
end

function class_group_get_pivot_info(clg::ClassGrpCtx)
  # Extract information about (missing) pivot elements.
  # If we are in the full rank case, they come from the hnf itself,
  # Otherwise we look at the echelon form of the reduction.

  @vtime_add_elapsed :ClassGroup 1 clg :hnf_time ntp = non_trivial_pivot(clg.M)::BitSet
  @vtime_add_elapsed :ClassGroup 1 clg :hnf_time h = check_index(clg.M)
  clg.h = h
  return (h, ntp)
end

################################################################################
#
#  Main loop to find relations
#
################################################################################

function class_group_find_relations(clg::ClassGrpCtx; val = 0, prec::Int = 100,
                limit::Int = 10)
  clg.hnf_call = 0
  clg.rel_cnt = 0
  clg.bad_rel = 0

  n = degree(clg.FB.ideals[1].parent.order)
  t = time_ns()
  I = []
  O = parent(clg.FB.ideals[1]).order
  sqrt_disc = isqrt(abs(discriminant(O)))
  sqrt_disc = max(sqrt_disc, 1000)
  np = nbits(sqrt_disc)+30

  f = 0

  for i in clg.FB.ideals
    f = class_group_small_real_elements_relation_start(clg, i, limit = limit,
                        prec = prec, val = val)
    push!(I, f)
    f.vl = val
    while true
      e = class_group_small_real_elements_relation_next(I[end])
      n = abs(norm_div(e, norm(I[end].A), np))
#      if n==0 || e==0
##        println("found ", e, " of norm ", n)
#      end
#        print_with_color(:blue, "norm OK:")
#        println(n//norm(I[end].A), " should be ", sqrt_disc)
      if nbits(numerator(n)) > np-10
#        prec = Int(ceil(prec*1.2))
#        print_with_color(:red, "norm too large:")
#        println(n, " should be ", sqrt_disc)
#        println("offending element is ", e)
#        println("offending ideal is ", I[end].A)
#        println("skipping ideal (for now)")
        break
      end
      f = class_group_add_relation(clg, e, n, norm(I[end].A), integral = true)
      if f
        I[end].cnt += 1
        break
      else
        I[end].bad += 1
        if I[end].bad > (clg.bad_rel/clg.rel_cnt)*2
          @v_do :ClassGroup 2 println("too slow in getting s.th. for ", i,
                          "\ngood: ", I[end].cnt,  " bad: ",  I[end].bad,
                          " ratio: ", (clg.bad_rel/clg.rel_cnt))
          break
        end
      end
    end
    @v_do :ClassGroup_gc 1 gc()
    #want 10% more relations than ideals...
    if ncols(clg.M) *1.1 < nrows(clg.M)
      @vprintln :ClassGroup 1 "rel mat probably full rank, leaving phase 1";
      while length(I) < length(clg.FB.ideals)
        push!(I, class_group_small_real_elements_relation_start(clg, clg.FB.ideals[length(I)+1], limit = limit, prec = prec, val = val))
      end
      break
    end
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-t)/1e9,
                  " sec for small elts, so far ", clg.time[:hnf_time]/1e9,
                  " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)

  @v_do :ClassGroup 1 println("total ", nrows(clg.M), " relations (incl. orbit)")

  s = time_ns()

  class_group_process_relmatrix(clg)
  h, piv = class_group_get_pivot_info(clg)

  println("current h=$h")

  idl = clg.FB.ideals
  want_extra = 5
  bad_h = false
  bad_norm = 0
  new_rel = 0
  while h != 1 && (h==0 || want_extra > 0)
    for i in sort([ x for x in piv], lt = >)
      E = I[i]
      lt = max(100, round((clg.bad_rel/clg.rel_cnt)*2))

      while true
        if (E.cnt==0 && E.bad > lt) || (E.cnt != 0 && (bad_h || E.bad > lt))
          @v_do :ClassGroup 2 println("cnt ", E.cnt, " bad ", E.bad, " limit ", lt)
          @v_do :ClassGroup 2 println("re-starting (at ", i, ") ")
          @v_do :ClassGroup 3 println("for ideal ", E.A)

          A = idl[i]
          while norm(A) < sqrt_disc
            A *= rand(idl)
          end
          bad_norm = 0

          I[i] = class_group_small_real_elements_relation_start(clg, A,
                          val = E.vl, limit = limit, prec = prec)
          E = I[i]
        end
        e = class_group_small_real_elements_relation_next(E)
        n = abs(norm_div(e, norm(E.A), np))

        if nbits(numerator(n)) > np-10
          bad_norm += 1
          if bad_norm /(E.cnt + E.bad + 1) > 0.1
#            print_with_color(:red, "too many large norms, changing ideal\n")
#            println("bad_norm: ", bad_norm, " cnt: ", E.cnt, " bad ", E.bad)
            A = idl[i]
            while norm(A) < sqrt_disc
              A *= rand(idl)
            end
            I[i] = class_group_small_real_elements_relation_start(clg, A,
                            val = E.vl, limit = limit, prec = prec)
            E = I[i]
            bad_norm = 0
          end
          #= CF: think careful here
           - norm might be wrong as we did not use enough primes
           - use as large prime variant
           - bad chance for smooth
           lets skip it for now
          =#
          continue;
        end
        if class_group_add_relation(clg, e, n, norm(E.A), orbit = false, integral = true)
          E.cnt += 1
          new_rel += 1
          break
        else
          E.bad += 1
        end
        if  clg.bad_rel - clg.last > 1000000
#          global AllRels = (i, I[i], E)
          error("to bad in finding rel")
        end
      end
      if new_rel > 20
        break
      end
    end
    last_h = h
    l_piv = piv
    new_rel = 0
    class_group_process_relmatrix(clg)
    h, piv = class_group_get_pivot_info(clg)
    println("current h=$h from $(clg.M)")

    if h != 0
      if h==1
        return h, piv
      end
      @v_do :ClassGroup 1 println("full rank: current h = ", h,
                      " want ", want_extra, " more")
      if h == last_h
        want_extra -= 1
      else
        want_extra = 15
      end
    end
    if length(l_piv) - length(piv) < length(l_piv)/2
      bad_h = true
    else
      bad_h = false
    end
    @v_do :ClassGroup_gc 1 gc()
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-s)/1e9, " total so far ",
                  clg.time[:hnf_time]/1e9, " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)

  class_group_process_relmatrix(clg)
  h, piv = class_group_get_pivot_info(clg)

  return h, piv
end

function class_group_find_relations2(clg::ClassGrpCtx; val = 0, prec = 100,
                limit = 10)
  clg.hnf_call = 0
  clg.rel_cnt = 0
  clg.bad_rel = 0

  n = degree(clg.FB.ideals[1].parent.order)
  t = time_ns()
  I = []
  O = parent(clg.FB.ideals[1]).order
  sqrt_disc = isqrt(abs(discriminant(O)))
  sqrt_disc = max(sqrt_disc, 1000)
  np = nbits(sqrt_disc)+30

  local f

  old_r = rank(clg.M)
#  println("starting with $old_r in rank increase")

  nI = length(clg.FB.ideals)
  Idl = clg.FB.ideals
  for i in nI:-1:1
    I = Idl[i]
    too_slow = false
    f = class_group_small_real_elements_relation_start(clg, I,
                                       limit = limit, prec = prec, val = val)

    f.vl = val
    while true
      e = class_group_small_real_elements_relation_next(f)
      n = abs(norm_div(e, norm(f.A), np))
      if nbits(numerator(n)) > np-10 || f.restart > 0
#        print_with_color(:red, "norm too large or restarting: $(f.restart)")
#        println(n, " should be ", sqrt_disc)
#        println("offending element is ", e)
#        println("skipping ideal (for now)")
        break
      end
      fl = class_group_add_relation(clg, e, n, norm(f.A), orbit = false)
      if fl
        f.cnt += 1
        if f.cnt % 20 == 0
          a = rank(clg.M)
          if (a-old_r) < 0.5
            @v_do :ClassGroup 2 println("rank too slow $a ($old_r) and $(clg.rel_mat_full_rank)")
            too_slow = true
            break
          end
          old_r = a
        else
          break
        end
      else
        f.bad += 1
        if clg.bad_rel > clg.rel_cnt && f.bad > max(10, (clg.bad_rel/clg.rel_cnt)*2)
          @v_do :ClassGroup 2 println("too slow in getting s.th. for ", i,
                          "\ngood: ", f.cnt,  " bad: ",  f.bad,
                          " ratio: ", (clg.bad_rel/clg.rel_cnt))
          too_slow = true
          break
        end
      end
    end
    @v_do :ClassGroup_gc 1 gc()
    if too_slow
      break
    end
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-t)/1e9,
                  " sec for small elts, so far ", clg.time[:hnf_time]/1e9,
                  " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)

  s = time_ns()

  h, piv = class_group_get_pivot_info(clg)

  @vprintln :ClassGroup 1 "Target rank: $(length(clg.FB.ideals))\nCurrent rank: $(rank(clg.M))\nTentative class number: $(h)"

  want_extra = 5
  bad_h = false
  no_rand = 1
  a_old = rank(clg.M)
  while h != 1 && (h==0 || want_extra > 0)
    for i in sort([ x for x in piv], lt = >)
      I = Idl[i]
      lt = max(100, round((clg.bad_rel/clg.rel_cnt)*2))

      while true
        A = Idl[i]
        j = 0
        while j < no_rand #  && norm(A) < sqrt_disc
          A *= rand(Idl)
          j += 1
        end
        bad_norm = 0
#        println("using ideal of norm $(norm(A)) no_rand $no_rand")

        E = 0
        E = class_group_small_real_elements_relation_start(clg, A,
                        val = val, limit = limit, prec = prec)
        no_rand_local = no_rand
        while true
          e = class_group_small_real_elements_relation_next(E)
          n = abs(norm_div(e, norm(E.A), np))
          if nbits(numerator(n)) > np-10 || E.restart > 5
#            @v_do :ClassGroup 2 begin
#              print_with_color(:red, "2:norm too large (or restarting):")
#              println(n, " should be ", sqrt_disc)
#              println("offending element is ", e)
#              println("prec now ", prec)
#            end
            A = Idl[i]
            j = 0
            # TH: without added no_rand_local < nI it crashes sometimes
            #     but I don't know what I am doing
            while norm(A) < sqrt_disc && j < no_rand_local && no_rand_local < nI
              A *= rand(Idl[(nI-no_rand_local):nI])
              j += 1
            end
            no_rand_local = min(nI-1, no_rand_local+1)
#            println("using ideal $A of norm $(norm(A))")
            E = class_group_small_real_elements_relation_start(clg, A,
                            val = E.vl, limit = limit, prec = prec)
            #= CF: think careful here
             - norm might be wrong as we did not use enough primes
             - use as large prime variant
             - bad chance for smooth
             lets skip it for now
            =#
            continue;
          end
          if class_group_add_relation(clg, e, n, norm(E.A))
            E.cnt += 1
            #print_with_color(:green, "success\n")
            break
            if length(clg.RS) % 20 == 0
              #print_with_color(:blue, "found rels, trying again\n")
            end
          else
            E.bad += 1
          end
        end
        if length(clg.RS) % 20 == 0 # ncols(clg.M)*0.1
#          print_with_color(:blue, "2:found rels, trying again\n")
          break
        end
      end
      if length(clg.RS) % 20  == 0# ncols(clg.M)*0.1
#        print_with_color(:blue, "3:found rels, trying again\n")
        break
      end
    end
    last_h = h
    l_piv = piv
    last_rank = rank(clg.M)
    class_group_process_relmatrix(clg)
    a = rank(clg.M)
#    println("rank increase gave $a was $a_old")
    h, piv = class_group_get_pivot_info(clg)
    if (a-a_old) < 0.5 * clg.bad_rel/(length(clg.RS) + clg.bad_rel)
      no_rand += 5
      no_rand = min(no_rand, length(clg.FB.ideals))
      no_rand = min(no_rand, Int(floor(length(clg.FB.ideals)*0.1)))
    end
    a_old = a
    if h != 0
      if h==1
        return h, piv
      end
      @vprintln :ClassGroup 1 "Now have $(clg.M)"
      @vprintln :ClassGroup 1 "full rank: current h = $(h) want $(want_extra) more"
      if h == last_h
        want_extra -= 1
      else
        want_extra = 15
      end
    end
    if length(l_piv) - length(piv) < length(l_piv)/2
      bad_h = true
    else
      bad_h = false
    end
    @v_do :ClassGroup_gc 1 gc()
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-s)/1e9, " total so far ",
                  clg.time[:hnf_time]/1e9, " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)
  class_group_process_relmatrix(clg)
  h, piv = class_group_get_pivot_info(clg)
end

# add one/ a few more relations

function class_group_find_new_relation(clg::ClassGrpCtx; val = 0, prec = 100,
                limit = 10, extra = 1)
  if !isdefined(clg, :randomClsEnv)
    clg.randomClsEnv = random_init(clg.FB.ideals)
  end

  O = parent(clg.FB.ideals[1]).order
  sqrt_disc = isqrt(abs(discriminant(O)))
  sqrt_disc = max(sqrt_disc, 1000)
  np = nbits(sqrt_disc)+30

  rat = max(clg.bad_rel/clg.rel_cnt, 20.0)

  while true
    I = random_get(clg.randomClsEnv)
#    println("trying in ideal $I");
    E = class_group_small_real_elements_relation_start(clg, I,
                            val = val, limit = limit, prec = prec)

    while true
      e = class_group_small_real_elements_relation_next(E)
      n = abs(norm_div(e, norm(E.A), np))
      if nbits(numerator(n)) > np-10 || E.restart > 2
        break;
      end
      if class_group_add_relation(clg, e, n, norm(E.A))
        E.cnt += 1
        extra -= 1
        if extra <= 0
          return
        end
      else
        E.bad += 1
        if E.bad > rat
          break
        end
      end
    end
  end
  class_group_process_relmatrix(clg)
end


