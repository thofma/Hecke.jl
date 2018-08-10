################################################################################
# same with LLL
################################################################################

function single_env{T}(c::ClassGrpCtx{T}, I::Hecke.SmallLLLRelationsCtx, nb::Int, rat::Float64, max_good::Int = 2)
  bad_norm = 0
  rk = rank(c.M)
  good = 0
  while true
    e = class_group_small_lll_elements_relation_next(I)
    n = norm_div(e, norm(I.A), nb)
    if I.cnt > length(I.b)^2
      break
    end
    if nbits(numerator(n)) > nb - 25
      bad_norm += 1
      if I.cnt > 100  && bad_norm / I.cnt > 0.1
        @vprint :ClassGroup 2 "norm too large, $(I.cnt) has size $(nbits(numerator(n))) should be <= $(nb - 20) $bad_norm $(I.cnt)\n"
        break
      end
      continue
    end
    fl = class_group_add_relation(c, e, n, norm(I.A), integral = true)
    if !fl  && I.cnt/(good+1) > 2*c.expect
      @vprint :ClassGroup 2 "not enough progress $(I.cnt) $(c.expect) $good\n"
      break
    end
    if fl 
      good += 1
    end
    if fl && max_good > -1
      if max_good < good
        @vprint :ClassGroup 2 "found enough $(I.cnt)\n"
        break
      end
    end
    if false && fl && good > 0 && (rank(c.M)- rk+1)/good < rat
      @vprint :ClassGroup 2 "rank too slow $(I.cnt) $good $(rank(c.M)) $rk\n"
      break
    end
  end
end

function class_group_via_lll{T}(c::ClassGrpCtx{T}, rat::Float64 = 0.2)
  O = order(c.FB.ideals[1])
  nb = nbits(abs(discriminant(O)))
  nb = div(nb, 2) + 30

  rt = time_ns()
  I = class_group_small_lll_elements_relation_start(c, O)
  single_env(c, I, nb, rat/10, -1)
  @vprint :ClassGroup 1 "search in order:  $((time_ns()-rt)*1e-9) rel mat:  $(c.M.bas_gens)\nin $(c.M)"

  @vtime :ClassGroup 1 h, piv = class_group_get_pivot_info(c)
  if h == 1 return c; end

#  for p = piv
#    I = class_group_small_lll_elements_relation_start(c, c.FB.ideals[p])
#    single_env(c, I, nb, rat, 1)
#  end
#
#  @vprint :ClassGroup 1 "search in ideals:  $((time_ns()-rt)*1e-9) rel mat:  $(c.M.bas_gens)\n"

#  @vtime :ClassGroup 1 h, piv = class_group_get_pivot_info(c)
#  if h == 1 return c; end

#  @vprint :ClassGroup 1 "Now with random...\n"
#  @vprint :ClassGroup 1 "length(piv) = $(length(piv)) and h = $h\n"
#  @vprint :ClassGroup 1 "$(piv)\n"

  class_group_new_relations_via_lll(c, rat, extra = -1)

  return c
end

function class_group_new_relations_via_lll{T}(c::ClassGrpCtx{T}, rat::Float64 = 0.2; extra::Int = 5, rand_exp::Int = 1)

  O = order(c.FB.ideals[1])
  nb = nbits(abs(discriminant(O)))
  nb = div(nb, 2) + 30

  st = c.rel_cnt

  @vtime :ClassGroup 1 h, piv = class_group_get_pivot_info(c)

  @vprint :ClassGroup 1 "Now with random...\n"
  @vprint :ClassGroup 1 "length(piv) = $(length(piv)) and h = $h\n"
  @vprint :ClassGroup 1 "$(piv)\n"
  if length(piv) == 0
    for i=1:5
      push!(piv, rand(1:length(c.FB.ideals)))
    end
    @vprint :ClassGroup 1 "piv was empty, supplemented it to\n"
    @vprint :ClassGroup 1 "$(piv)\n"
  end  


  start = max(1, max(div(length(c.FB.ideals), 2)+1, length(c.FB.ideals)-10*(1+div(rand_exp, 3))))
  stop = length(c.FB.ideals)
  if isdefined(c, :randomClsEnv)
    rand_env = c.randomClsEnv
    random_extend(rand_env, 2.0)
    @vprint :ClassGroup 1 "re-using and extending random: $(nbits(norm(rand_env.rand))) and $(rand_env.exp)\n"
  else
    @vprint :ClassGroup 1 "want $(stop-start) primes for random. Try distinct rational primes...\n"
#    @show start, stop
    JJ = [c.FB.ideals[stop]]
    start += length(c.FB.ideals) - stop
    stop  += length(c.FB.ideals) - stop
    i = stop
    while i>1 && length(JJ) < stop - start
      i -= 1
      if degree(c.FB.ideals[i]) > 1
        continue
      end
      if minimum(c.FB.ideals[i]) in [minimum(x) for x = JJ]
        continue
      else
        push!(JJ, c.FB.ideals[i])
      end
    end
    while length(JJ) < stop - start
      AA = rand(c.FB.ideals)
      if !(AA in JJ)
        push!(JJ, AA)
      end
    end
#    @show [ (norm(x), minimum(x)) for x = JJ]
    rand_env = random_init(JJ, lb = root(abs(discriminant(O)), 2)^1, ub = abs(discriminant(O))^1, reduce = false)
    c.randomClsEnv = rand_env
  end

  if h > 0
    rand_exp += 1
    while gcd(h, rand_exp) > 1
      rand_exp += 1
    end
  end

  while true
    st = c.rel_cnt
    while (c.rel_cnt - st < 2)
      for p = sort(collect(piv), rev = true)
        @vprint :ClassGroup 1 "p: $p $rand_exp $(length(rand_env.base))\n"
        @vtime :ClassGroup 3 J = random_get(rand_env, reduce = false)
  #      @show nbits(norm(J)), rand_env.exp, rand_exp
        @vtime :ClassGroup 3 J *= c.FB.ideals[p]^rand_exp
        @vtime :ClassGroup 3 I = class_group_small_lll_elements_relation_start(c, J)
        @vtime :ClassGroup 3 single_env(c, I, nb, 0.8, -1)
        if h > 0 && c.rel_cnt - st > 2
          return
        else
          if h == 0 && c.rel_cnt - st > length(piv) + 2
            break
          end
        end
      end
    end  

    @vprint :ClassGroup 1 "eval info\n"
    @vtime :ClassGroup 1 h, piv_new = class_group_get_pivot_info(c)
    @vprint :ClassGroup 1 "length(piv) = $(length(piv_new)) and h = $h\n"
    @vprint :ClassGroup 1 "$(piv_new)\n"
    
    if piv_new == piv
      if h > 0
        extra = 5
#        J = [rand(c.FB.ideals) for x=1:10]
#        println("extending rand")
#        random_extend(rand_env, J)
        random_extend(rand_env, root(abs(discriminant(O)), 2))
      end
      rand_exp += 1
      rand_exp = min(rand_exp, 13)
      if h>0
        while gcd(rand_exp, h) > 1
          rand_exp += 1
        end
      end  

      if rand_exp % 3 == 0
        start = max(start -10, 1)
      end
    end
    piv = piv_new
    if h == 1 return end
  end
end

