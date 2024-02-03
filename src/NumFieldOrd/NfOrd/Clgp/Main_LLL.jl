################################################################################
# same with LLL
################################################################################

function single_env(c::ClassGrpCtx{T}, I::Hecke.SmallLLLRelationsCtx, rat::Float64, max_good::Int = 2) where {T}
  bad_norm = 0
  rk = rank(c.M)
  good = 0
  O = order(c)
  K = nf(O)
  while true
    e = class_group_small_lll_elements_relation_next(I)
    n = norm(e, c.normCtx, norm(I.A))
    if I.cnt > length(I.b)^2
      break
    end
    if n === nothing
      #@show "BadNorm"
      bad_norm += 1
      if I.cnt > 100  && bad_norm / I.cnt > 0.1
        @vprintln :ClassGroup 2 "norm too large, $(I.cnt)"
        break
      end
      continue
    end
    bef = length(c.M.bas_gens) #+ length(c.M.rel_gens)
    fl, r = is_smooth!(c.FB.fb_int, n)
    fl || push_normStat!(c, n, fl)
    fl || (c.bad_rel += 1)
    fl = fl || (r < c.B2 && is_prime(r))
    if fl
      ee = K(O(ZZRingElem[e[1, i] for i=1:degree(K)]))
      fl = class_group_add_relation(c, ee, QQFieldElem(n), norm(I.A), integral = true)
    end
    if !fl  && I.cnt/(good+1) > 2*c.expect
      @vprintln :ClassGroup 2 "not enough progress $(I.cnt) $(c.expect) $good"
      break
    end
    if fl
      good += length(c.M.bas_gens) #= + length(c.M.rel_gens) =# - bef
    end
    if fl && max_good > -1
      if max_good < good
        @vprintln :ClassGroup 2 "found enough $(I.cnt)"
        break
      end
    end
    if false && fl && good > 0 && (rank(c.M)- rk+1)/good < rat
      @vprintln :ClassGroup 2 "rank too slow $(I.cnt) $good $(rank(c.M)) $rk"
      break
    end
  end
  @vprintln :ClassGroup 2 "delta rank: $(rank(c.M) - rk) found $good rels"
  return (rank(c.M) - rk), good
end

function class_group_via_lll(c::ClassGrpCtx{T}, rat::Float64 = 0.2) where {T}
  O = order(c.FB.ideals[1])

  rr1, rr2 = signature(O)
  rt = time_ns()
  I = class_group_small_lll_elements_relation_start(c, O)
  single_env(c, I, rat/10, -1)
  @vprint :ClassGroup 1 "search in order:  $((time_ns()-rt)*1e-9) rel mat:  $(c.M.bas_gens)\nin $(c.M)"

  @vtime :ClassGroup 1 h, piv = class_group_get_pivot_info(c)
  if h == 1 return c; end

#  for p = piv
#    I = class_group_small_lll_elements_relation_start(c, c.FB.ideals[p])
#    single_env(c, I, nb, rat, 1)
#  end
#
#  @vprintln :ClassGroup 1 "search in ideals:  $((time_ns()-rt)*1e-9) rel mat:  $(c.M.bas_gens)"

#  @vtime :ClassGroup 1 h, piv = class_group_get_pivot_info(c)
#  if h == 1 return c; end

#  @vprintln :ClassGroup 1 "Now with random..."
#  @vprintln :ClassGroup 1 "length(piv) = $(length(piv)) and h = $h"
#  @vprintln :ClassGroup 1 "$(piv)"

  #while iszero(h) || length(c.M.rel_gens) < rr1 + rr2 - 1
    class_group_new_relations_via_lll(c, rat, extra = -1)
  #end


  return c
end

function class_group_new_relations_via_lll(c::ClassGrpCtx{T}, rat::Float64 = 0.2; extra::Int = 5, rand_exp::Int = 1) where {T}

  O = order(c.FB.ideals[1])

  st = c.rel_cnt

  @vtime :ClassGroup 1 h, piv = class_group_get_pivot_info(c)

  @vprintln :ClassGroup 1 "Now with random..."
  @vprintln :ClassGroup 1 "length(piv) = $(length(piv)) and h = $h"
  @vprintln :ClassGroup 1 "$(piv)"
  if length(piv) == 0
    for i=1:5
      push!(piv, rand(1:length(c.FB.ideals)))
    end
    @vprintln :ClassGroup 1 "piv was empty, supplemented it to"
    @vprintln :ClassGroup 1 "$(piv)"
  end


  start = max(1, max(div(length(c.FB.ideals), 2)+1, length(c.FB.ideals)-10*(1+div(rand_exp, 3))))
  stop = length(c.FB.ideals)
  if isdefined(c, :randomClsEnv)
    rand_env = c.randomClsEnv
    random_extend(rand_env, 2.0)
    @vprintln :ClassGroup 1 "re-using and extending random: $(nbits(norm(rand_env.rand))) and $(rand_env.exp)"
  else
    @vprintln :ClassGroup 1 "want $(stop-start) primes for random. Try distinct rational primes..."
#    @show start, stop
    JJ = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[c.FB.ideals[stop]]
    start += length(c.FB.ideals) - stop
    stop  += length(c.FB.ideals) - stop
    i = stop
    minimums = ZZRingElem[minimum(x, copy = false) for x = JJ]
    while i>1 && length(JJ) < stop - start
      i -= 1
      if degree(c.FB.ideals[i]) > 1 || minimum(c.FB.ideals[i], copy = false) in minimums
        continue
      end
      push!(JJ, c.FB.ideals[i])
      push!(minimums, minimum(c.FB.ideals[i], copy = false))
    end
    while length(JJ) < stop - start
      AA = rand(c.FB.ideals)
      if !(AA in JJ)
        push!(JJ, AA)
      end
    end
#    @show [ (norm(x), minimum(x)) for x = JJ]
    rand_env = random_init(JJ, lb = isqrt(abs(discriminant(O)))^1, ub = abs(discriminant(O))^1, reduce = false)
    c.randomClsEnv = rand_env
  end

  if h > 0
    rand_exp += 1
    while gcd(h, rand_exp) > 1
      rand_exp += 1
    end
  end

  n_idl = 0
  while true
    st = c.rel_cnt
    while (c.rel_cnt - st < 2)
      sort_rev = rank(c.M) < length(c.FB.ideals) *0.9
      for p = sort(collect(piv), rev = sort_rev)
        @vprint :ClassGroup 1 "$(set_cursor_col())$(clear_to_eol())#ideals tested: $n_idl, pivot ideal: $p, exp: $rand_exp, #rand base: $(length(rand_env.base))"
        @vprintln :ClassGroup 2 "" #otherwise the printing above is horrible
        @vtime :ClassGroup 3 J = random_get(rand_env, reduce = false)
        #@show nbits(norm(J)), rand_env.exp, rand_exp
        @vtime :ClassGroup 3 J *= c.FB.ideals[p]^rand_exp
        @vtime :ClassGroup 3 I = class_group_small_lll_elements_relation_start(c, J)
        n_idl += 1
        @vtime :ClassGroup 3 single_env(c, I, 0.8, length(c.FB.ideals)/rank(c.M) < 2 ? 1 : -1)
        if h == 0 && rank(c.M) == length(c.FB.ideals)
          #reached full rank for the 1st time!!
          h, p = class_group_get_pivot_info(c)
          if h > 0
            break
          end
        end
        if h > 0 && c.rel_cnt - st > 1
          return nothing
        else
          if h == 0 && c.rel_cnt - st > length(piv) + 2
            break
          end
        end
      end
    end

    @vprintln :ClassGroup 1 "eval info"
    @vtime :ClassGroup 1 h, piv_new = class_group_get_pivot_info(c)
    @vprintln :ClassGroup 1 "length(piv) = $(length(piv_new)) and h = $h"
    @vprintln :ClassGroup 1 "$(piv_new)"

    if piv_new == piv
      if h > 0
        extra = 2
#        J = [rand(c.FB.ideals) for x=1:10]
        #println("extending rand")
#        random_extend(rand_env, J)
        random_extend(rand_env, isqrt(abs(discriminant(O))))
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
    if h == 1
      return nothing
    end
  end
end

