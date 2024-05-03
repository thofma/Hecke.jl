#=
  should probably just use an integer as hash: p*root of poly

  so a is an integral element where the norm is almost smooth, it means
  norm(a) = prod over factor base * p
  where p is a prime.
  This means
  <p, a> is a prime ideal of norm p hence of degree 1
  if p is no index divisor, then <p,a> = <p, b> where
  b is a linear factor of f, the defining polynomial, mod p.
  I can compute b as gcd(a, f) of course.
  =#
function special_prime_ideal(p::ZZRingElem, a::AbsSimpleNumFieldElem)
  K = parent(a)
  f = K.pol
  R = parent(f)
  Zx = polynomial_ring(FlintZZ)[1]
  Zpx = polynomial_ring(Native.GF(UInt(p), cached=false), "\$x_p", cached=false)[1]
  g = Zpx(a)
  ff = Zpx(f)
  gcd!(g, g, ff)
  return lift(Zx, g)
end

function push_normStat!(clg::ClassGrpCtx, n::ZZRingElem, b::Bool)
  nb = nbits(abs(n))
  if !haskey(clg.normStat, nb)
    clg.normStat[nb] = (0,0)
  end
  t = clg.normStat[nb]
  if b
    clg.normStat[nb] = (t[1], t[2] + 1)
  else
    clg.normStat[nb] = (t[1] + 1, t[2])
  end
end

function class_group_add_relation(clg::ClassGrpCtx{T}, a::AbsSimpleNumFieldElem; orbit::Bool = true, integral::Bool = false) where T
  return class_group_add_relation(clg, a, norm(a), ZZRingElem(1), orbit = orbit, integral = integral)
end

#deal with integral and non-integral elements differently. Computing the order
#denominator is expensive (and mostly unnecessary)
function class_group_add_relation(clg::ClassGrpCtx{T}, a::AbsSimpleNumFieldElem, n::QQFieldElem, nI::ZZRingElem; orbit::Bool = true, integral::Bool = true, always::Bool = true) where T
  if hash(a) in clg.RS
    return false
  end

  O = order(clg.FB.ideals[1])
  easy = is_defining_polynomial_nice(parent(a))
  @vprintln :ClassGroup 3 "trying relation of length $(Float64(length(a))) and norm $(Float64(n*nI)), effective $(Float64(n))"
  if integral #element is known to be integral
    fl, r = is_smooth!(clg.FB.fb_int, numerator(n*nI))
    push_normStat!(clg, numerator(n), fl)
  else
    fl, r = is_smooth!(clg.FB.fb_int, numerator(n*nI)*denominator(a, O))
    push_normStat!(clg, numerator(n)*denominator(a), fl)
  end
  @assert is_smooth!(clg.FB.fb_int, nI)[1]


  if !fl
    @vprintln :ClassGroup 3 "not int-smooth"
#    println("not int-smooth");
    # try for large prime?
    if easy && abs(r) < clg.B2 && is_prime(r) && !is_index_divisor(O, r)
      @vprintln :ClassGroup 3 "gives potential large prime"
      i = special_prime_ideal(r, a)
      #TODO: check Galois orbit of special ideal
      if haskey(clg.largePrime, (r, i))
        lp = clg.largePrime[(r, i)]
        fl, r1 = _factor!(clg.FB, a, false, n*nI)
        fl, r2 = _factor!(clg.FB, lp[1], false, norm(lp[1]))
        b = FacElem(Dict([(a,1), (lp[1],-1)]))
        fl = class_group_add_relation(clg, b, r1 - r2)
        if fl
          clg.largePrime_success += 1
        else
          clg.largePrime_no_success += 1
        end
      else
        clg.largePrime[i] = (a, n*nI)
      end
      clg.largePrimeCnt += 1
    else
      clg.bad_rel += 1
    end
    #println(" -> fail")
    return false
  end
  fl, res = _factor!(clg.FB, a, false, n*nI, integral)
  if fl
    if res in clg.M.rel_gens || res in clg.M.bas_gens
      return false
    end
    @vprintln :ClassGroup 3 "adding $res"
    new_gen = add_gen!(clg.M, res, always)
    if always
      if new_gen
        push!(clg.R_gen, a)
      else
        push!(clg.R_rel, a)
      end
      clg.rel_cnt += 1
      push!(clg.RS, hash(a))
    else
      if new_gen
        push!(clg.R_gen, a)
        push!(clg.RS, hash(a))
        clg.rel_cnt += 1
      end
    end

    if new_gen && orbit && isdefined(clg, :aut_grp)
      n = res
      o = _get_autos_from_ctx(clg)

      @v_do :ClassGroup 1 println(" adding orbit with $(length(o)) elements")
      for (b, m) in o
        nn = Hecke.permute_row(n, m)
        if nn != n
          if nn in clg.M.bas_gens || nn in clg.M.rel_gens
            break
          end
          if add_gen!(clg.M, nn, false)
            ba = b(a)
            push!(clg.R_gen, ba)
            clg.rel_cnt += 1
            push!(clg.RS, hash(ba))
          end
        end
      end
    end


#    @assert clg.rel_cnt < 2*ncols(clg.M)
    @v_do :ClassGroup 1 println(" -> OK, rate currently ",
           clg.bad_rel/clg.rel_cnt, " this ", clg.bad_rel - clg.last,
           " rank now ", rank(clg.M), " of ", length(clg.FB.ideals))
    clg.last = clg.bad_rel
    return true
  else
    @vprintln :ClassGroup 3 "not alg-smooth"
    clg.bad_rel += 1
    return false
  end
end



function class_group_add_relation(clg::ClassGrpCtx{<:SMat{ZZRingElem}}, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
  R = sparse_row(FlintZZ)
  for i = 1:length(clg.FB.ideals)
    p = clg.FB.ideals[i]
    v = valuation(a, p)
    if !iszero(v)
      push!(R.values, v)
      push!(R.pos, i)
    end
  end
  return class_group_add_relation(clg, a, R)
end

function class_group_add_relation(clg::ClassGrpCtx{<:SMat{ZZRingElem}}, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, R::SRow{ZZRingElem}; always::Bool = true, add_orbit = true)

  if hash(a) in clg.RS
    return false
  end

  O = order(clg.FB.ideals[1])

  @vprintln :ClassGroup 3 "adding $R"

  new_gen = add_gen!(clg.M, R, always)
  if always
    if new_gen
      push!(clg.R_gen, a)
    else
      push!(clg.R_rel, a)
    end
    push!(clg.RS, hash(a))
    clg.rel_cnt += 1
  else
    if new_gen
      push!(clg.R_gen, a)
      push!(clg.RS, hash(a))
      clg.rel_cnt += 1
    end
  end

  if add_orbit && isdefined(clg, :aut_grp) && new_gen
    o = _get_autos_from_ctx(clg)
    @v_do :ClassGroup 1 println(" adding orbit with $(length(o)) elements")
    for (b, m) in o
      Rnew = permute_row(R, m)
      if Rnew != R
        if Rnew in clg.M.bas_gens || Rnew in clg.M.rel_gens
          break
        end
        if add_gen!(clg.M, Rnew, false)
          ba = b(a)
          push!(clg.R_gen, ba)
          clg.rel_cnt += 1
          push!(clg.RS, hash(ba))
        end
      end
    end
  end

  clg.last = clg.bad_rel
  return true
end
