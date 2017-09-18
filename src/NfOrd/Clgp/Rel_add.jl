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
function special_prime_ideal(p::fmpz, a::nf_elem)
  K = parent(a)
  f = K.pol
  R = parent(f)
  Zx = PolynomialRing(FlintZZ)[1]
  Zpx = PolynomialRing(ResidueRing(FlintZZ, p, cached=false), "\$x_p", cached=false)[1]
  g = Zpx(a)  
  ff = Zpx(f)
  gcd!(g, g, ff)
  return lift(Zx, g)
end

function class_group_add_relation(clg::ClassGrpCtx{T}, a::nf_elem; orbit::Bool = true, integral::Bool = false) where T
  return class_group_add_relation(clg, a, norm(a), fmpz(1), orbit = orbit, integral = integral)
end

#deal with integral and non-integral elements differently. Computing the order
#denominator is expensive (and mostly unnecessary)
function class_group_add_relation(clg::ClassGrpCtx{T}, a::nf_elem, n::fmpq, nI::fmpz; orbit::Bool = true, integral::Bool = true) where T
  if iszero(a)
    return false
  end
  if a in clg.RS 
    return false
  end

  nb = div(nbits(num(n)), 2)
  if haskey(clg.normStat, nb)
    clg.normStat[nb] += 1
  else
    clg.normStat[nb] = 1
  end
  
  O = order(clg.FB.ideals[1]) 
  @vprint :ClassGroup 3 "trying relation of length $(Float64(length(a))) and norm $(Float64(n*nI)), effective $(Float64(n))\n"
  if integral #element is known to be integral
    fl, r = issmooth!(clg.FB.fb_int, num(n*nI))
  else  
    fl, r = issmooth!(clg.FB.fb_int, num(n*nI)*den(a, O))
  end  
  if !fl
    @vprint :ClassGroup 3 "not int-smooth\n"
#    println("not int-smooth");
    # try for large prime?
    if abs(r) < clg.B2 && isprime(r) && !isindex_divisor(O, r) 
      @vprint :ClassGroup 3 "gives potential large prime\n"
      i = special_prime_ideal(r, a)
      #TODO: check Galois orbit of special ideal
      if haskey(clg.largePrime, i)
        lp = clg.largePrime[i]
        b = a//lp[1]
        fl = class_group_add_relation(clg, b, n*nI//lp[2], fmpz(1), integral = false)
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
    if add_gen!(clg.M, res)
      push!(clg.R_gen, a)
    else
      push!(clg.R_rel, a)
    end
    push!(clg.RS, a)
    if orbit && isdefined(clg, :aut_grp)
      n = res
      o = clg.aut_grp
      function op_smat(n::SRow, p::Nemo.Generic.perm)
        r = [(p[i], v) for (i,v) = n]
        sort!(r, lt = (a,b)->a[1]<b[1])
        return typeof(n)(r)
      end

      @v_do :ClassGroup 1 println(" adding orbit with $(length(o)) elements")
      for (b, m) in o
        nn = op_smat(n, m)
        if nn != n
          ba = b(a)
          if add_gen!(clg.M, nn)
            push!(clg.R_gen, ba)
          else
            push!(clg.R_rel, ba)
          end
          push!(clg.RS, ba)
        end
      end
    end  

    clg.rel_cnt += 1
#    @assert clg.rel_cnt < 2*cols(clg.M)
    @v_do :ClassGroup 1 println(" -> OK, rate currently ",
           clg.bad_rel/clg.rel_cnt, " this ", clg.bad_rel - clg.last)
    clg.last = clg.bad_rel
    return true
  else
    @vprint :ClassGroup 3 "not alg-smooth\n"
    clg.bad_rel += 1
    return false
  end
end

