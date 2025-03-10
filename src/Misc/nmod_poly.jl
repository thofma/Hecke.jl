################################################################################
#
#  Computation of a generator of the ideal of the resultant
#
################################################################################
@doc raw"""
    resultant_ideal(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion -> T

A generator for the ideal of the resultant of $f$ and $g$ using a quadratic-time algorithm.
One of the two polynomials must be monic.
"""
function resultant_ideal(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  #The algorithm is the same as the resultant. We assume that one fo the 2 polynomials is monic. Under this assumption, at every
  #step the same is true and we can discard the unit obtained from the fun_factor function
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = ZZRingElem(modulus(R))

  #easy = is_prime_power(m)
  #if easy
  #  return resultant_ideal_pp(f,g)
  #end

  #Some initial checks
  res = R(1)
  if degree(f) < 1 && degree(g) < 1
    if iszero(f) || iszero(g)
      return R(0)
    end
    return res
  end

  if degree(f) < 1
    res = mul!(res, res, leading_coefficient(f)^degree(g))
    return res
  end

  c, f = primsplit(f)
  if !isone(c)
    res = mul!(res, res, R(c)^degree(g))
  end

  c, g = primsplit(g)
  if !isone(c)
    res = mul!(res, res, R(c)^degree(f))
  end

  if degree(f) < degree(g)
    f, g = g, f
  end

  if iszero(res)
    return res
  end


  #Now, I can safely assume that the degree of f is always greater than the degree of g
  while true

    if degree(g) < 1
      res = mul!(res, res, leading_coefficient(g)^degree(f))
      return res
    end

    c, g = primsplit!(g)
    if !isone(c)
      res = mul!(res, res, R(c)^degree(f))
    end

    if iszero(res)
      return res
    end
    #want f % g which works iff leading_coefficient(g) | leading_coefficient(f)

    if is_unit(leading_coefficient(g)) #accelerate a bit...possibly.
      rem!(f, f, g)
      f, g = g, f
      continue
    end
    break
  end

  # factoring case, need to split the ring as well.
  # we need a coprime factorisation and then we go recursively
  #If res is not coprime to the modulus, I can continue the computations modulo a smaller one.
  s = gcd(m, lift(res))
  if !isone(s)
    m = divexact(m, s)
  end
  cp = ZZRingElem[gcd(lift(coeff(g, i)), m) for i=0:degree(g)]
  push!(cp, m)
  cp = ZZRingElem[x for x = cp if !iszero(x)]
  cp = coprime_base(cp)
  cp = ZZRingElem[x for x = cp if !is_unit(x)] #error: [1, 1, 3, 27] -> [1,3]
  resp = ZZRingElem[]
  pg = ZZRingElem[]
  for p = cp
    lg = p^valuation(m, p)
    push!(pg, lg)
    R1 = residue_ring(ZZ, S(lg), cached = false)[1]
    R1t = polynomial_ring(R1, cached = false)[1]
    #g is bad in R1, so factor it
    gR1 = R1t(T[R1(lift(coeff(g, i))) for i = 0:degree(g)])
    fR1 = R1t(T[R1(lift(coeff(f, i))) for i = 0:degree(f)])

    if degree(fR1) < degree(f) && degree(gR1) < degree(g)
      res1 = R1(0)
    elseif degree(fR1) < degree(f)
      res1 = leading_coefficient(gR1)^(degree(f) - degree(fR1))
    else
      res1 = R1(1)
    end

    if !is_unit(leading_coefficient(gR1))
      g1, g2 = fun_factor(gR1)
      res1 = mul!(res1, res1, resultant_ideal(fR1, g2))
      push!(resp, lift(res1))
    else
      #gR1 has a invertible leading coeff
      res1 = mul!(res1, res1, resultant_ideal(fR1, gR1))
      push!(resp, lift(res1))
    end
  end
  if length(resp) == 1
    res = mul!(res, res, R(resp[1]))
  else
    res = mul!(res, res, R(crt(resp, pg)))
  end
  return res
end


function resultant_ideal_pp(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  #The algorithm is the same as the resultant. We assume that one fo the 2 polynomials is monic. Under this assumption, at every
  #step the same is true and we can discard the unit obtained from the fun_factor function
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  #pn = ZZRingElem(modulus(R))
  pn = modulus(R)

  #Some initial checks
  if degree(f) < 1 && degree(g) < 1
    if iszero(f) || iszero(g)
      return R(0)
    else
      return R(1)
    end
  end

  res = R(1)

  if degree(f) < 1
    res = mul!(res, res, leading_coefficient(f)^degree(g))
    return res
  end

  if degree(g) < 1
    res = mul!(res, res, leading_coefficient(g)^degree(f))
    return res
  end

  c, f = primsplit(f)
  if !isone(c)
    res = mul!(res, res, c^degree(g))
  end

  c, g = primsplit(g)
  if !isone(c)
    res = mul!(res, res, c^degree(f))
  end

  if degree(f) < degree(g)
    f, g = g, f
  end

  if iszero(res)
    return res
  end

  while true
    #want f % g which works iff leading_coefficient(g) | leading_coefficient(f)

    if is_unit(leading_coefficient(g)) #accelerate a bit...possibly.
      rem!(f, f, g)
      if degree(f) < 1
        res = mul!(res, res, leading_coefficient(f)^degree(g))
        return res
      end
      c, f = primsplit!(f)
      if !isone(c)
        res = mul!(res, res, c^degree(g))
      end
      f, g = g, f
    else
      s = gcd(lift(res), pn)
      if !isone(s)
        new_pn = divexact(pn, s)
        if is_one(new_pn)
          return zero(R)
        end
        R1 = residue_ring(ZZ, S(new_pn), cached = false)[1]
        R1t = polynomial_ring(R1, "y", cached = false)[1]
        f2 = R1t(T[R1(lift(coeff(f, i))) for i = 0:degree(f)])
        g2 = R1t(T[R1(lift(coeff(g, i))) for i = 0:degree(g)])
        g2 = fun_factor(g2)[2]
        z = resultant_ideal_pp(f2, g2)
        return mul!(res, res, R(lift(z)))
      end
      g = fun_factor(g)[2]
      if degree(g) < 1
        res = mul!(res, res, leading_coefficient(g)^degree(f))
        return res
      end
    end
  end

end

################################################################################
#
#  Extended gcd
#
################################################################################

@doc raw"""
    xxgcd(a::ResElem{ZZRingElem}, b::ResElem{ZZRingElem}) -> g, e, f, u, v
    xxgcd(a::ResElem{Integer}, b::ResElem{Integer}) -> g, e, f, u, v

Computes $g = \gcd(a, b)$, the Bezout coefficients, $e$, $f$ s.th.
$g = ea+fb$ and $u$, $v$ s.th. $ev-fu = 1$, $gu = a$ and $gv = b$.
"""
function xxgcd(a::ResElem{S}, b::ResElem{S}) where S <: IntegerUnion
  g, e, f = gcdx(a, b)
  if iszero(g)
    return g, e, f, f, e
  else
    return g, e, f, divexact(a, g), divexact(b, g)
  end
end


#for testing: the obvious(?) naive method(s)
function rres_hnf(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  R = base_ring(f)
  Zx = polynomial_ring(ZZ, "x", cached = false)[1]
  s = Nemo.Generic.sylvester_matrix(lift(Zx, f), lift(Zx, g))
  h = hnf(s)
  return gcd(R(0), R(h[nrows(h), ncols(h)]))
end

function rres_bez(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  R = base_ring(f)
  Zx = polynomial_ring(ZZ, "x", cached = false)[1]
  Qx = polynomial_ring(QQ, "x", cached = false)[1]
  g, q, w = gcdx(Qx(lift(Zx, f)), Qx(lift(Zx, g)))
  return gcd(R(0), R(lcm(denominator(q), denominator(w))))
end


#polynomial remainder sequence - almost
#=
function prs_sircana(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion

  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = ZZRingElem(modulus(R))
  e, p = is_perfect_power_with_data(m)
  easy = is_prime(p)
  @assert easy

  Zx = polynomial_ring(ZZ, cached = false)[1]

  rs = []

  while degree(g) >0
    g *= inv(canonical_unit(leading_coefficient(g)))
    c, gg = primsplit(g)
    @show f, (g, mu) = gg, my_divrem(f, gg)
    push!(rs, (c, gg, mu))
  end
  return rs, g
end
=#


@doc raw"""
    annihilator(a::ResElem{ZZRingElem}) -> r
    annihilator(a::ResElem{Integer}) -> r

The annihilator of $a$, i.e. a generator for the annihilator ideal
$\{x | xa = 0\} = \langle r\rangle$.
"""
function annihilator(a::ResElem{T}) where T <: IntegerUnion
  R = parent(a)
  m = modulus(R)
  return R(divexact(m, gcd(m, a.data)))
end

function is_zerodivisor(f::T) where T <: Union{ZZModPolyRingElem,zzModPolyRingElem}
  c = content(f)
  return is_nilpotent(c)
end

function rres_sircana_pp(f1::PolyRingElem{T}, g1::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f1, g1)
  @assert typeof(f1) == typeof(g1)
  Rt = parent(f1)
  R = base_ring(Rt)
  m = ZZRingElem(modulus(R))
  e, p = is_perfect_power_with_data(m)
  f = deepcopy(f1)
  g = deepcopy(g1)

  res = R(1)
  while true
    #First, some trivial check.
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) && iszero(g)
        res = zero(R)
      else
        res = mul!(res, res, R(gcd(lift(leading_coefficient(f)), lift(leading_coefficient(g)))))
      end
      return res
    end

    if degree(f) < degree(g)
      f, g = g, f
    end
    if degree(g) < 1

      if is_divisible_by(lift(coeff(f, degree(f))), p)
        #need the constant coeff * the annihilator of the others...
        a = coeff(f, 1)
        for i = 2:degree(f)
          a = gcd(a, coeff(f, i))
          if isone(a)
            break
          end
        end
        a = annihilator(a)
        if iszero(a)
          return res*coeff(g, 0)
        else
          res = mul!(res, res, R(gcd(lift(coeff(g, 0)), lift(a)*lift(coeff(f, 0)))))
          return res
        end
      else
        res = mul!(res, res, constant_coefficient(g))
        return res
      end
    end

    c, g = primsplit!(g)
    res = mul!(res, res, c)
    if iszero(res)
      return res
    end

    if is_divisible_by(lift(coeff(g, degree(g))), p)
      #one of the coefficient will now be invertible (at least after the splitting)
      g = fun_factor(g)[2]
    end
    rem!(f, f, g)
  end
end

# Based on these formulas:
# rres(f, g) = rres(f - kg, g), so I can divide.
# rres(f, g) = rres(g, f)
# rres(uf, g) = rres(f, g)
# rres(pf, g) mod p^n = p*(rres(f, g) mod p^(n-1)) (under right hypotheses)
function rres_sircana(f1::PolyRingElem{T}, g1::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f1, g1)
  @assert typeof(f1) == typeof(g1)
  Rt = parent(f1)
  R = base_ring(Rt)
  m = ZZRingElem(modulus(R))
  #easy = is_prime_power(m)
  #if easy
  #  return rres_sircana_pp(f1, g1)
  #end
  f = deepcopy(f1)
  g = deepcopy(g1)

  Zx = polynomial_ring(ZZ, cached = false)[1]

  res = R(1)
  while true
    #First, some trivial check.
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) && iszero(g)
        res = zero(R)
      else
        res *= R(gcd(lift(leading_coefficient(f)), lift(leading_coefficient(g))))
      end
      return res
    end

    if degree(f) < degree(g)
      f, g = g, f
    end

    if degree(g) < 1
      if !is_unit(leading_coefficient(f))
        #need the constant coeff * the annihilator of the others...
        a = coeff(f, 1)
        for i = 2:degree(f)
          a = gcd(a, coeff(f, i))
          if isone(a)
            break
          end
        end
        a = annihilator(a)
        if iszero(a)
          return leading_coefficient(g)
        else
          res *= gcd(leading_coefficient(g), a*constant_coefficient(f))
          return res
        end
      else
        res *= constant_coefficient(g)
        return res
      end
    end

    c, g = primsplit!(g)
    res *= R(c)
    if iszero(res)
      return res
    end

    if !is_unit(leading_coefficient(g))
      #one of the coefficient will now be invertible (at least after the splitting)
      s = gcd(m, lift(res))
      if !isone(s)
        m = divexact(m, s)
      end
      #if easy
      #  cp = S[m]
      #else
        cp = S[gcd(lift(coeff(g, i)), m) for i=0:degree(g)]
        push!(cp, m)
        cp = S[x for x = cp if !iszero(x)]
        cp = coprime_base(cp)
        cp = S[x for x = cp if !is_unit(x)] #error: [1, 1, 3, 27] -> [1,3]
      # end
      resp = ZZRingElem[]
      pg = ZZRingElem[]
      for p = cp
        lg = p^valuation(m, p)
        push!(pg, lg)
        R1 = residue_ring(ZZ, S(lg), cached=false)[1]
        R1t = polynomial_ring(R1, cached=false)[1]
        #g is bad in R1, so factor it
        gR1 = R1t(lift(Zx, g))
        fR1 = R1t(lift(Zx, f))
        res1 = one(R1)
        if is_unit(leading_coefficient(gR1))
          g2 = gR1
        else
          if iszero(gR1)
            push!(resp, ZZRingElem(0))
            continue
          end
          c, gR1 = primsplit!(gR1)
          res1 *= R1(c)
          g1, g2 = fun_factor(gR1)
        end
        push!(resp, lift(res1)*lift(rres_sircana(fR1, g2)))
      end
      if length(resp) == 1
        res *= R(resp[1])
      else
        res *= R(crt(resp, pg))
      end
      return res
    end

    f = rem!(f, f, g)
  end
end

@doc raw"""
    rresx(f::PolyRingElem{ResElem{ZZRingElem}}, g::PolyRingElem{ResElem{ZZRingElem}}) -> r, u, v

The reduced resultant $r$ and polynomials $u$ and $v$ s.th.
$r = uf+vg$ and $\langle r\rangle = \langle f, g\rangle\cap \mathbb Z$.
"""
function rresx(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)
  return rresx_sircana(f, g)
end

function rresx_sircana(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  @assert is_unit(leading_coefficient(f)) || is_unit(leading_coefficient(g))
  res, u, v = _rresx_sircana(f, g)
  if !iszero(res)
    cu = canonical_unit(res)
    cu = inv(cu)
    res = mul!(res, res, cu)
    u *= cu
    v *= cu
  end
  if is_unit(leading_coefficient(g))
    q, r = divrem(u, g)
    @hassert :AbsNumFieldOrder 1 res == r*f + (v+q*f)*g
    mul!(q, q, f)
    add!(v, v, q)
    return res, r, v
  else
    q, r = divrem(v, f)
    @hassert :AbsNumFieldOrder 1 res == (u+q*g)*f + r*g
    mul!(q, q, g)
    add!(u, u, q)
    return res, u, r
  end
end

function rresx_sircana_pp(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  @assert is_unit(leading_coefficient(f)) || is_unit(leading_coefficient(g)) #can be weakened to invertable lead
  res, u, v = _rresx_sircana_pp(f, g)
  if !iszero(res)
    cu = canonical_unit(res)
    cu = inv(cu)
    res = mul!(res, res, cu)
    u *= cu
    v *= cu
  end
  if is_unit(leading_coefficient(g))
    q, r = divrem(u, g)
    @hassert :AbsNumFieldOrder 1 res == r*f + (v+q*f)*g
    return res, r, v+q*f
  else
    q, r = divrem(v, f)
    @hassert :AbsNumFieldOrder 1 res == (u+q*g)*f + r*g
    return res, u+q*g, r
  end
end


function _rresx_sircana(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)

  Rt = parent(f)
  R = base_ring(Rt)
  Zx = polynomial_ring(ZZ, "x", cached = false)[1]
  m = ZZRingElem(modulus(R))
  #easy = is_prime_power(m)
  #if easy
  #  return _rresx_sircana_pp(f, g)
  #end

  u, v = Rt(0), Rt(1)
  U, V = Rt(1), Rt(0)

  while true
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) || iszero(g)
        res = R(0)
        u = Rt(0)
        v = Rt(0)
      else
        res, uu, vv = gcdx(leading_coefficient(f), leading_coefficient(g))
        #res = uu*f + vv*g = uu*(U f_in + V g_in) + vv*(u f_in + v g_in)
        #    = uu*U + vv*u  uu*V + vv*v
        u, v = (uu*U + vv*u), (uu*V + vv*v)
      end
      return res, u, v
    end

    if degree(f) < degree(g)
      f, g = g, f
      U, u = u, U
      V, v = v, V
    end

    if degree(g) < 1
      if !is_unit(leading_coefficient(f))
        #need the constant coeff * the annihilator of the others...
        a = coeff(f, 1)
        for i = 2:degree(f)
          a = gcd(a, coeff(f, i))
          if isone(a)
            break
          end
        end
        a = annihilator(a)
        if iszero(a)
          return leading_coefficient(g), u, v
        else
          res, uu, vv = gcdx(a*constant_coefficient(f), leading_coefficient(g))
          return res, uu*a*U + vv*u, uu*a*V + vv*v
        end
      else
        return constant_coefficient(g), u, v
      end
    end


    if !is_unit(leading_coefficient(g))
      c, g = primsplit(g)
      cp = ZZRingElem[gcd(lift(coeff(g, i)), m) for i=0:degree(g)]
      push!(cp, m)
      cp = coprime_base(cp)
      cp = ZZRingElem[x for x = cp if !is_unit(x)] #error: [1, 1, 3, 27] -> [1,3]
      resp = ZZRingElem[]
      resB = Tuple{typeof(f), typeof(f)}[]
      pg = ZZRingElem[]
      for p = cp
        lg = p^valuation(m, p)
        push!(pg, lg)
        R1 = residue_ring(ZZ, S(lg), cached=false)[1]
        R1t = polynomial_ring(R1, cached=false)[1]
        #g is bad in R1, so factor it
        gR1 = R1t(lift(Zx, g))
        fR1 = R1t(lift(Zx, f))

        if iszero(R1(lift(c)))
          push!(resp, ZZRingElem(0))
          push!(resB, (R1t(0), R1t(1))) #relation need to be primitive
        else
          if is_unit(leading_coefficient(gR1))
            g2 = gR1
            g1 = R1t(1)
          else
            g1, g2 = fun_factor(gR1)
          end
          #@assert is_unit(g1)
          rr, uu, vv = rresx_sircana(fR1, g2)
          push!(resp, lift(lift(c)*rr))
          push!(resB, (uu*lift(c), inv(g1)*vv))
        end
      end
      if length(cp) == 1
        res, u_, v_ = R(resp[1]), Rt(lift(Zx, resB[1][1])), Rt(lift(Zx, resB[1][2]))
      else
        ce = crt_env(pg)
        res = R(crt(resp, ce))
        u_ = Rt(induce_crt(typeof(f)[x[1] for x = resB], ce))
        v_ = Rt(induce_crt(typeof(f)[x[2] for x = resB], ce))
      end
      # f = U*f_in + V*g_in
      # g = u*f_in + v*g_in
      # r = u_ * f + v_ * g
      return res, (u_*U + v_*u), (u_*V + v_*v)
    end
    q, f = divrem(f, g)
    #f -> f-qg, so U*f_in + V * g_in -> ...
    U = U - q*u
    V = V - q*v
  end
end


function _rresx_sircana_pp(f1::PolyRingElem{T}, g1::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f1, g1)

  Rt = parent(f1)
  R = base_ring(Rt)
  Zx = polynomial_ring(ZZ, "x", cached = false)[1]
  m = ZZRingElem(modulus(R))
  f = f1
  g = g1

  u, v = Rt(0), Rt(1)
  U, V = Rt(1), Rt(0)


  while true
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) && iszero(g)
        res = R(0)
        u = Rt(0)
        v = Rt(0)
      else
        res, uu, vv = gcdx(leading_coefficient(f), leading_coefficient(g))
        #res = uu*f + vv*g = uu*(U f_in + V g_in) + vv*(u f_in + v g_in)
        #    = uu*U + vv*u  uu*V + vv*v
        u, v = (uu*U + vv*u), (uu*V + vv*v)
      end
      return res, u, v
    end

    if degree(f) < degree(g)
      f, g = g, f
      U, u = u, U
      V, v = v, V
    end

    if degree(g) < 1
      if !is_unit(leading_coefficient(f))
        #need the constant coeff * the annihilator of the others...
        a = coeff(f, 1)
        for i = 2:degree(f)
          a = gcd(a, coeff(f, i))
          if isone(a)
            break
          end
        end
        a = annihilator(a)
        if iszero(a)
          return leading_coefficient(g), u, v
        else
          res, uu, vv = gcdx(a*constant_coefficient(f), leading_coefficient(g))
          u, v = (uu*a*U + vv*u), (uu*a*V + vv*v)

          return res, u, v
        end
      else
        return constant_coefficient(g), u, v
      end
    end

    if !is_unit(leading_coefficient(g))
      c, g = primsplit(g)
      g1, g2 = fun_factor(g)
      rr, uu, vv = _rresx_sircana_pp(f, g2)
      res = rr*c
      u_ = uu*c
      v_ = inv(g1)
      mul!(v_, v_, vv)
      return res, (u_*U + v_*u), (u_*V + v_*v)
    end

    q, f = divrem(f, g)
    #f -> f-qg, so U*f_in + V * g_in -> ...
    U = U - q*u
    V = V - q*v
  end
end

function my_divrem(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  g1, g2 = fun_factor(g)
  if degree(g2) < 1 # g2 is monic, so it's 1
    return parent(f)(0), g2
  end
  u = invmod(g1, g2)
  q, r = divrem(f, g2)
  q, r = divrem(r*u, g2)
  return g1*r, g2
end

#need divexact using the fun_factor and coprime base as well...

#key idea (Carlo): if g = ab and a is a unit mod p, then it is actually a unit
# in Z/p^kZ, hence the ideal (f, g) = (f, b) where b is now monic.
#Thus rres(f,g ) = rres(f, b).... and the division can continue
@doc raw"""
    reduced_resultant(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion -> T

The reduced resultant of $f$ and $g$ using a quadratic-time algorithm.
That is a generator for the $(f, g) \cap Z$
"""
function reduced_resultant(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)
  return rres_sircana(f, g)
end

################################################################################
#
#  Gcd
#
################################################################################

@doc raw"""
    gcd_sircana(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion -> T

The 'gcd' of $f$ and $g$ together with the 'cofactors' using a quadratic-time algorithm.
"""
function gcd_sircana(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)
  _F = f
  _G = g
  @assert typeof(f) == typeof(g)
  iszero(g) && return f, one(parent(f)), zero(parent(f))
  iszero(f) && return g, zero(parent(f)), one(parent(f))
  isone(f) && return f, f, g
  isone(g) && return g, f, g

  Rt = parent(f)
  R = base_ring(Rt)
  m = ZZRingElem(modulus(R))
  #from Sircana: if content is nilpotent, then removing the content
  # results in s.th. that has a non-nilpotent content
  # one should be able to use this to split the ring
  # recall: if the leading coeff is nilpotent, but the polynomial is not
  #   then the polynomial splits into unit * monic. The unit is not
  #   used for gcd.
  # start with primitive polynomials - in contrast to fields we
  # cannot ignore the contents as it can contribute...
  @assert isone(content(f))
  @assert isone(content(g))

  while !iszero(g)
    if !is_unit(leading_coefficient(g))
      cp = coprime_base(vcat(map(x->gcd(lift(x), modulus(R)), coefficients(g)), [modulus(R)]))
      cp = [x for x = cp if !is_unit(x)]
      gc = NTuple{3, ZZPolyRingElem}[]
      for p = cp
        F, mF = quo(parent(p), p^valuation(modulus(R), p))
        gp = map_coefficients(mF, g, cached = false)
        @assert base_ring(gp) == F
        fp = map_coefficients(mF, f, parent = parent(gp))
        if !is_unit(leading_coefficient(fp))
          if iszero(fp)
            fp = zero(parent(fp))
          else
            _, fp = fun_factor(fp)
          end
        end
        if !is_unit(leading_coefficient(gp))
          if iszero(gp)
            gp = zero(parent(gp))
          else
            _, gp = fun_factor(gp)
          end
        end
        push!(gc, map(y->map_coefficients(x->lift(x), y, cached = false), gcd_sircana(fp, gp)))
      end
      f = map_coefficients(R, induce_crt([x[1] for x = gc], cp), parent = parent(f))
      qf = map_coefficients(R, induce_crt([x[2] for x = gc], cp), parent = parent(f))
      qg = map_coefficients(R, induce_crt([x[3] for x = gc], cp), parent = parent(f))
      break
    else
      f, g = g, rem(f, g)
      if iszero(g)
        qf = divexact(_F, f)
        qg = divexact(_G, f)
        break
      end
    end
  end
  c = canonical_unit(leading_coefficient(f))
  f = divexact(f, c)
  qf *= c
  qg *= c

  @assert f*qf == _F
  @assert f*qg == _G

  return f, qf, qg
end

function induce_crt(f::Vector{<:PolyRingElem{T}}, m::Vector{ZZRingElem}, parent::ZZPolyRing = Hecke.Globals.Zx) where {T}
  d = maximum(degree, f)
  g = parent()
  ce = crt_env(m)
  for i=0:d
    setcoeff!(g, i, crt([coeff(x, i) for x = f], ce))
  end
  return g
end

################################################################################
#
#  Resultant
#
################################################################################

@doc raw"""
    resultant_sircana(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion -> T

The resultant of $f$ and $g$ using a quadratic-time algorithm.
"""
function resultant_sircana(f::PolyRingElem{T}, g::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = ZZRingElem(modulus(R))
  e, p = is_perfect_power_with_data(m)
  easy = is_prime(p)

  Zx = polynomial_ring(ZZ, cached = false)[1]

  res = R(1)

  while true
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) || iszero(g)
        res *= R(0)
      else
        res *= R(1)
      end
      return res
    end

    if degree(f) < 1
      res *= leading_coefficient(f)^degree(g)
      return res
    end

    if degree(g) < 1
      res *= leading_coefficient(g)^degree(f)
      return res
    end

    c, f = primsplit(f)
    if !isone(c)
      res *= c^degree(g)
    end

    c, g = primsplit(g)
    if !isone(c)
      res *= c^degree(f)
    end

    if degree(f) < degree(g)
      res *= (-1)^(degree(f)*degree(g))
      f, g = g, f
    end

    #want f % g which works iff leading_coefficient(g) | leading_coefficient(f)

    if is_unit(leading_coefficient(g)) #accelerate a bit...possibly.
      q, r = divrem(f, g)
      res *= leading_coefficient(g)^(degree(f) - degree(r))
      res *= R(-1)^(degree(g)*(degree(f) - degree(r)))
      f = r
      continue
    end

    if gcd(lift(leading_coefficient(f)), m)  % gcd(lift(leading_coefficient(g)), m) == 0
      q = divexact(leading_coefficient(f), leading_coefficient(g))
      ff = f - q*g*gen(Rt)^(degree(f) - degree(g))
      @assert degree(f) > degree(ff)
      res *= leading_coefficient(g)^(degree(f) - degree(ff))
      res *= R(-1)^(degree(g)*(degree(f) - degree(ff)))
      f = ff
      continue
    end
    break
  end

  #factoring case, need to split the ring as well.
  #merde : we need a coprime factorisation: take
  # 6t^2+2t+3 mod 36....
  if easy
    cp = [m]
  else
    cp = [gcd(lift(coeff(g, i)), m) for i=0:degree(g)]
    push!(cp, m)
    cp = [x for x = cp if !iszero(x)]
    cp = coprime_base(cp)
    cp = [x for x = cp if !is_unit(x)] #error: [1, 1, 3, 27] -> [1,3]
  end
  resp = ZZRingElem[]
  pg = ZZRingElem[]
  for p = cp
    lg = p^valuation(m, p)
    push!(pg, lg)

    if lg != m
      R1 = residue_ring(ZZ, S(lg), cached=false)[1]
      R1t = polynomial_ring(R1, cached=false)[1]
      #g is bad in R1, so factor it
      gR1 = R1t(lift(Zx, g))
      fR1 = R1t(lift(Zx, f))
    else
      gR1 = g
      fR1 = f
      R1 = R
      R1t = Rt
    end

    if degree(fR1) < degree(f) &&
       degree(gR1) < degree(g)
       res1 = R1(0)
    elseif degree(fR1) < degree(f)
        res1 = R1(-1)^(degree(g) * (degree(f) - degree(fR1))) *
               leading_coefficient(gR1)^(degree(f) - degree(fR1))
    elseif degree(gR1) < degree(g)
        res1 = leading_coefficient(fR1)^(degree(g) - degree(gR1))
    else
        res1 = R1(1)
    end

    if !is_unit(leading_coefficient(gR1))
      g1, g2 = fun_factor(gR1)

      #careful: leading_coefficient(g) = 0 mod lg is possible, so the degree drops!
      #from Wiki:
      # phi: R -> S
      # phi(res(f, g)) = res(phi(f), phi(g)) if the degrees are the same
      #                = 0                   if both degrees drop (zero column in
      #                                         sylvester matrix)
      #                = (-1)^(delta(f)*deg(g))*
      #                  phi(l(g))^delta(f)  if only degree(f) drops
      #                = phi(l(f))^delta(g)  if only degree(g) drops
      #
      # we use res(f, gh) = res(f, g)res(f, h) which seems to be true in general
      #next: res(fR1, gR1) = res(phi(f), g1)
      #g1 is = 1 mod p
      #however, reverse(fR1) can have a smaller degree then fR1 (eg. x^2 -> 1)
      # res(f, g) = t(g)^delta(f) * (-1)^(deg(g)*delta(f)) * res(rev(f), rev(g))
      # there is a (-1)^deg(f)*deg(g) from Wiki for the reverse on top.

      res1 *= resultant_sircana(reverse(fR1), reverse(g1))
      v = valuation(fR1, gen(parent(fR1)))
           #should be delta(f) = degree(rev(f)) - degree(f)
      res1 *= constant_coefficient(g1)^v*R1(-1)^(v*degree(g1))
      res1 *= R1(-1)^(degree(g1)*degree(fR1))

      res1 *= resultant_sircana(fR1, g2)
      push!(resp, lift(res1))
    else
      #gR1 has a invertible leading coeff
      res1 *= resultant_sircana(fR1, gR1)
      push!(resp, lift(res1))
    end
  end
  res *= length(cp)==1 ? R(resp[1]) : R(crt(resp, pg))
  return res
end

################################################################################
#
#  Fun Factor
#
################################################################################
# factors f as unit * monic
# requires some coefficient of f to be a unit

function fun_factor(f::T) where T <: Union{ZZModPolyRingElem, zzModPolyRingElem}
  Rx = parent(f)
  if is_unit(leading_coefficient(f))
    l = leading_coefficient(f)
    return Rx(l), f*inv(l)
  end
  R = base_ring(Rx)
  smod = lift(coeff(f, degree(f)))
  ind = degree(f)-1
  while !is_unit(coeff(f, ind))
    smod = gcd(smod, lift(coeff(f, ind)))
    ind -= 1
  end
  if iszero(ind)
    return f, one(Rx)
  end

  u0 = zero(Rx)
  for i = 0:degree(f)-ind
    setcoeff!(u0, i, coeff(f, ind+i))
  end
  g0 = zero(Rx)
  invc = inv(coeff(f, ind))
  for i = 0:ind-1
    setcoeff!(g0, i, coeff(f, i) * invc)
  end
  setcoeff!(g0, ind, one(R))

  Zy, y = polynomial_ring(ZZ, "y", cached = false)
  f2 = lift(Zy, f)
  mod = ZZRingElem(gcd(smod, ZZRingElem(modulus(Rx)))) #We have the equality modulo mod
  mod = gcd(mod*mod, ZZRingElem(modulus(Rx)))
  R1 = residue_ring(ZZ, mod, cached = false)[1]
  R1x, x = polynomial_ring(R1, "x", cached = false)
  s = R1x(lift(inv(coeff(u0, 0))))
  t = zero(R1x)
  u = R1x(lift(Zy, u0))
  g = R1x(lift(Zy, g0))

  f1 = R1x(f2)
  u, g, s, t = _hensel(f1, u, g, s, t)
  @hassert :AbsNumFieldOrder 1 f1 == u*g
  i = 1
  modRx = ZZRingElem(modulus(Rx))
  while modRx > mod

    mod = mod*mod
    if mod > modRx
      mod = modRx
    end
    R1 = residue_ring(ZZ, mod, cached = false)[1]
    R1x, x = polynomial_ring(R1, "x", cached = false)
    u = R1x(lift(Zy, u))
    g = R1x(lift(Zy, g))
    s = R1x(lift(Zy, s))
    t = R1x(lift(Zy, t))
    f1 = R1x(f2)
    i += 1

    u, g, s, t = _hensel(f1, u, g, s, t)

    @hassert :AbsNumFieldOrder 1 f1 == u*g

    if i>20 #in general: loop forever... one could check that the
      # contents of f-gh and s*g+t*h - 1 is nilpotent.
      # this SHOULD ensure convergence
      @show f
      @show parent(f)
      @show g, u, s, t
      @show content(f-g*u)
      @show content(g*t-s*u-1)
      error("too long")
    end
  end
  u0 = Rx(lift(Zy, u))
  g0 = Rx(lift(Zy, g))
  @hassert :AbsNumFieldOrder 1 g0*u0 == f
  return u0, g0
end



function _hensel(f::PolyRingElem{T}, g::PolyRingElem{T}, h::PolyRingElem{T}, s::PolyRingElem{T}, t::PolyRingElem{T}) where T <: RingElem #from von zur Gathen: h needs to be monic
  @assert is_monic(h)
  #@assert is_nilpotent(content(f-g*h))  #this guarantees useful lifting
  #@assert is_nilpotent(content(g*s+h*t-1))
  Rx = parent(f)
  aux1 = Rx()
  mul!(aux1, g, h)
  sub!(aux1, f, aux1)
  #aux1 = f-g*h
  aux2 = Rx()
  mul!(aux2, s, aux1)
  q, r = divrem(aux2, h)
  #@assert s*e == q*h+r
  mul!(aux1, aux1, t)
  add!(aux1, aux1, g)
  mul!(aux2, q, g)
  add!(aux1, aux1, aux2)
  #g = g+t*e+q*g
  g = aux1
  add!(aux2, h, r)
  h = aux2
  #h = h+r
  #@assert is_monic(h)
  aux3 = Rx()
  aux4 = Rx()
  mul!(aux3, s, aux1)
  mul!(aux4, t, aux2)
  add!(aux3, aux3, aux4)
  sub!(aux3, aux3, one(Rx))
  mul!(aux4, s, aux3)
  c, d = divrem(aux4, h)
  #@assert s*b == c*h+d
  mul!(aux3, aux3, t)
  sub!(aux3, t, aux3)
  mul!(c, c, g)
  sub!(aux3, aux3, c)
  sub!(aux4, s, d)
  return aux1, aux2, aux4, aux3
end

################################################################################
#
#  Primitive splitting
#
################################################################################


@doc raw"""
    primsplit!(f::PolyRingElem{ResElem{ZZRingElem}}) -> c, f
    primsplit!(f::PolyRingElem{ResElem{Integer}}) -> c, f

Computes the contents $c$ and the primitive part of $f$ destructively.
"""
function primsplit!(f::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion

  @assert !iszero(f)
  d = degree(f)
  if iszero(d)
    if iszero(f)
      return base_ring(parent(f))(1), f
    end
    c = canonical_unit(coeff(f, 0))
    c1 = inv(c)*coeff(f, 0)
    setcoeff!(f, 0, c)
    return c1, f
  end
  fl, g = is_primitive(f)
  if fl
    return g, f
  end

  for i = 0:d
    setcoeff!(f, i, divexact(coeff(f, i), g))
  end
  return g, f
end

@doc raw"""
    primsplit(f::PolyRingElem{ResElem{ZZRingElem}}}) -> c, f
    primsplit(f::PolyRingElem{ResElem{Integer}}}) -> c, f

Computes the contents $c$ and the primitive part of $f$.
"""
function primsplit(f::PolyRingElem{T}) where T <: ResElem{S} where S <: IntegerUnion
  g = deepcopy(f)
  return primsplit!(g)
end

function quo(R::fqPolyRepPolyRing, f::fqPolyRepPolyRingElem)
  Q, mQ = residue_ring(R, f)
  return Q, mQ
end

#= not finished
function unit_group(R::EuclideanRingResidueRing{fqPolyRepPolyRingElem})
  f = modulus(R)
  lf = factor(f)
  lu = [unit_group_pp(p, k) for (p,k) = f.fac]
  return lu
end

function unit_group_pp(f::fqPolyRepPolyRingElem, k::Int)
  @assert is_irreducible(f)
  k, o = GF(characteristic(parent(f)), degree(base_ring(f))*degree(f))
  #o is a primitive element as per Bill's semantic...
  #however, I need it written wrt. "my" poly
end

=#

function unit_group_1_part(f::fqPolyRepPolyRingElem, k::Int)
  pr = [k]
  while k>1
    k = div(k+1, 2)
    push!(pr, k)
  end

  K = base_ring(f)
  x = gen(parent(f))
  p = characteristic(K)

  b = basis(K)
  gens = [1+f*x^i*c for i=0:degree(f)-1 for c = b]
  rels = identity_matrix(ZZ, length(gens))*p

  for i=length(pr)-1:-1:2
    p1 = pr[i]
    p2 = pr[i-1]
    f1 = f^p1
    f2 = f^p2
    # 1 -> 1+f^p1/1+f^p2 -> 1+f/1+f^p2 -> 1+f/1+f^p1 -> 1
    # by induction, we have  presentation for 1+f/1+f^p1
    # gens are polys and rels is a matrix with the relations
    #
    # new gens:
    # 1+f^p1/1+f^p2 = f^p1/f^p2 = f^(p2-p1), latter additively
    ngens = [1+(x^i)*f1*c for i=0:(degree(f)*(p2-p1)-1) for c = b]
    nr = matrix(ZZ, 0, length(ngens), [])
    for j=1:nrows(rels)
      g = rem(prod(powermod(gens[k], rels[j, k], f2) for k=1:ncols(rels)), f2) - 1
      q,r = divrem(g, f1)
      @assert iszero(r)
      nr = vcat(nr, matrix(ZZ, 1, ncols(nr), [(coeff(coeff(q, k), l)) for k = 0:degree(f)*(p2-p1)-1 for l = 0:degree(K)-1]))
    end
    rels = [rels -nr; zero_matrix(ZZ, length(ngens), ncols(rels)) identity_matrix(ZZ, length(ngens))*p]
    append!(gens, ngens)
  end
  return gens, rels
end

function euler_phi(f::T) where {T <: Union{fpPolyRingElem, fqPolyRepPolyRingElem, FpPolyRingElem}}
  lf = factor(f)
  q = size(base_ring(f))
  return prod((q^degree(p)-1)*q^(degree(p)*k) for (p,k) = lf.fac)
end

function carmichael_lambda(f::T) where {T <: Union{fpPolyRingElem, fqPolyRepPolyRingElem, FpPolyRingElem}}
  lf = factor(f)
  pp = characteristic(base_ring(f))
  q = size(base_ring(f))
  #ala Auer... (Diss, DOI:10.4064/aa-95-2-97-122)
  l = reduce(lcm, [(q^degree(p)-1)*pp^ceil(Int, log(k)/log(pp)) for (p,k) = lf.fac], init = ZZRingElem(1))
  #l = reduce(lcm, [(q^degree(p)-1)*largest_elementary_divisor(unit_group_1_part(p, k)[2]) for (p,k) = lf.fac], init = ZZRingElem(1))
  return l
end


@doc raw"""
    compose_mod(x::zzModPolyRingElem, y::zzModPolyRingElem, z::zzModPolyRingElem) -> zzModPolyRingElem

  Compute $x(y)$ mod $z$.
"""
function compose_mod(x::zzModPolyRingElem, y::zzModPolyRingElem, z::zzModPolyRingElem)
  check_parent(x,y)
  check_parent(x,z)
  r = parent(x)()
  ccall((:nmod_poly_compose_mod, libflint), Nothing,
          (Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}), r, x, y, z)
  return r
end

function compose_mod(x::fpPolyRingElem, y::fpPolyRingElem, z::fpPolyRingElem)
  check_parent(x,y)
  check_parent(x,z)
  r = parent(x)()
  ccall((:nmod_poly_compose_mod, libflint), Nothing,
          (Ref{fpPolyRingElem}, Ref{fpPolyRingElem}, Ref{fpPolyRingElem}, Ref{fpPolyRingElem}), r, x, y, z)
  return r
end


@doc raw"""
    taylor_shift(x::zzModPolyRingElem, c::UInt) -> zzModPolyRingElem

  Compute $x(t-c)$.
"""
function taylor_shift(x::zzModPolyRingElem, c::UInt)
  r = parent(x)()
  ccall((:nmod_poly_taylor_shift, libflint), Nothing,
          (Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}, UInt), r, x, c)
  return r
end


"""
    is_primitive(f::zzModPolyRingElem)

Tests if the ideal generated by the coefficients is trivial, ie. the full ring.
"""
function is_primitive(f::zzModPolyRingElem)
  R = base_ring(f)
  n = R(gcd(modulus(R), lift(coeff(f, 0))))
  if isone(n)
    return true, n
  end
  for i = 1:degree(f)
    n = gcd(n, coeff(f, i))
    if isone(n)
      return true, R(n)
    end
  end
  return isone(n), R(n)
end

"""
    is_primitive(f::ZZModPolyRingElem)

Tests if the ideal generated by the coefficients is trivial, ie. the full ring.
"""
function is_primitive(f::ZZModPolyRingElem)
  Rx = parent(f)
  R = base_ring(Rx)
  z = ZZRingElem()
  g = ZZRingElem()
  GC.@preserve f begin
    for i = 0:degree(f)
      ccall((:fmpz_mod_poly_get_coeff_fmpz, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZModPolyRingElem}, Int, Ref{fmpz_mod_ctx_struct}), z, f, i, f.parent.base_ring.ninv)
      gcd!(g, g, z)
      if isone(g)
        return true, R(g)
      end
    end
  end
  gcd!(g, g, modulus(R))
  return isone(g), R(g)
end

function _coprimality_test(f::T, g::T, h::T) where T <: Union{zzModPolyRingElem, ZZModPolyRingElem}
  Rx = parent(f)
  m = modulus(Rx)
  #First, I order the polynomials by degree
  if degree(f) > degree(g)
    if degree(g) > degree(h)
      return _coprimality_test(h, g, f)
    elseif degree(f) > degree(h)
      return _coprimality_test(g, h, f)
    else
      return _coprimality_test(g, f, h)
    end
  elseif degree(g) > degree(h)
    return _coprimality_test(f, h, g)
  end
  #Now, we start.
  Zx = polynomial_ring(ZZ, "x", cached = false)[1]
  while true
    if is_constant(f)
      if is_unit(coeff(f, 0))
        return true
      else
        return is_unit(gcd(coeff(f, 0), reduced_resultant(f, h)))
      end
    end
    if is_unit(leading_coefficient(f))
      g = mod(g, f)
      h = mod(h, f)
      if is_constant(g)
        if is_unit(g)
          return true
        else
          return is_unit(gcd(coeff(g, 0), reduced_resultant(f, h)))
        end
      elseif is_constant(h)
        if is_unit(h)
          return true
        else
          return is_unit(gcd(coeff(h, 0), reduced_resultant(f, g)))
        end
      end
      if degree(g) > degree(h)
        f, g, h = h, g, f
      else
        f, g, h = g, h, f
      end
      continue
    end

    c, f = primsplit(f)
    must_split = false
    if is_unit(c)
      for i = degree(f):-1:0
        cfi = coeff(f, i)
        if is_nilpotent(cfi)
          continue
        end
        if is_unit(cfi)
          break
        else
          must_split = true
        end
      end
      if !must_split
        f = fun_factor(f)[2]
        continue
      end
    end
    if !must_split && is_unit(leading_coefficient(g))
      h = mod(h, g)
      if degree(h) < degree(f)
        f, g, h = h, c*f, g
      else
        f, g, h = c*f, h, g
      end
      continue
    end
    c1, g = primsplit(g)
    if !must_split && is_unit(c1)
      for i = degree(g):-1:0
        cgi = coeff(g, i)
        if is_nilpotent(cgi)
          continue
        end
        if is_unit(cgi)
          break
        else
          must_split = true
        end
      end
      if !must_split
        g = fun_factor(g)[2]
        if degree(g) < degree(f)
          f, g, h  = g, h, f
          continue
        end
        h = mod(h, g)
        if degree(h) <= degree(f)
          f, g, h = h, f, g
        else
          f, g, h = f, h, g
        end
        continue
      end
    end
    if must_split || is_unit(gcd(c, c1))
      #split the ring
      _to_base = ZZRingElem[m, lift(c), lift(c1)]
      for i = 0:degree(f)
        cfi = coeff(f, i)
        if !iszero(cfi) && !is_unit(cfi)
          push!(_to_base, lift(cfi))
        end
      end
      for i = 0:degree(g)
        cgi = coeff(g, i)
        if !iszero(cgi) && !is_unit(cgi)
          push!(_to_base, lift(cgi))
        end
      end
      for i = 0:degree(h)
        chi = coeff(h, i)
        if !iszero(chi) && !is_unit(chi)
          push!(_to_base, lift(chi))
        end
      end
      cp = coprime_base(_to_base)
      for p in cp
        if isone(p) || !is_divisible_by(ZZRingElem(m), p)
          continue
        end
        R = residue_ring(ZZ, Int(p), cached = false)[1]
        Rx = polynomial_ring(R, "x", cached = false)[1]
        f1 = Rx(lift(Zx, c*f))
        g1 = Rx(lift(Zx, c1*g))
        h1 = Rx(lift(Zx, h))
        if !_coprimality_test(f1, g1, h1)
          return false
        end
      end
      return true
    end
    return false
  end
end
