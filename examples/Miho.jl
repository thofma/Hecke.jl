
function Hecke.trace_matrix(b::Vector{AbsSimpleNumFieldElem})
  m = zero_matrix(QQ, length(b), length(b))
  for i=1:length(b)
    m[i,i] = trace(b[i]*b[i])
    for j=i+1:length(b)
      m[i,j] = m[j,i] = trace(b[i]*b[j])
    end
  end
  return m
end

"""
Miho Aoki: From Leopoldt

Let G = C_(p^n) and K with Gal(K) = G
Then 

    O_K = oplus Z[G] a_i 

where the a_i are given explicitly as Gauss-sums from large cyclotomic fields   
This implements the Acciaro-Fieker approach, bypassing the Gauss sums
IN particular for n = 1 and tame fields, it will find a normal generator.
"""
function INB(K::AbsSimpleNumField)
  G, mG = automorphism_group(PermGroup, K)
  @assert is_cyclic(G)
  @assert Hecke.is_prime_power(degree(K))

  p = degree(K)
  @assert order(G) == p

  C, z = cyclotomic_field(p)
  OC = maximal_order(C)
  OK = maximal_order(K)

  f = iroot(discriminant(OK), p-1)
  is_wild = (!is_prime(p)) || f % p^2 == 0

  g = Hecke.normal_basis(K)
  g *= denominator(g, OK)

  sigma = cyclic_generator(G)

  nb = [g]
  for i=2:p
    push!(nb, mG(sigma)(nb[end]))
  end

  t = integral_split(trace_matrix(nb), ZZ)
  @assert t[2] == 1

  d = elementary_divisors(t[1])[end]
  trafo = matrix(hcat([coordinates(x) for x= nb]...))*(1//d)

  phi = function(x::AbsSimpleNumFieldElem)
    c = matrix(coordinates(x))
    s = solve(trafo, c; side = :right)
    return sum(s[i,1]*z^(i-1) for i=1:p)
  end

  I = sum(phi(x)*OC for x = basis(OK, K))
  fl, gamma = is_principal_with_data(I)
  @assert fl

  local tr
  if is_prime(p)
    all_u = AbsSimpleNumFieldElem[]
    get_u = x->x
    for i = 1:divexact(p-1, 2)
      push!(all_u, (1-z^i)/(1-z))
    end
    tr = trace
    pp = p
  else
    local u
    # a known subgroup of Z[G]^* of fin. index
    # from Acciaro-Fieker draft, probably from Bass
    u = [sum(gen(C)^(l-1) for l=1:i)^euler_phi(p) for i=2:p-1 if gcd(i, p) == 1]
    U, mU = unit_group(OC)
    q, mq = quo(U, [preimage(mU, x) for x = u])
    all_u = q
    get_u = x -> mU(preimage(mq, x))
    e, pp = is_power(p)
    au = mG(sigma^divexact(p, pp))
    tr = x->sum(mG(sigma^(i*divexact(p, pp)))(x) for i=0:pp-1)
  end
  for x = all_u
    u = get_u(x)
    g = sum(nb[i]*coeff(gamma*u, i-1) for i=1:p-1)//d

    if is_wild
      g1 = g+(0-tr(g))//pp
      if denominator(g1, OK) == 1
        @show :WILD
        if !is_prime(p)
          s, ms = subfields(K, degree = divexact(p, pp))[1]
          b = INB(s)
          b = map(ms, b)
          return push!(b, g1)
        else
          return [K(1), g1]
        end
      end
    else
      g1 = g+(1-trace(g))//p
      if denominator(g1, OK) == 1
        @show :TAME
        return [g1]
      end
      g2 = g+(-1-trace(g))//p
      if denominator(g2, OK) == 1
        @show :TAME
        return [g2]
      end
    end
  end
  error("dnw")
end

function INB_via_gauss(K::ClassField)
  p = degree(K)
  #@assert is_prime(p)
  @assert degree(base_field(K)) == 1

  @show f = norm(conductor(K)[1])
  C, _z = cyclotomic_field(NonSimpleNumField, Int(f))
  z = prod(_z)

  R, mR = quo(ZZ, f)
  U, mU = unit_group(R)

  #find the fix group in C of K, kind of...
  g = Tuple{FinGenAbGroupElem, FinGenAbGroupElem}[]
  p = 1
  q, mq = quo(U, [zero(U)])
  while order(q) > 1
    p = next_prime(p)
    f % p == 0 && continue
    i = preimage(mU, mR(ZZ(p)))
    is_zero(mq(i)) && continue
    push!(g, (i, preimage(K.rayclassgroupmap, base_ring(K)*p)))
    q, mmq = quo(q, [mq(i)])
    mq = mq * mmq
  end

  h = hom([x[1] for x = g], [x[2] for x = g])
  @assert is_bijective(h)

  #the Gauss sum is the trace down to K, ie. the sum over the fix group
  #this is done "by hand" via orbits of generators and primes and such
  #also: here cyclotomic elements are written as (sum of) powers of zeta
  #up to zeta^(n-1). The reduction modulo the polynomial is only done
  #in the end. MUCH faster
  H, mH = preimage(h, kernel(K.quotientmap)[1])
  H, mmH = snf(H)
  mH = mmH*mH
#  t = z

  T = Dict{Int, ZZRingElem}(1 => ZZ(1))
  for g = gens(H)
    o = order(g)
    lp = factor(o).fac
    for (p, k) = lp
      for i=1:k
#        aut = hom(C, C, z^Int(preimage(mR, mU(mH((o/p^i)*g)))), check = false)
        AUT = Int(preimage(mR, mU(mH((o/p^i)*g))))
#        s = t
        S = copy(T)
        for j = 1:p-1
          S = Dict(((k*AUT)%f) => v for (k, v) = S)
#          s = aut(s)
#          t += s
          for (k,v) = S
            if haskey(T, k)
              T[k] += v
            else
              T[k] = v
            end
          end
        end
      end
    end
  end
  con = [T]
  q, mq = quo(U, image(mH)[1])
  for x = q
    isone(x) && continue
    AUT = Int(preimage(mR, mU(preimage(mq, x))))
    AT = Dict(((k*AUT)%f) => v for (k, v) = T)
    push!(con, AT)
  end
  Qx = parent(C.pol[1])
  c = elem_type(C)[]
  o = [1 for x = _z]
  r = get_attribute(C, :decom)
  for t = con
    z = MPolyBuildCtx(Qx)
    for (k,v) = t
      push_term!(z, QQ(v), (k .* o) .% r)
    end
    push!(c, C(finish(z)))
  end
  return c, con
end





