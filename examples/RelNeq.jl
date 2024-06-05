module module_RelNeq

using Hecke

struct RelNeq
  k::AbsSimpleNumField
  K::AbsSimpleNumField
  Kk::Hecke.RelSimpleNumField{AbsSimpleNumFieldElem}
  m_k_K::Map
  m_Kk_K::Map
  function RelNeq(k::AbsSimpleNumField, Kk::Hecke.RelSimpleNumField{AbsSimpleNumFieldElem})
    k = base_ring(Kk)
    K, m_K_Kk = absolute_simple_field(Kk)
    m1 = inv(m_K_Kk)
    return new(k, K, Kk, m1, restrict(m1, k))
  end

  function RelNeq(k::AbsSimpleNumField, K::AbsSimpleNumField)
    kt, t = polynomial_ring(k, cached = false)
    fl, mp = Hecke.is_subfield(k, K)
    Qt = parent(K.pol)
    h = gcd(gen(k) - evaluate(Qt(mp(gen(k))), t), evaluate(K.pol, t))
    Kk, _ = number_field(h)
    return new(k, K, Kk, mp, mp)
  end

  function RelNeq(m::Map)
    return RelNeq(domain(m), codomain(m))
  end
end

#= Via Lorenz... Let K/k be finite

  {N(I) = 1}
  ----------   < Cl_(Z_K * m)
  {N(a) = 1}

  For m the lorenz_module for n=K:k in Z_k: any unit u = 1 (m) is an n-th power.
  If I = J in Cl_(Z_K m) => I = a J and a = 1 (Z_K m). Furthermore, since N(I) = N(J) = 1Zk (the trivial ideal)
  N(a) is a unit. Since a = 1 (Z_K m) we have N(a) = 1 (m) so N(a) = eps^n, thus N(a/eps) = 1 and
  I = J in the norm-1-group.
  Since the map (injection) is only well defined on ideals coprime to m, we don't get everything.
  We're missing the contribution of finitely many explicit ideals, hence this can be fixed.

  In the case of k = Q, this amounts to the strict (narrow) class group (I think).

  This is easier to handle than the version below (free of lorenz_module).

  Next Q: Let N^1 be the subgroup of Cl_M defined above. Then

           X_M  the ray class field mod M = Z_K m
            |
            |
            X   the class field for N^1, thus the norm group is Cl_M/N^1
         Y  |   the norm group of Y is the norm of X_M over k.
         |  |   Possibly X = KY? To neat, but maybe a central/ ...? extension
         |  K
         | /
         |/
         k


 Now, finally the question: has X any (useful) Galois theoretic characterisation such as
   the minimal/ maximal field ...
   the compositum with ...
   is a version of the genus field ...
 Can one use this unknown characterisation to compute X (the degree of X) hence get a method to
 provably compute N^1?
 So far, to compute N^1: just try small prime ideals until the computation stablises. Then hope.
   Alternatively: use Jan Albert's thesis to get bound on the generation...

 For K/k normal this should reduce(?) to Scholz' paper (or Jehne's version) on Zahlknoten/ number knots
 In this case N(I) = 1 iff I = prod A^(1-sigma a) thus it can be computed from the Galois action on
 ideal (classes), then Cl/N^1 is fixed pointwise by Gal(K/k) (trivial action) (in fact this should be the
 largest/ smallest such quotient)
 hence the group extension (exact sequence)

   1 -> Cl/N^1 -> Gal(X/k) -> Gal(K/k) -> 1

 is split(?) direct(?) (nice?) (special?)

 My memory of Scholz is that there is a second field lurking around...
=#
function norm_1_subgroup(A::RelNeq)
  k = A.k
  K = A.K
  Kk = A.Kk

  d = lcm([numerator(discriminant(k)), numerator(discriminant(K)), numerator(norm(discriminant(Kk)))])

  @show I = Hecke.lorenz_module(k, degree(Kk), containing = discriminant(maximal_order(Kk)))
  Hecke.assure_2_normal(I)
  ZK = maximal_order(K)

  I_K = ideal(ZK, I.gen_one, maximal_order(K)(A.m_k_K(I.gen_two.elem_in_nf)))
  r, mr = ray_class_group(I_K, real_places(K), n_quo = degree(Kk))

  q, mq = quo(r, elem_type(r)[])

  S = PrimesSet(1, -1)
  gens = Set{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  gg = []

  max_stable = 15*ngens(r)
  stable = max_stable

  np = 0
  for p = S
    np += 1
    if np % 50 == 0
      @show p, stable, snf(q)[1]
    end
    if minimum(I) % p == 0
      continue
    end

    lp = prime_decomposition(maximal_order(k), p)
    for P = lp
      if d % p == 0
        lP = collect(factor(IdealSet(ZK)(A.m_k_K, P[1])))
      else
        lP = Hecke.prime_decomposition_nonindex(A.m_k_K, P[1])
      end
      f = [ZZRingElem(div(degree(Q[1]), degree(P[1]))) for Q = lP]
      m = matrix(FlintZZ, 1, length(f), f)
      n = kernel(m, side = :right)
      r = ncols(n)

      decom = [mq(mr\Q[1]) for Q = lP]
      for i=1:r
        a = sum(n[j,i] * decom[j] for j = 1:length(decom))
        if iszero(a)
          stable -= 1
          continue
        end
        stable = max_stable

        q, nq = quo(q, [a])
        @show order(q), snf(q)[1]
        mq = mq*nq
        decom = [nq(x) for x = decom]
        push!(gens, P[1])
        push!(gg, FacElem(Dict((lP[j][1], n[j, i]) for j=1:length(decom) if n[j,i] != 0)))
      end
    end
    if stable <= 0
      break
    end
  end

  return mr, mq, gens, gg
end


function knot(K::AbsSimpleNumField)
  return knot(rationals_as_number_field()[1], K)
end

function knot(k::AbsSimpleNumField, K::AbsSimpleNumField)
  R = RelNeq(k, K)
  #TODO: is this better than using implicit extensions?
  mr, mq, gens, gg = norm_1_subgroup(R)
  #TODO: first genus_field as this is (should be) a lower bound for the search
  #of norm-1 stuff
  Z = ray_class_field(mr, mq)
  G = genus_field(Z, k)
  return degree(ZZRingElem, Z)//degree(ZZRingElem, G)
end

#= The idea
  we have
                        1

                        |
                        V

        U_K        {N(a) in U_k}      {N(I) = 1}
1 -> ---------- -> -------------  ->  ----------  -> Cl
     {N(u) = 1}      {N(a) = 1}       {N(a) = 1}

                        | N
                        V

                       U_k


 So what we want is a group extension of a sub-group of a quotient of U_k
 by a subgroup of Cl:

                        1

                        |
                        V

                {N(a) in U_k}      {N(I) = 1}
      1  ->   ----------------  ->  ----------  -> Cl
              N(U_K){N(a) = 1}       {N(a) = 1}

                        | N
                        V

                       U_k
                      -----
                      N(U_K)


=#
mutable struct Norm1Group
  gens::Vector{Hecke.AbsSimpleNumFieldOrderFractionalIdeal}
  rels
  A::RelNeq
  gC::Vector{Tuple{Hecke.AbsSimpleNumFieldOrderFractionalIdeal, FinGenAbGroupElem}}
  sC::Tuple{FinGenAbGroup, Hecke.FinGenAbGroupHom}
  gU::Vector{Tuple{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, FinGenAbGroupElem}}
  sU::Tuple{FinGenAbGroup, Hecke.FinGenAbGroupHom}
  C::Any
  U::Any

  function Norm1Group(A::RelNeq)
    r = new()
    r.A = A
    r.C = class_group(A.K)
    c, mc = r.C
    r.sC = sub(c, elem_type(c)[])
    U, mU = Hecke.unit_group_fac_elem(maximal_order(A.K))
    u, mu = Hecke.unit_group_fac_elem(maximal_order(A.k))
    q, mq = quo(u, [mu\norm(A.m_k_K, mU(U[i])) for i=1:ngens(U)])
    r.U = q, pseudo_inv(mq)*mu
    r.sU = sub(u, elem_type(u)[])
    r.gC = [(ideal(maximal_order(A.K), 1)//1, 0*c[1])]
    r.gU = [(FacElem(A.k(1)), 0*q[1])]
    r.gens = []
    return r
  end
end

function Base.show(io::IO, N::Norm1Group)
  println(io, "Norm-1-class group")
  println(io, snf(N.sC[1])[1], " by ", snf(N.sU[1])[1])
  println(io, "currently, using $(length(N.gens)) generators")
end

function is_principal_fac_elem(A::FacElem{<:AbsNumFieldOrderIdeal})
  a,b = Hecke.reduce_ideal(A)
  # a*b == A
  fl, c = is_principal_fac_elem(a)
  if !fl
    return fl, c
  end
  return fl, c*b
end

function is_principal_fac_elem(A::FacElem{<:Hecke.AbsSimpleNumFieldOrderFractionalIdeal})
  zk = order(base_ring(A))
  B = FacElem(Dict((numerator(x), v) for (x,v) = A.fac))
  den = Dict{AbsSimpleNumFieldElem, ZZRingElem}()
  for (x,v) = A.fac
    k = nf(zk)(denominator(x))
    if haskey(den, k)
      den[k] += v
    else
      den[k] = v
    end
  end
  #TODO: redude_ideal for FracIdl as well
  a,b = Hecke.reduce_ideal(B)
  # a*b == B = A*den
  fl, c = is_principal_fac_elem(a)
  if !fl
    return fl, c
  end
  return fl, c*b*inv(FacElem(den))
end


function Base.push!(N::Norm1Group, I::Hecke.AbsSimpleNumFieldOrderFractionalIdeal)
  A = N.A
  @assert isone(norm(A.m_k_K, I))
  c, mc = N.C
  u, mu = N.U
  r = mc\numerator(I)
  fl, s = has_preimage_with_preimage(N.sC[2], r)
  if fl # found new relation
    J = FacElem(Dict((N.gC[i][1], s.coeff[1, i]) for i=1:ngens(N.sC[1])))
    J = I*inv(J)
    fl, g = is_principal_fac_elem(J)
    @assert fl
    ng = norm(A.m_k_K, g)
    @assert is_unit(maximal_order(N.A.k)(evaluate(ng)))
    r = mu\ng
    fl, _ = has_preimage_with_preimage(N.sU[2], r)
    if fl
      return false # nothing new
    end
    push!(N.gens, I)
    push!(N.gU, (g, r))
    N.sU = sub(u, [x[2] for x = N.gU])
    return true
  else # found new generator
    push!(N.gens, I)
    push!(N.gC, (I, r))
    N.sC = sub(c, [x[2] for x = N.gC])
    return true
  end
end

function Hecke.order(N::Norm1Group)
  return order(N.sU[1]) * order(N.sC[1])
end

function order_bound(N::Norm1Group)
  return order(N.U[1]) * order(N.C[1])
end

Hecke.elem_type(::Type{Hecke.AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) = Hecke.AbsSimpleNumFieldOrderFractionalIdeal

function Hecke.evaluate(N::Norm1Group)
  # want the group extension (and the disc log and such)
  s1, ms1 = snf(N.sC[1])
  s2, ms2 = snf(N.sU[1])
  R = [rels(s2) zero_matrix(FlintZZ, ngens(s2), ngens(s1));
       zero_matrix(FlintZZ, ngens(s1), ngens(s2)) rels(s1)]

  for i = 1:ngens(s1)
    x = ms1(s1[i])
    I = FacElem(Dict((N.gC[j][1], x[j]) for j=1:ngens(N.sC[1])))
    I = I^order(x)
    fl, g = is_principal_fac_elem(I)
    @assert fl
    ng = norm(N.A.m_k_K, g)
    @assert is_unit(maximal_order(N.A.k)(evaluate(ng)))
    r = N.U[2]\ng
    fl, x = has_preimage_with_preimage(N.sU[2], r)
    for j=1:ngens(s2)
      R[ngens(s2) + i, j] = -x[j]
    end
  end
  A = abelian_group(R)
  ZK = maximal_order(N.A.K)
  function exp(a::FinGenAbGroupElem)
    a1 = sub(a.coeff, 1:1, 1:ngens(s2))
    a2 = sub(a.coeff, 1:1, ngens(s2)+(1:ngens(s1)))
    b1 = ms2(s2(a1))
    b2 = ms1(s1(a2))
    I1 = FacElem(Dict((N.gC[i][1], b2[i]) for i=1:ngens(N.sC[1])))
    I2 = prod(ideal(ZK, N.gU[i][1]) ^ b1[i] for i=1:ngens(N.sU[1]))
    return I1*I2
  end

  function log(I::Hecke.AbsSimpleNumFieldOrderFractionalIdeal)
    @assert isone(norm(N.A.m_k_K, I))
    r = N.C[2]\numerator(I)
    fl, s = has_preimage_with_preimage(N.sC[2], r)
    @assert fl
    J = FacElem(Dict((N.gC[i][1], s.coeff[1, i]) for i=1:ngens(N.sC[1])))
    J = I*inv(J)
    fl, g = is_principal_fac_elem(J)
    @assert fl
    ng = norm(N.A.m_k_K, g)
    @assert is_unit(maximal_order(N.A.k)(evaluate(ng)))
    r = N.U[2]\ng
    fl, r = has_preimage_with_preimage(N.sU[2], r)
    @assert fl
    return A(hcat((ms2\r).coeff, (ms1\s).coeff))
  end
  return A, exp, log
end

function n1group(A::RelNeq, B::Int)
  K = A.K
  k = A.k
  mp = A.m_k_K

  S = PrimesSet(2, -1)
  max_stable = 20
  stable = max_stable
  zk = maximal_order(k)
  ZK = maximal_order(K)
  N = Norm1Group(A)

  function single_prime(P::AbsNumFieldOrderIdeal)
    p = minimum(P)
    if numerator(discriminant(K)) % p == 0 ||
       numerator(discriminant(k)) % p == 0
       @show "expensive", p
      lq = collect(factor(IdealSet(ZK)(A.m_k_K, P)))
    else
      lq = Hecke.prime_decomposition_nonindex(A.m_k_K, P)
    end
    f = matrix(FlintZZ, 1, length(lq), ZZRingElem[div(degree(Q[1]), degree(P)) for Q = lq])
    n = kernel(f, side = :right)
    r = ncols(n)
    res = false
    for i = 1:r
      I = evaluate(FacElem(Dict((lq[j][1], n[j,i]) for j = 1:length(lq))), coprime = true)
      res = push!(N, I) || res
    end
    return res
  end

#TODO: missing: we NEED the ramified primes...
  for p = keys(factor(numerator(discriminant(ZK))).fac) #TODO: rel disc
    lp = prime_decomposition(zk, p)
    for P = lp
      if single_prime(P[1])
        stable = max_stable
      else
        stable -= 1
      end
    end
    if stable <= 0
      break
    end
  end

  d = lcm(numerator(discriminant(k)), numerator(discriminant(K)))

  for p = S
    if d % p == 0
      continue
    end
    lp = prime_decomposition(zk, p)
    for P = lp
      if single_prime(P[1])
        stable = max_stable
      else
        stable -= 1
      end
    end
    if stable <= 0
      break
    end
  end
  return N
end

function doit(f::ZZPolyRingElem)
  K, a = number_field(f, cached = false)
  x = gen(parent(K.pol))
  k, b = number_field(x-1, cached = false)
  R = RelNeq(k, K)
  N = n1group(R, 10)
  C, _ = evaluate(N)
  return C
end

Zx, x = FlintZZ["x"]
function doit(n::String)
  f = open(n, "r")
  fo = open("$n.out", "w")
  i = 1
  while true
    @show l = readline(f)
    g = eval(parse(l))
    C = doit(g)
    C = snf(C)[1]
    println(fo, "$l -> $(C.snf)")
    println("$l -> $(C.snf)")
    i += 1
    if i % 10 == 0
      flush(fo)
    end
  end
end



end



