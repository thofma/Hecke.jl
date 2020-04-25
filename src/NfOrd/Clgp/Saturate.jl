module RelSaturate
using Hecke

Hecke.add_verbose_scope(:Saturate)

export saturate!

function dlog(dl::Dict, x, p::Int) 
  if iszero(x)
    throw(Hecke.BadPrime(1))
  end
  if haskey(dl, x)
    return dl[x]
  end
#  println("difficult for ", parent(x))
  i = 2
  y = x*x
  while !haskey(dl, y)
    y *= x
    i += 1
    @assert i <= p
  end
  #OK: we know x^i = g^dl[y] (we don't know g)
  v = dl[y]
  g = gcd(p, i)
  r = div(p, g)
  @assert v % g == 0
  e = invmod(div(i, g), r)*div(v, g) % r
  if e == 0
    e = r
  end
  dl[x] = e
  y = x*x
  f = (e*2) % p
  while !isone(y)
    if haskey(dl, y)
      @assert dl[y] == f
    end
    dl[y] = f
    y *= x
    f = (f+e) % p
  end
  g = [ a for (a,b) = dl if b == 1]
  @assert length(g) == 1
  @assert g[1]^dl[x] == x
  return dl[x]
end

function Hecke.matrix(R::Hecke.Ring, M::MatElem)
  return matrix(R, nrows(M), ncols(M), elem_type(R)[R(M[i,j]) for i=1:nrows(M) for j=1:ncols(M)])
end

function mod_p(R, Q::NfOrdIdl, p::Int, T)
  Zk = order(Q)
  F, mF = Hecke.ResidueFieldSmallDegree1(Zk, Q)
  mF1 = Hecke.extend_easy(mF, number_field(Zk))
  @assert size(F) % p == 1
  pp, e = Hecke.ppio(Int(size(F)-1), p)
  dl = Dict{elem_type(F), Int}()
  dl[F(1)] = 0
  lp = factor(p)
  while true
    x = rand(F)
    if iszero(x)
      continue
    end
    x = x^e
    if any(i-> x^div(pp, Int(i)) == 1, keys(lp.fac))
      continue
    else
      dlog(dl, x, pp)
      @assert length(dl) == pp
      break
    end
  end
  return matrix(T, 1, length(R), Int[dlog(dl, image(mF1, x, pp)^e, pp) % p for x = R])
end

function mod_p(R, Q::NfOrdIdl, p::Int, T, D::Vector, cached::Bool)
  Zk = order(Q)
  F, mF = Hecke.ResidueFieldSmallDegree1(Zk, Q)
  mF1 = Hecke.extend_easy(mF, number_field(Zk))
  @assert size(F) % p == 1
  pp, e = Hecke.ppio(Int(size(F)-1), p)
  dl = Dict{elem_type(F), Int}()
  dl[F(1)] = 0
  lp = factor(p)
  while true
    x = rand(F)
    if iszero(x)
      continue
    end
    x = x^e
    if any(i-> x^div(pp, Int(i)) == 1, keys(lp.fac))
      continue
    else
      dlog(dl, x, pp)
      @assert length(dl) == pp
      break
    end
  end
  return matrix(T, 1, length(R), Int[dlog(dl, image(mF1, R[i], D[i], cached, pp)^e, pp) % p for i in 1:length(R)])
end

Hecke.lift(A::fmpz_mat) = A

#= idea
  let G = <a_1, ... a_n> and p a prime
    for prime ideals Q s.th. N(Q) = 1 (p) we do
        log_Q(a_i)
        nullspace() to get comb. that looks locally like an p-th power
        change a_i
=#

function lift_nonsymmetric(a::nmod_mat)
  z = fmpz_mat(nrows(a), ncols(a))
  z.base_ring = FlintZZ
  ccall((:fmpz_mat_set_nmod_mat_unsigned, Hecke.libflint), Nothing,
          (Ref{fmpz_mat}, Ref{nmod_mat}), z, a)
  return z
end

function lift_nonsymmetric(a::gfp_mat)
  z = fmpz_mat(nrows(a), ncols(a))
  z.base_ring = FlintZZ
  ccall((:fmpz_mat_set_nmod_mat_unsigned, Hecke.libflint), Nothing,
          (Ref{fmpz_mat}, Ref{gfp_mat}), z, a)
  return z
end

function saturate_exp_normal(c::Hecke.ClassGrpCtx, p::Int, stable = 1.5)
  ZK = order(c.FB.ideals[1])
  T, mT = torsion_unit_group(ZK)
  sT = Int(order(T))

  R = vcat(c.R_gen, c.R_rel)
  K = nf(ZK)
  zeta = mT(T[1])
  if gcd(sT, p) != 1 && !(hash(zeta) in c.RS) # && order is promising...
    push!(R, K(zeta))
#  else
#    println("NOT doint zeta")
  end
  T = GF(p, cached = false)
  A = identity_matrix(T, length(R))
  cA = ncols(A)
  i = 1

  S = Hecke.PrimesSet(Hecke.p_start, -1, Int(p), 1)

  D = Vector{Vector{gfp_poly}}(undef, length(R))
  for i in 1:length(R)
    D[i] = Vector{gfp_poly}(undef, R[i] isa FacElem ? length(R[i].fac) : 1)
  end

  for q in S
    @vprint :Saturate 3 "Finding primes for saturation: $i/$(stable*ncols(A))\n"
    if isdefining_polynomial_nice(K) && isindex_divisor(ZK, q)
      continue
    end
    if discriminant(ZK) % q == 0
      continue
    end
    #if gcd(div(q-1, Int(pp)), pp) > 1 # not possible if cond(k) is involved
    #  continue
    #end
    @vtime :Saturate 3 lq = prime_decomposition(ZK, q, 1)
    if length(lq) == 0
      continue
    end

    first_prime = true

    for Q in lq
      try
        if first_prime
          @vtime :Saturate 3 z = mod_p(R, Q[1], Int(p), T, D, false)
          first_prime = false
        else
          @vtime :Saturate 3 z = mod_p(R, Q[1], Int(p), T, D, true)
        end
        zz = mod_p(R, Q[1], Int(p), T)
        findfirst(i -> !iszero(z[i]), 1:length(z))
        @assert !iszero(zz[i])
        scalar = divexact(zz[i], z[i])
        @assert scalar * z == zz
        z = z*A
        rrz, z = nullspace(z)
        if iszero(rrz)
          return zero_matrix(FlintZZ, 0, length(R))
        end
        A = A*sub(z, 1:nrows(z), 1:rrz)
        # TODO: Remove or understand the following condition
        if false && cA == ncols(A)
          break #the other ideals are going to give the same info
                #for multi-quad as the field is normal
        end        
      catch e
        if !isa(e, Hecke.BadPrime)
          rethrow(e)
        end
      end
    end
    if cA == ncols(A) 
      i += 1
    else
      i = 0
      cA = ncols(A)
    end
    if i> stable*ncols(A)
      break
    end
  end
  return lift_nonsymmetric(A)
end

function saturate_exp(c::Hecke.ClassGrpCtx, p::Int, stable = 1.5)
  ZK = order(c.FB.ideals[1])
  T, mT = torsion_unit_group(ZK)
  sT = Int(order(T))

  R = vcat(c.R_gen, c.R_rel)
  K = nf(ZK)
  zeta = mT(T[1])
  if gcd(sT, p) != 1 && !(hash(zeta) in c.RS) # && order is promising...
    push!(R, K(zeta))
#  else
#    println("NOT doint zeta")
  end
  T = GF(p, cached = false)
  A = identity_matrix(T, length(R))
  cA = ncols(A)
  i = 1

  S = Hecke.PrimesSet(Hecke.p_start, -1, Int(p), 1)

  for q in S
    @vprint :Saturate 3 "Finding primes for saturation: $i/$(stable*ncols(A))\n"
    if isdefining_polynomial_nice(K) && isindex_divisor(ZK, q)
      continue
    end
    if discriminant(ZK) % q == 0
      continue
    end
    #if gcd(div(q-1, Int(pp)), pp) > 1 # not possible if cond(k) is involved
    #  continue
    #end
    @vtime :Saturate 3 lq = prime_decomposition(ZK, q, 1)
    if length(lq) == 0
      continue
    end

    for Q in lq
      try
        @vtime :Saturate 3 z = mod_p(R, Q[1], Int(p), T)
        z = z*A
        rrz, z = nullspace(z)
        if iszero(rrz)
          return zero_matrix(FlintZZ, 0, length(R))
        end
        A = A*sub(z, 1:nrows(z), 1:rrz)
        # TODO: Remove or understand the following condition
        if false && cA == ncols(A)
          break #the other ideals are going to give the same info
                #for multi-quad as the field is normal
        end        
      catch e
        if !isa(e, Hecke.BadPrime)
          rethrow(e)
        end
      end
    end
    if cA == ncols(A) 
      i += 1
    else
      i = 0
      cA = ncols(A)
    end
    if i> stable*ncols(A)
      break
    end
  end
  return lift_nonsymmetric(A)
end

fe(a::FacElem) = a
fe(a::nf_elem) = FacElem(a)

function elems_from_sat(c::Hecke.ClassGrpCtx, z)
  res = []#Tuple{FacElem{nf_elem, AnticNumberField}, }[]
  for i=1:ncols(z)
    a = fe(c.R_gen[1])^FlintZZ(z[1, i])
    b = FlintZZ(z[1, i]) * c.M.bas_gens[1]
    for j=2:length(c.R_gen)
      a *= fe(c.R_gen[j])^FlintZZ(z[j, i])
      b += FlintZZ(z[j, i]) * c.M.bas_gens[j]
    end
    for j=1:length(c.R_rel)
      a *= fe(c.R_rel[j])^FlintZZ(z[j + length(c.R_gen), i])
      b += FlintZZ(z[j + length(c.R_gen), i]) * c.M.rel_gens[j]
    end
    push!(res, (a, b))
  end
  return res
end

function saturate!(d::Hecke.ClassGrpCtx, U::Hecke.UnitGrpCtx, n::Int, stable = 3.5)
  @assert isprime(n)
  @vtime :Saturate 1 c = simplify(d, U) 
  success = false
  while true
    @vprint :Saturate 1 "Computing candidates for the saturation ...\n"
    @vtime :Saturate 1 e = saturate_exp(c, n, stable)
    if nrows(e) == 0
      @vprint :Saturate 1  "sat yielded nothing new at $stable, $success, \n"
      return success
    end
    se = sparse_matrix(e)'

    A = sparse_matrix(FlintZZ)
    K = nf(c)
    t, mt = torsion_unit_group(maximal_order(K))
    zeta = K(mt(t[1]))

    @vprint :Saturate 1 "sat: (Hopefully) enlarging by $(ncols(e)) elements\n"

    wasted = false
    for i=1:ncols(e)
      r = e[:, i]
      @assert content(r) == 1
      a = FacElem(K(1))
      fac_a = SRow(FlintZZ)
      for j = 1:length(c.R_gen)
        if !iszero(r[j, 1])
          mul!(a, a, fe(c.R_gen[j])^r[j, 1])
          fac_a += r[j, 1] * c.M.bas_gens[j]
        end
      end
      for j=1:length(c.R_rel)
        if !iszero(r[j + length(c.R_gen), 1])
          mul!(a, a, fe(c.R_rel[j])^r[j + length(c.R_gen), 1])
          fac_a += r[j + length(c.R_gen), 1] * c.M.rel_gens[j]
        end
      end
      if nrows(e) > length(c.R_gen) + length(c.R_rel) && !iszero(r[nrows(e), 1])
        @assert length(c.R_gen) + length(c.R_rel) + 1 == nrows(e)
        a *= fe(zeta)^r[nrows(e), 1]
      end
      
      decom = Dict((c.FB.ideals[k], v) for (k,v) = fac_a)
      @vprint :Saturate 1 "Testing if element is an n-th power\n"
      
      
      @vtime :Saturate 1 fl, x = ispower(a, n, decom = decom)
      if fl
        @assert isa(x, FacElem)
        success = true
        fac_a = divexact(fac_a, n)
        Hecke.class_group_add_relation(d, x, fac_a)
        @vprint :Saturate 1  "sat added new relation\n"
        if iszero(fac_a) #to make sure the new unit is used!
          #find units can be randomised...
          #maybe that should also be addressed elsewhere
          @vprint :Saturate 2  "sat added new unit\n"
          Hecke._add_dependent_unit(U, x)
        end
      else
        
        @vprint :Saturate 2  "sat wasted time, local power wasn't global\n"
        wasted = true
      end
    end
    if wasted 
      stable *= 2
    else
      @vprint :Saturate  1 "sat success at $(stable)\n"
      return success
    end
  end
end

function simplify(c::Hecke.ClassGrpCtx, U::Hecke.UnitGrpCtx)
  d = Hecke.class_group_init(c.FB, SMat{fmpz}, add_rels = false)

  Hecke.module_trafo_assure(c.M)
  trafos = c.M.trafo
 
  for i=1:length(c.FB.ideals)
    c.M.basis.rows[i].values[1] == 1 && continue
    @assert all(x -> x > 0, c.M.basis.rows[i].values)
    x = zeros(fmpz, length(c.R_gen) + length(c.R_rel))
    x[i] = 1
    for j in length(trafos):-1:1
      Hecke.apply_right!(x, trafos[j])
    end
    y = FacElem(vcat(c.R_gen, c.R_rel), x)
    fl = Hecke.class_group_add_relation(d, y, deepcopy(c.M.basis.rows[i]))
    @assert fl
  end
  for i=1:length(U.units)  
    Hecke.class_group_add_relation(d, U.units[i], SRow(FlintZZ))
  end
  return d
end

end
