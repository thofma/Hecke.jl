module RelSaturate
using Hecke

Hecke.add_verbose_scope(:Saturate)

export saturate!

function mod_p(R::Vector{FacElem{nf_elem, AnticNumberField}}, Q::NfOrdIdl, p::Int, T::Hecke.GaloisField, D::Vector, cached::Bool)
  Zk = order(Q)
  F, mF = Hecke.ResidueFieldSmallDegree1(Zk, Q)
  mF1 = Hecke.extend_easy(mF, number_field(Zk))
  oF = Int(size(F))-1
  @assert iszero(oF % p)
  pp, e = Hecke.ppio(oF, p)
  #We now want the discrete logarithm of the images of the elements of R in F
  #We don't need the full group, just the quotient by p
  #We compute a generator and cache the powers in dl
  #Then we will compute the discrete logarithms by checking the values in dl
  dl = Dict{Hecke.Nemo.gfp_elem, Int}()
  dl[F(1)] = 0
  exp_to_test = divexact(pp, p)
  x = rand(F)
  while true
    if iszero(x)
      continue
    end
    x = x^e
    if !isone(x^exp_to_test)
      break
    end
    x = rand(F)
  end
  y = x
  for i = 1:pp-1
    dl[y] = i
    y *= x
  end 
  return matrix(T, 1, length(R), Int[dl[image(mF1, R[i], D[i], cached, pp)^e] % p for i in 1:length(R)])
end

#= idea
  let G = <a_1, ... a_n> and p a prime
    for prime ideals Q s.th. N(Q) = 1 (p) we do
        log_Q(a_i)
        nullspace() to get comb. that looks locally like an p-th power
        change a_i
=#

function _mod_exponents(a::FacElem{nf_elem, AnticNumberField}, p::Int)
  pU = UInt(p)
  a1 = copy(a.fac)
  for i = a1.idxfloor:length(a1.vals)
    if a1.slots[i] == 0x01
      new_e = Hecke.fmpz_mod_ui(a1.vals[i], pU)
      if iszero(new_e)
        a1.slots[i] = 0x00
        a1.count -= 1
      else
        a1.vals[i] = new_e
      end
    end
  end
  if isempty(a1)
    #TODO: If this happens, I already have a square!
    #Should take care of this before starting with this part of code.
    K = base_ring(parent(a))
    return FacElem(one(K))
  end
  return FacElem(a1)
end

function relations(c::Hecke.ClassGrpCtx)
  v = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(c.R_gen) + length(c.R_rel))
  for i = 1:length(c.R_gen)
    if typeof(c.R_gen[i]) == nf_elem
      v[i] = FacElem(c.R_gen[i])
    else
      v[i] = c.R_gen[i]
    end
  end
  for i = 1:length(c.R_rel)
    if typeof(c.R_rel[i]) == nf_elem
      v[i+length(c.R_gen)] = FacElem(c.R_rel[i])
    else
      v[i+length(c.R_gen)] = c.R_rel[i]
    end
  end
  return v
end

function relations_mod_powers(c::Hecke.ClassGrpCtx, p::Int)
  v = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(c.R_gen) + length(c.R_rel))
  for i = 1:length(c.R_gen)
    if typeof(c.R_gen[i]) == nf_elem
      v[i] = FacElem(c.R_gen[i])
    else
      v[i] = _mod_exponents(c.R_gen[i], p)
    end
  end
  for i = 1:length(c.R_rel)
    if typeof(c.R_rel[i]) == nf_elem
      v[i+length(c.R_gen)] = FacElem(c.R_rel[i])
    else
      v[i+length(c.R_gen)] = _mod_exponents(c.R_rel[i], p)
    end
  end
  return v
end

function relations_matrix(c::Hecke.ClassGrpCtx)
  v = Vector{SRow{fmpz}}(undef, length(c.R_gen) + length(c.R_rel))
  for i = 1:length(c.R_gen)
    v[i] = c.M.bas_gens[i]
  end
  for i = 1:length(c.R_rel)
    v[i+length(c.R_gen)] = c.M.rel_gens[i]
  end
  return v
end

function compute_candidates_for_saturate(c::Hecke.ClassGrpCtx, p::Int, stable::Float64 = 1.5)
  ZK = order(c.FB.ideals[1])
  K = nf(ZK)
  zeta, sT = Hecke.torsion_units_gen_order(K)

  @vprint :Saturate 3 "Reducing exponents\n"
  R = relations_mod_powers(c, p)
  if gcd(sT, p) != 1 && !(hash(zeta) in c.RS) # && order is promising...
    push!(R, FacElem(zeta))
  end
  @vprint :Saturate 3 "Done\n"

  T = GF(p, cached = false)
  cA = length(R)
  A = identity_matrix(T, cA)
  
  S = Hecke.PrimesSet(Hecke.p_start, -1, p, 1)

  D = Vector{Vector{gfp_poly}}(undef, length(R))
  for i in 1:length(R)
    D[i] = Vector{gfp_poly}(undef, length(R[i].fac))
  end
  dK = discriminant(ZK) 
  threshold = stable*ncols(A)

  i = 1
  for q in S
    @vprint :Saturate 3 "Finding primes for saturation: $i/$(threshold)\n"
    if isdefining_polynomial_nice(K) && isindex_divisor(ZK, q)
      continue
    end
    if iszero(dK % q)
      continue
    end
    @vtime :Saturate 3 lq = prime_decomposition(ZK, q, 1)
    if isempty(lq)
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
        z = z*A
        rrz, z = nullspace(z)
        if iszero(rrz)
          return zero_matrix(FlintZZ, 0, length(R))
        end
        A = A*sub(z, 1:nrows(z), 1:rrz)
        if cA == ncols(A) 
          i += 1
        else
          i = 0
          cA = ncols(A)
        end
        if i > threshold
          break
        end
      catch e
        if !isa(e, Hecke.BadPrime)
          rethrow(e)
        end
      end
    end
    if i > threshold
      break
    end
  end
  return Hecke.lift_nonsymmetric(A)
end

function saturate!(d::Hecke.ClassGrpCtx, U::Hecke.UnitGrpCtx, n::Int, stable::Float64 = 3.5)
  @assert isprime(n)
  K = nf(d)
  @vprint :Saturate 1 "Simplifying the context\n"
  @vtime :Saturate 1 c = simplify(d, U)
  success = false
  while true
    if success
      @vprint :Saturate 1 "Simplifying the context\n"
      @vtime :Saturate 1 c = simplify(d, U)
    end
    @vprint :Saturate 1 "Computing candidates for the saturation\n"
    @vtime :Saturate 1 e = compute_candidates_for_saturate(c, n, stable)
    if nrows(e) == 0
      @vprint :Saturate 1 "sat yielded nothing new at $stable, $success \n"
      return success
    end
    zeta = Hecke.torsion_units_generator(K)
    @vprint :Saturate 1 "(Hopefully) enlarging by $(ncols(e)) elements\n"

    R = relations(c)
    R_mat = relations_matrix(c)
    wasted = false
    for i = 1:ncols(e)
      a = FacElem(K(1))
      fac_a = SRow(FlintZZ)
      for j = 1:length(R)
        if !iszero(e[j, i])
          mul!(a, a, R[j]^e[j, i])
          fac_a += e[j, i] * R_mat[j]
        end
      end
      if nrows(e) > length(R) && !iszero(e[nrows(e), i])
        @assert length(R) + 1 == nrows(e)
        mul!(a, a, FacElem(nf_elem[zeta], fmpz[e[nrows(e), i]]))
      end
      
      decom = Dict{NfOrdIdl, fmpz}((c.FB.ideals[k], v) for (k, v) = fac_a)
      @vprint :Saturate 1 "Testing if element is an n-th power\n"
      @vtime :Saturate 1 fl, x = ispower(a, n, decom = decom)
      if fl
        @vprint :Saturate 1  "The element is an n-th power\n"
        success = true
        fac_a = divexact(fac_a, n)
        Hecke.class_group_add_relation(d, x, fac_a)
        if iszero(fac_a) 
          #In this case, the element we have found is a unit and
          #we want to make sure it is used
          #find units can be randomised...
          #maybe that should also be addressed elsewhere
          @vprint :Saturate 2  "sat added new unit\n"
          Hecke._add_dependent_unit(U, x)
        end
      else
        @vprint :Saturate 1  "The element is not an n-th power\n"
        wasted = true
        break
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
 
  R = relations(c)
  for i=1:length(c.FB.ideals)
    c.M.basis.rows[i].values[1] == 1 && continue
    @assert all(x -> x > 0, c.M.basis.rows[i].values)
    x = zeros(fmpz, length(R))
    x[i] = 1
    for j in length(trafos):-1:1
      Hecke.apply_right!(x, trafos[j])
    end
    y = R[1]^x[1]
    for j = 2:length(R)
      mul!(y, y, R[j]^x[j])
    end
    fl = Hecke.class_group_add_relation(d, y, deepcopy(c.M.basis.rows[i]))
    @assert fl
  end
  for i=1:length(U.units)  
    Hecke.class_group_add_relation(d, U.units[i], SRow(FlintZZ))
  end
  return d
end

end


#=
OLD CODE:


function saturate_exp(c::Hecke.ClassGrpCtx, p::Int, stable = 1.5)
  return saturate_exp_normal(c, p, stable)
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
    if i > stable*ncols(A)
      break
    end
  end
  return lift_nonsymmetric(A)
end


fe(a::FacElem{nf_elem, AnticNumberField}) = a
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


function mod_p(R, Q::NfOrdIdl, p::Int, T::Hecke.GaloisField)
  Zk = order(Q)
  F, mF = Hecke.ResidueFieldSmallDegree1(Zk, Q)
  mF1 = Hecke.extend_easy(mF, number_field(Zk))
  oF = Int(size(F)-1)
  @assert iszero(oF % p)
  pp, e = Hecke.ppio(oF, p)
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
=#