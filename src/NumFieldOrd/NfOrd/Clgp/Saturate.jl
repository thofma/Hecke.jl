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


function compute_candidates_for_saturate(v::Vector{FacElem{nf_elem, AnticNumberField}}, p::Int, stable::Float64 = 1.5)
  K = base_ring(v[1])
  OK = maximal_order(K)
  zeta, sT = Hecke.torsion_units_gen_order(K)
  v1 = FacElem{nf_elem, AnticNumberField}[_mod_exponents(x, p) for x in v]
  if gcd(sT, p) != 1
    push!(v1, FacElem(zeta))
  end

  T = GF(p, cached = false)
  cA = length(v1)
  A = identity_matrix(T, cA)

  S = Hecke.PrimesSet(Hecke.p_start, -1, p, 1)

  D = Vector{Vector{gfp_poly}}(undef, length(v1))
  for i in 1:length(v1)
    D[i] = Vector{gfp_poly}(undef, length(v1[i].fac))
  end
  dK = discriminant(OK)
  threshold = stable*ncols(A)

  i = 1
  for q in S
    @vprint :Saturate 3 "Finding primes for saturation: $i/$(threshold)\n"
    if is_defining_polynomial_nice(K) && is_index_divisor(OK, q)
      continue
    end
    if iszero(dK % q)
      continue
    end
    @vtime :Saturate 3 lq = prime_decomposition(OK, q, 1)
    if isempty(lq)
      continue
    end

    first_prime = true
    for Q in lq
      try
        if first_prime
          @vtime :Saturate 3 z = mod_p(v1, Q[1], Int(p), T, D, false)
          first_prime = false
        else
          @vtime :Saturate 3 z = mod_p(v1, Q[1], Int(p), T, D, true)
        end
        z = z*A
        rrz, z = nullspace(z)
        if iszero(rrz)
          return zero_matrix(FlintZZ, 0, length(v1))
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


function compute_candidates_for_saturate1(c::Hecke.ClassGrpCtx, p::Int, stable::Float64 = 1.5)
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

  dK = discriminant(ZK)
  threshold = stable*ncols(A)

  f = K.pol
  att = 1

  #evals will contain at the same time all the evaluations at the prime ideals
  #of every element in R
  evals = Vector{Vector{Hecke.gfp_elem}}(undef, length(R))
  for i = 1:length(evals)
    evals[i] = Vector{Hecke.gfp_elem}(undef, degree(K))
  end

  evaluateat = Vector{Hecke.gfp_elem}(undef, degree(K))
  for q in S
    @vprint :Saturate 3 "Finding primes for saturation: $att/$(threshold)\n"
    if is_defining_polynomial_nice(K) && is_index_divisor(ZK, q)
      continue
    end
    if iszero(dK % q)
      continue
    end

    F = GF(q, cached = false)
    Fx, x = PolynomialRing(F, "x", cached = false)
    fF = Fx(f)
    g = gcd(fF, powermod(x, q, fF)-x)
    if isone(g)
      continue
    end
    facts = Hecke.factor_equal_deg(g, 1)
    lfacts = length(facts)
    #I take the evaluation points...
    for i = 1:lfacts
      evaluateat[i] = -coeff(facts[i], 0)
    end

    #Now, I evaluate the elements.
    bad_prime = false
    t = Fx()
    for i = 1:length(R)
      isfirst = true
      for (k, v) in R[i]
        if !is_coprime(denominator(k), q)
          bad_prime = true
          break
        end
        Hecke.nf_elem_to_gfp_poly!(t, k)
        #evaluations = evaluate(t, evaluateat[1:lfacts])
        for j = 1:lfacts
          ev_t = evaluate(t, evaluateat[j])#evaluations[j]
          if isone(ev_t)
            continue
          end
          if isfirst
            if isone(v)
              evals[i][j] = ev_t
            else
              evals[i][j] = ev_t^Int(v)
            end
          else
            if isone(v)
              evals[i][j] = mul!(evals[i][j], evals[i][j], ev_t)
            else
              evals[i][j] = mul!(evals[i][j], evals[i][j], ev_t^Int(v))
            end
          end
        end
        isfirst = false
      end
      if bad_prime
        break
      end
    end
    if bad_prime
      continue
    end
    #Prepare the disc log dictionary
    disc_log = Dict{Hecke.gfp_elem, Hecke.gfp_elem}()
    disc_log[F(1)] = zero(T)
    pp, e = ppio(q-1, p)
    exp_to_test = divexact(pp, p)
    elF = rand(F)
    while true
      if iszero(elF)
        continue
      end
      elF = elF^e
      if !isone(elF^exp_to_test)
        break
      end
      elF = rand(F)
    end
    y = elF
    for i = 1:pp-1
      disc_log[y] = T(i)
      y *= elF
    end
    #The disc log dictionary is ready. Now we need the subspace.
    for i = 1:lfacts
      z = matrix(T, 1, length(R), Hecke.gfp_elem[disc_log[evals[j][i]^e] for j = 1:length(R)])
      z = z*A
      rrz, z = nullspace(z)
      if iszero(rrz)
        return zero_matrix(FlintZZ, 0, length(R))
      end
      A = A*sub(z, 1:nrows(z), 1:rrz)
      if cA == ncols(A)
        att += 1
      else
        att = 0
        cA = ncols(A)
      end
      if att > threshold
        break
      end
    end
    if att > threshold
      break
    end
  end
  return Hecke.lift_nonsymmetric(A)
end

function _get_element(e, R, R_mat, zeta, i)
  K = parent(zeta)
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
    Hecke.add_to_key!(a.fac, zeta, e[nrows(e), i])
  end
  return a, fac_a
end


function saturate!(U::Hecke.UnitGrpCtx, n::Int, stable::Float64 = 3.5; use_orbit::Bool = false, easy_root::Bool = false, use_LLL::Bool = false)
  @assert is_prime(n)
  O = order(U)
  K = nf(O)
  success = false
  restart = false
  decom = Dict{NfOrdIdl, fmpz}()
  while true
    @vprint :Saturate 1 "Computing candidates for the saturation\n"
    R = U.units
    @vtime :Saturate 1 e = compute_candidates_for_saturate(R, n, stable)
    if nrows(e) == 0
      @vprint :Saturate 1 "sat yielded nothing new at $stable, $success \n"
      return success
    end
    zeta = Hecke.torsion_units_generator(K)
    @vprint :Saturate 1 "(Hopefully) enlarging by $(ncols(e)) elements\n"

    wasted = false
    for i = ncols(e):-1:1
      a  = FacElem(one(K))
      for j = 1:length(R)
        if !iszero(e[j, i])
          mul!(a, a, R[j]^e[j, i])
        end
      end
      if nrows(e) > length(R) && !iszero(e[nrows(e), i])
        @assert length(R) + 1 == nrows(e)
        Hecke.add_to_key!(a.fac, zeta, e[nrows(e), i])
      end
      @vprint :Saturate 1 "Testing if element is an n-th power\n"
      @vtime :Saturate 1 fl, x = is_power(a, n, decom = decom, easy = easy_root)
      if fl
        @vprint :Saturate 1  "The element is an n-th power\n"
        success = true
        Hecke._add_dependent_unit!(U, x)
      else
        @vprint :Saturate 1  "The element is not an n-th power\n"
        wasted = true
        break
      end
    end
    if restart
      restart = false
      continue
    elseif wasted
      stable *= 2
    else
      @vprint :Saturate  1 "sat success at $(stable)\n"
      return success
    end
  end
end

function saturate!(d::Hecke.ClassGrpCtx, U::Hecke.UnitGrpCtx, n::Int, stable::Float64 = 3.5; use_orbit::Bool = false, easy_root::Bool = false, use_LLL::Bool = false)
  @assert is_prime(n)
  K = nf(U)
  @vprint :Saturate 1 "Simplifying the context\n"
  @vtime :Saturate 1 c = simplify(d, U, n, use_LLL = use_LLL)
  success = false
  restart = false
  while true
    if success
      @vprint :Saturate 1 "Simplifying the context\n"
      @vtime :Saturate 1 c = simplify(d, U, n, use_LLL = use_LLL)
    end
    @vprint :Saturate 1 "Computing candidates for the saturation\n"
    R = relations(c)
    @vtime :Saturate 1 e = compute_candidates_for_saturate(R, n, stable)
    if nrows(e) == 0
      @vprint :Saturate 1 "sat yielded nothing new at $stable, $success \n"
      return success
    end
    zeta = Hecke.torsion_units_generator(K)
    @vprint :Saturate 1 "(Hopefully) enlarging by $(ncols(e)) elements\n"

    rels_added = sparse_matrix(FlintZZ)
    R_mat = relations_matrix(c)
    wasted = false
    for i = ncols(e):-1:1
      a, fac_a = _get_element(e, R, R_mat, zeta, i)
      if !iszero(fac_a) && nrows(rels_added) > 0
        candidate_rel = divexact(fac_a, n)
        red_candidate = reduce(rels_added, candidate_rel)
        if iszero(red_candidate)
          @vprint :Saturate 1 "Ignore this relation! \n"
          continue
        end
      end

      decom = Dict{NfOrdIdl, fmpz}((c.FB.ideals[k], v) for (k, v) = fac_a)
      @vprint :Saturate 1 "Testing if element is an n-th power\n"
      @vtime :Saturate 1 fl, x = is_power(a, n, decom = decom, easy = easy_root)
      if fl
        @vprint :Saturate 1  "The element is an n-th power\n"
        success = true
        fac_a = divexact(fac_a, n)
        if iszero(fac_a)
          #In this case, the element we have found is a unit and
          #we want to make sure it is used
          #find units can be randomised...
          #maybe that should also be addressed elsewhere
          @vprint :Saturate 1  "The new element is a unit\n"

          if use_orbit
            auts_action = Hecke._get_autos_from_ctx(d)
            for s = 1:length(auts_action)
              new_u = auts_action[s][1](x)
              Hecke._add_dependent_unit!(U, new_u)
            end
            restart = true
            break
          else
            Hecke._add_dependent_unit!(U, x)
          end
        else
          @vprint :Saturate 1  "The new element gives a relation\n"
          Hecke.class_group_add_relation(d, x, fac_a)
          if use_orbit
            #We add the relation to the matrix and compute the snf
            auts_action = Hecke._get_autos_from_ctx(d)
            for s = 1:length(auts_action)
              push!(rels_added, Hecke.permute_row(fac_a, auts_action[s][2]))
            end
            rels_added = hnf(rels_added, truncate = true)
            restart = true
          end
        end
      else
        @vprint :Saturate 1  "The element is not an n-th power\n"
        wasted = true
        break
      end
    end
    if restart
      restart = false
      continue
    elseif wasted
      stable *= 2
    else
      @vprint :Saturate  1 "sat success at $(stable)\n"
      return success
    end
  end
end

function simplify(c::Hecke.ClassGrpCtx, U::Hecke.UnitGrpCtx, cp::Int = 0; use_LLL::Bool = false)

  d = Hecke.class_group_init(c.FB, SMat{fmpz}, add_rels = false)
  Hecke.module_trafo_assure(c.M)
  trafos = c.M.trafo
  R = relations(c)
  R_mat = relations_matrix(c)

  new_rels = Vector{FacElem{nf_elem, AnticNumberField}}()
  vals_new_rels = Vector{SRow{fmpz}}()
  @vprint :Saturate 1 "Computing rels...\n"
  for i=1:length(c.FB.ideals)
    if cp != 0 && isone(c.M.basis.rows[i].values[1])
      continue
    end
    @assert all(x -> x > 0, c.M.basis.rows[i].values)
    x = zeros(fmpz, length(R))
    x[i] = 1
    for j in length(trafos):-1:1
      Hecke.apply_right!(x, trafos[j])
    end
    y = R[1]^x[1]
    for j = 2:length(R)
      if !iszero(x[j])
        mul!(y, y, R[j]^x[j])
      end
    end
    push!(new_rels, y)
    push!(vals_new_rels, deepcopy(c.M.basis.rows[i]))
  end
  if use_LLL && !isempty(new_rels)
    M = sparse_matrix(FlintZZ)
    for x in vals_new_rels
      push!(M, x)
    end
    M1 = matrix(M)
    M2, T = lll_with_transform(M1)
    transpose!(T, T)
    new_rels = transform(new_rels, T)
    for i = 1:length(vals_new_rels)
      vals_new_rels[i] = sparse_row(view(M2, i:i, 1:ncols(M2)))
    end
  end
  @vprint :Saturate 1 "Reducing rels...\n"
  if !isempty(new_rels)
    @vtime :Saturate 1 new_rels = Hecke.reduce_mod_units(new_rels, U)
    for i = 1:length(new_rels)
      fl = Hecke.class_group_add_relation(d, new_rels[i], vals_new_rels[i])
      @assert fl
    end
  end
  for i=1:length(U.units)
    Hecke.class_group_add_relation(d, U.units[i], SRow(FlintZZ))
  end
  return d
end

end
