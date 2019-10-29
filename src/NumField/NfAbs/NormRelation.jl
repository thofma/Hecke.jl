################################################################################
#
#  (Generalized) norm relations
#
################################################################################

add_verbose_scope(:NormRelation)
add_assert_scope(:NormRelation)

# Example
# 
# julia> f = x^8+8*x^6+64*x^4-192*x^2+576
# x^8+8*x^6+64*x^4-192*x^2+576
# 
# julia> K, a = number_field(f);
# 
# julia> N  = Hecke._norm_relation_setup(K)
# Norm relation of
#   Number field over Rational Field with defining polynomial x^8+8*x^6+64*x^4-192*x^2+576
# of index 4 and the subfields
#   Number field over Rational Field with defining polynomial x^2+1
#   Number field over Rational Field with defining polynomial x^2-6
#   Number field over Rational Field with defining polynomial x^2-2
#   Number field over Rational Field with defining polynomial x^2+2
#   Number field over Rational Field with defining polynomial x^2+6
#   Number field over Rational Field with defining polynomial x^2-3
#   Number field over Rational Field with defining polynomial x^2-x+1
 
mutable struct NormRelation{T}
  K::AnticNumberField
  subfields::Vector{Tuple{AnticNumberField, NfToNfMor}}
  denominator::Int
  coefficients::Vector{Vector{Tuple{NfToNfMor, Int}}}
  ispure::Bool
  pure_coefficients::Vector{Int}
  isabelian::Bool
  isgeneric::Bool
  coefficients_gen::Vector{Vector{Tuple{Int, NfToNfMor, NfToNfMor}}}
  embed_cache::Dict{Tuple{Int, Int}, Dict{nf_elem, nf_elem}}
  mor_cache::Dict{NfToNfMor, Dict{nf_elem, nf_elem}}
  induced::Dict{NfToNfMor, Perm{Int}}
  embed_cache_triv::Vector{Dict{nf_elem, nf_elem}}

  function NormRelation{T}() where {T}
    z = new{T}()
    z.ispure = false
    z.isabelian = false
    z.isgeneric = false
    z.denominator = 0
    z.embed_cache = Dict{Tuple{Int, Int}, Dict{nf_elem, nf_elem}}()
    z.mor_cache = Dict{NfToNfMor, Dict{nf_elem, nf_elem}}()
    z.induced = Dict{NfToNfMor, Perm{Int}}()
    return z
  end
end

function Base.show(io::IO, N::NormRelation)
  print(io, "Norm relation of\n  ", N.K, "\nof index ", index(N), " and the subfields")
  for i in 1:length(N)
    print(io, "\n  ", subfields(N)[i][1])
  end
end

function Base.hash(x::AlgGrpElem, h::UInt)
  return Base.hash(x.coeffs, h)
end

function _norm_relation_setup_abelian(K::AnticNumberField; small_degree::Bool = true, pure::Bool = true, index::fmpz = zero(fmpz))
  G = automorphisms(K)
  A, GtoA, AtoG = find_isomorphism_with_abelian_group(G, *);
  if iszero(index)
    subs = [f for f in subgroups(A) if order(f[1]) > 1]
  else
    subs = [f for f in subgroups(A) if order(f[1]) > 1 && order(f[1]) == index || order(f[1]) == index^2]
  end

  b, den, ls = _has_norm_relation_abstract(A, subs, large_index = !small_degree, pure = pure)
  @assert b
  n = length(ls)

  z = NormRelation{Int}()
  z.K = K
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = false

  for i in 1:n
    F, mF = fixed_field(K, NfToNfMor[AtoG[f] for f in ls[i][2]])
    maximal_order(F)
    S, mS = simplify(F)
    L = S
    mL = mS * mF
    z.subfields[i] = L, mL
  end

  if pure
    z.ispure = true
    z.pure_coefficients = Vector{Int}(undef, n)
    for i in 1:n
      z.pure_coefficients[i] = ls[i][1]
    end
  else
    z.coefficients = Vector{Vector{Tuple{NfToNfMor, Int}}}(undef, n)
    for i in 1:n
      w = Vector{Tuple{NfToNfMor, Int}}(undef, length(ls[i][1]))
      for (j, (expo, auto)) in enumerate(ls[i][1])
        w[j] = (AtoG[auto], expo)
      end
      z.coefficients[i] = w
    end

  end

  z.isabelian = true

  return z
end

function _norm_relation_setup_generic(K::AnticNumberField; small_degree::Bool = true, pure::Bool = false, target_den::fmpz = zero(fmpz))
  A = automorphisms(K)
  G, AtoG, GtoA = generic_group(A, *)
  if iszero(target_den)
    b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(G, conjugacy_classes = true) if order(f[1]) > 1], pure = pure)
  else
    b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(G, conjugacy_classes = true) if order(f[1]) > 1], target_den = target_den, pure = pure)
  end

  @assert b
  n = length(ls)

  z = NormRelation{Int}()
  z.K = K
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = pure
  z.embed_cache_triv = Vector{Dict{nf_elem, nf_elem}}(undef, n)
  for i in 1:n
    z.embed_cache_triv[i] = Dict{nf_elem, nf_elem}()
  end
 
  for i in 1:n
    F, mF = fixed_field(K, NfToNfMor[GtoA[f] for f in ls[i][1]])
    S, mS = simplify(F, cached = true)
    L = S
    mL = mS * mF
    z.subfields[i] = L, mL
  end

  z.coefficients_gen = Vector{Vector{Tuple{Int, NfToNfMor, NfToNfMor}}}(undef, n)

  for i in 1:n
    w = Vector{Tuple{Int, NfToNfMor, NfToNfMor}}(undef, length(ls[i][2]))
    for (j, (expo, auto_pre, auto_post)) in enumerate(ls[i][2])
      w[j] = (expo, GtoA[auto_pre], GtoA[auto_post])
    end
    z.coefficients_gen[i] = w
  end

  z.isabelian = false

  return z
end

Base.length(N::NormRelation) = length(N.subfields)

field(N::NormRelation) = N.K

subfields(N::NormRelation) = N.subfields

subfield(N::NormRelation, i::Int) = N.subfields[i]

embedding(N::NormRelation, i::Int) = N.subfields[i][2]

index(N::NormRelation) = N.denominator

norm(N::NormRelation, i::Int, a) = norm(N.embeddings[i], a)

ispure(N::NormRelation) = N.ispure

function image(f::NfToNfMor, a::FacElem{nf_elem, AnticNumberField})
  D = Dict{nf_elem, fmpz}(f(b) => e for (b, e) in a)
  return FacElem(D)
end

function check_relation(N::NormRelation, a::nf_elem)
  @assert !iszero(a)
  if false#ispure(N)
    z = one(field(N))
    for i in 1:length(N)
      z = z * N(norm(embedding(N, i), a), i)
    end
    return a^index(N) == z
  else
    # I applied the exponent when embedding
    z = one(field(N))
    for i in 1:length(N)
      z = z * N([norm(embedding(N, i), auto(a)^exp) for  (exp, auto, _) in N.coefficients_gen[i]], i)
    end
    return a^index(N) == z
  end
end

function _apply_auto(N::NormRelation, auto::NfToNfMor, x::nf_elem)
  if haskey(N.mor_cache, auto)
    d = N.mor_cache[auto]
    if haskey(d, x)
      return d[x]
    else
      y = auto(x)
      d[x] = y
      return y
    end
  else
    d = Dict{nf_elem, nf_elem}()
    y = auto(x)
    d[x] = y
    N.mor_cache[auto] = d
    return y
  end
end

function (N::NormRelation)(x::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, i::Int, j::Int)
  @assert (1 <= j) && (j <= length(N.coefficients_gen[i]))
  if haskey(N.embed_cache, (i, j)) && haskey(N.embed_cache[i, j], x)
    return N.embed_cache[i, j][x]
  end

  _, mk = subfield(N, i)
  y = _apply_auto(N, mk, x)

  exp, _, auto = N.coefficients_gen[i][j]

  z = _apply_auto(N, auto, y)
  return z
end

function (N::NormRelation)(x::Vector{<:Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}, i::Int)
  @assert length(x) == length(N.coefficients_gen[i])
  z = one(N.K)
  for j in 1:length(N.coefficients_gen[i])
    z = z * N(x[j], i, j)
  end
  return z
end

################################################################################
#
#  Cheap induce action
#
################################################################################

function induce_action_from_subfield(N::NormRelation, i, s, FB, cache)
  S = FB.ideals
  ZK = order(S[1])

  z = SMat{fmpz}[zero_matrix(SMat, FlintZZ, 0, length(S)) for i in 1:degree(field(N))]

  mk = embedding(N, i)
  zk = order(s[1])
  
  if length(cache) == 0
    cache = resize!(cache, length(s))
    cached = false
  else
    cached = true
  end

  autos = automorphisms(field(N), copy = false)

  for auto in autos
    if haskey(N.induced, auto)
      p = N.induced[auto]
    else
      p = induce(FB, auto) 
      N.induced[auto] = p
    end
  end

  @assert mod(degree(ZK), degree(zk)) == 0
  reldeg = divexact(degree(ZK), degree(zk))

  for l in 1:length(s)
    if cached
      v = cache[l]
    else
      v = Tuple{Int, fmpz}[]
      P = s[l]
      genofsl = elem_in_nf(_apply_auto(N, mk, P.gen_two.elem_in_nf))
      pmin = minimum(P, copy = false)
      # Compute the number of ideals
      # Assume that L/K and L/Q are normal
      rele = divexact(ramification_index((FB.fb[pmin].lp)[1][2]), ramification_index(P))
      relf = divexact(degree((FB.fb[pmin].lp)[1][2]), degree(P))
      @assert mod(reldeg, rele * relf) == 0
      numb_ideal = divexact(reldeg, rele * relf)
      found = 0
      for k in 1:length(S)
        Q = S[k]
        if minimum(Q, copy = false) == pmin
          ant = anti_uniformizer(Q)
          if (genofsl * ant) in ZK
            found += 1
            @assert mod(ramification_index(Q), ramification_index(s[l])) == 0
            push!(v, (k, divexact(ramification_index(Q), ramification_index(s[l]))))
          end
        end
        if found == numb_ideal
          break
        end
      end
      cache[l] = v
    end

    # We still need to sort the positions of the non-zero entries
    #@show l, v
    sort!(v, by = x -> x[1])
    #@show l, v
    # Now apply the automorphism
    for i in 1:degree(field(N))
      p = N.induced[autos[i]]
      r = [(p[i], e) for (i, e) in v]
      sort!(r, lt = (a,b)->a[1]<b[1])
    #@show l, r
      push!(z[i], sparse_row(FlintZZ, r))
    end
  end

  #for l in 1:length(s)
  #  @show l
  #  a = uniformizer(s[l])
  #  @show [ valuation(a, Q) for Q in s]
  #  @show [ valuation(auto(mk(a.elem_in_nf)), Q) for Q in FB.ideals]
  #  @show [ z.rows[l][m] for m in 1:length(FB.ideals) ]
  #  @assert [ valuation(auto(mk(a.elem_in_nf)), Q) for Q in FB.ideals] == [ z.rows[l][m] for m in 1:length(FB.ideals) ]
  #end
  return z
end


function induce_action(N::NormRelation, i, j, s, FB, cache)
  S = FB.ideals
  ZK = order(S[1])
  z = zero_matrix(SMat, FlintZZ, 0, length(S))
  mk = embedding(N, i)
  zk = order(s[1])

  _ , _, auto = N.coefficients_gen[i][j]
  #@show auto
  println("Call to induce(FB, auto)...")
  if haskey(N.induced, auto)
    p = N.induced[auto]
  else
    p = induce(FB, auto)
    N.induced[auto] = p
  end
  #@show p

  if length(cache) == 0
    cache = resize!(cache, length(s))
    cached = false
  else
    cached = true
  end

  @show cached

  @assert mod(degree(ZK), degree(zk)) == 0
  reldeg = divexact(degree(ZK), degree(zk))

  for l in 1:length(s)
    if cached
      v = cache[l]
    else
      v = Tuple{Int, fmpz}[]
      P = s[l]
      genofsl = elem_in_nf(_apply_auto(N, mk, P.gen_two.elem_in_nf))
      pmin = minimum(P, copy = false)
      # Compute the number of ideals
      # Assume that L/K and L/Q are normal
      rele = divexact(ramification_index((FB.fb[pmin].lp)[1][2]), ramification_index(P))
      relf = divexact(degree((FB.fb[pmin].lp)[1][2]), degree(P))
      @assert mod(reldeg, rele * relf) == 0
      numb_ideal = divexact(reldeg, rele * relf)
      found = 0
      for k in 1:length(S)
        Q = S[k]
        if minimum(Q, copy = false) == pmin
          ant = anti_uniformizer(Q)
          if (genofsl * ant) in ZK
            found += 1
            @assert mod(ramification_index(Q), ramification_index(s[l])) == 0
            push!(v, (k, divexact(ramification_index(Q), ramification_index(s[l]))))
          end
        end
        if found == numb_ideal
          break
        end
      end
      cache[l] = v
    end

    # We still need to sort the positions of the non-zero entries
    @show l, v
    sort!(v, by = x -> x[1])
    #@show l, v
    # Now apply the automorphism
    r = [(p[i], e) for (i, e) in v]
    sort!(r, lt = (a,b)->a[1]<b[1])
    #@show l, r
    push!(z, sparse_row(FlintZZ, r))
  end

  #for l in 1:length(s)
  #  @show l
  #  a = uniformizer(s[l])
  #  @show [ valuation(a, Q) for Q in s]
  #  @show [ valuation(auto(mk(a.elem_in_nf)), Q) for Q in FB.ideals]
  #  @show [ z.rows[l][m] for m in 1:length(FB.ideals) ]
  #  @assert [ valuation(auto(mk(a.elem_in_nf)), Q) for Q in FB.ideals] == [ z.rows[l][m] for m in 1:length(FB.ideals) ]
  #end
  return z
end

function induce_action(N::NormRelation, i, s::Vector, S::Vector)
  if !ispure(N)
    throw(error("Not implemented yet"))
  end
  ZK = order(S[1])
  z = zero_matrix(SMat, FlintZZ, 0, length(S))
  mk = embedding(N, i)
  for j in 1:length(s)
    v = Tuple{Int, fmpz}[]
    for k in 1:length(S)
      Q = S[k]
      if minimum(Q, copy = false) == minimum(s[j], copy = false)
        ant = anti_uniformizer(Q)
        if (elem_in_nf(mk(s[j].gen_two.elem_in_nf)) * ant) in ZK
          push!(v, (k, divexact(ramification_index(Q), ramification_index(s[j]))))
        end
      end
    end

    # We still need to sort the positions of the non-zero entries
    sort!(v, by = x -> x[1])

    push!(z, N.pure_coefficients[i] * sparse_row(FlintZZ, v))
  end
  return z
end

function _setup_for_norm_relation_fun(K, S = prime_ideals_up_to(maximal_order(K), factor_base_bound_grh(maximal_order(K))))
  ZK = order(S[1])
  FB = NfFactorBase(ZK, S)
  c = class_group_init(FB)
  UZK = Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(ZK)
  return c, UZK
end

function _add_sunits_from_norm_relation!(c, UZK, N)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  for i = 1:length(N)
    k, mk = subfield(N, i)
    println("Computing maximal order ...")
    @time zk = maximal_order(k)
    println("Computing lll basis ... ")
    @show k
    @time zk = lll(zk)
    print("Computing class group of $k... ")
    @time class_group(zk, redo = !true, use_aut = true)
    println("done")
    lpk = NfOrdIdl[ P[1] for p in cp for P = prime_decomposition(zk, p)]
    println("Now computing the S-unit group for lp of length $(length(lpk))")
    @assert length(lpk) > 0
    @time Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)
#    @show length(N.coefficients_gen[i])

    D = Dict{nf_elem, nf_elem}()
    function N_mk(x, D, i)
      if haskey(D, x)
        return D[x]
      else
        y = N(x, i)
        D[x] = y
        return y
      end
    end


    #D = Dict{nf_elem, nf_elem}()
    cc = Vector{Tuple{Int, fmpz}}[]
    for j in 1:length(N.coefficients_gen[i])
      println("Inducing the action ... ")
      @time z = induce_action(N, i, j, lpk, c.FB, cc)

      print("Feeding in the S-units of the small field ... ")


      for l=1:ngens(Szk)
        print(l, " ")
        u = mS(Szk[l])  #do compact rep here???
        valofnewelement = mul(mS.valuations[l], z)
        Hecke.class_group_add_relation(c, FacElem(Dict((N(x, i, j), v) for (x,v) = u.fac)), valofnewelement)
      end
      println("")
    end

    println("done")

    # Skipping the units
    U, mU = unit_group_fac_elem(zk)
    for j=2:ngens(U) # I cannot add a torsion unit. He will hang forever.
      u = mU(U[j])
      Hecke._add_unit(UZK, FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac)))
    end
    UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end

  #UZK.tentative_regulator = Hecke.regulator(UZK.units, 64)
end

function _compute_sunit_and_unit_group!(c, U, N, saturate = true)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  skipped_units = FacElem{nf_elem, AnticNumberField}[]
  autos = automorphisms(field(N), copy = false)

  for i = 1:length(N)
    k, mk = subfield(N, i)
    zk = lll(maximal_order(k))
    print("Computing class group of $k... ")
    @time class_group(zk, redo = true, use_aut = true)
    println("done")
    lpk = NfOrdIdl[ P[1] for p in cp for P = prime_decomposition(zk, p)]
    println("Now computing the S-unit group for lp of length $(length(lpk))")
    @assert length(lpk) > 0
    @time Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)
    @show length(N.coefficients_gen[i])

    #D = Dict{nf_elem, nf_elem}()
    cc = Vector{Tuple{Int, fmpz}}[]
    induced = induce_action_from_subfield(N, i, lpk, c.FB, cc)
    for l in 1:ngens(Szk)
      u = mS(Szk[l])
      for j in 1:length(induced)
        aut = autos[j]
        valofnewelement = mul(mS.valuations[l], induced[j])
        Hecke.class_group_add_relation(c, FacElem(Dict((aut(embedding(N, i)(x)), v) for (x,v) = u.fac)), valofnewelement)
      end
    end


    #for j in 1:length(N.coefficients_gen[i])
    #  println("Inducing the action ... ")
    #  @time z = induce_action(N, i, j, lpk, c.FB, cc)

    #  print("Feeding in the S-units of the small field ... ")

    #  for l=1:ngens(Szk)
    #    u = mS(Szk[l])  #do compact rep here???
    #    valofnewelement = mul(mS.valuations[l], z)
    #    Hecke.class_group_add_relation(c, FacElem(Dict((N(x, i, j), v) for (x,v) = u.fac)), valofnewelement)
    #  end
    #end

    println("done")

    u, mu = unit_group_fac_elem(zk)
    for n=2:ngens(u) # I cannot add a torsion unit. He will hang forever.
      uelem = mu(u[n])
      for j in 1:length(induced)
        aut = autos[j]
        lifted_unit = FacElem(Dict((aut(embedding(N, i)(x)), v) for (x,v) = uelem.fac))
        bb = Hecke._add_unit(U, lifted_unit)
        @show bb
        if !bb
          push!(skipped_units, lifted_unit)
        end
      end
      U.units = Hecke.reduce(U.units, U.tors_prec)
    end

    #for j in 1:length(N.coefficients_gen[i])
    #  for n=2:ngens(u) # I cannot add a torsion unit. He will hang forever.
    #    uelem = mu(u[n])
    #    lifted_unit = FacElem(Dict((N(x, i, j), v) for (x,v) = uelem.fac))
    #    bb = Hecke._add_unit(U, lifted_unit)
    #    @show bb
    #    if !bb
    #      push!(skipped_units, lifted_unit)
    #    end
    #  end
    #  U.units = Hecke.reduce(U.units, U.tors_prec)
    #end
  end


  @show length(skipped_units)

  for lifted_unit in skipped_units
    @show Hecke.regulator(U.units, 64)
    Hecke._add_dependent_unit(U, lifted_unit)
  end

  U.tentative_regulator = Hecke.regulator(U.units, 64)

  println("Now saturating ... ")

  if saturate
    for (p, e) in factor(index(N))
      b = Hecke.saturate!(c, U, Int(p))
      while b
        b = Hecke.saturate!(c, U, Int(p))
      end
    end
  end
  return c, U
end

one(T::FacElemMon{AnticNumberField}) = T()

function simplify(c::Hecke.ClassGrpCtx)
  d = Hecke.class_group_init(c.FB, SMat{fmpz}, add_rels = false)
  U = Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(order(d))

  Hecke.module_trafo_assure(c.M)
  trafos = c.M.trafo

  for i=1:length(c.FB.ideals)
    x = zeros(fmpz, length(c.R_gen) + length(c.R_rel))
    x[i] = 1
    for j in length(trafos):-1:1
      Hecke.apply_right!(x, trafos[j])
    end
    y = FacElem(vcat(c.R_gen, c.R_rel), x)
    fl = Hecke.class_group_add_relation(d, y, deepcopy(c.M.basis.rows[i]))
    @assert fl
  end
  for i=1:nrows(c.M.rel_gens)
    if iszero(c.M.rel_gens.rows[i])
      Hecke._add_unit(U, c.R_rel[i])
    end
  end
  for i=1:length(U.units)  
    Hecke.class_group_add_relation(d, U.units[i], SRow(FlintZZ))
  end
  return d, U
end

function units(c::Hecke.ClassGrpCtx)
  d = Hecke.class_group_init(c.FB, SMat{fmpz}, add_rels = false)
  U = Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(order(d))

  Hecke.module_trafo_assure(c.M)
  trafos = c.M.trafo

  for i=1:nrows(c.M.rel_gens)
    if iszero(c.M.rel_gens.rows[i])
      Hecke._add_unit(U, c.R_rel[i])
    end
  end

  U.units = Hecke.reduce(U.units, U.tors_prec)
  U.tentative_regulator = Hecke.regulator(U.units, 64)

  return U
end

################################################################################
#
#  Residue computation via Brauer relations
#
################################################################################

function zeta_log_residue(O::NfOrd, N::NormRelation, abs_error::Float64)
  degree(O) == 1 && error("Number field must be of degree > 1")
  !ispure(N) && error("Norm relation must be a Brauer relation")
  @show index(N)
  target_prec = Int(floor(log(abs_error)))
  @show target_prec
  residues = arb[]
  for i in 1:length(N)
    v = N.coefficients_gen[i]
    @assert length(v) == 1
    c = (v[1][1] * divexact(degree(N.K), degree(N.subfields[i][1]))) // index(N)
    push!(residues, c * zeta_log_residue(maximal_order(N.subfields[i][1]), abs_error/(2*length(N))))
  end
  z = sum(residues)
  @assert radiuslttwopower(z, target_prec)
  return z
end

function _lift_to_normalized_brauer_relation(N)
  @assert ispure(N)
  rel = fmpq[]
  for i in 1:length(N)
    v = N.coefficients_gen[i]
    push!(rel, fmpq(v[1][1] * divexact(degree(N.K), degree(N.subfields[i][1]))) // index(N))
  end
  return rel
end

function hR_from_subfields(N, abs_prec::Int = 64)
  @assert ispure(N)
  rel = _lift_to_normalized_brauer_relation(N)
  vals = arb[]
  for i in 1:length(N)
    zk = lll(maximal_order(subfield(N, i)[1]))
    c, _ = class_group(zk)
    u, mu = unit_group_fac_elem(zk)
    push!(vals, (1//order(torsion_unit_group(zk)[1]) * order(c) * regulator([mu(u[i]) for i in 2:rank(u) + 1], abs_prec))^rel[i])
  end
  return prod(vals) * order(torsion_unit_group(maximal_order(field(N)))[1])
end

################################################################################
#
#  Code for abstract norm relations
#
################################################################################

# TODO: Make this great again
function _has_norm_relation_abstract(G::GrpGen, H::Vector{Tuple{GrpGen, GrpGenToGrpGenMor}};
                                     primitive::Bool = false,
                                     greedy::Bool = false,
                                     large_index::Bool = false,
                                     pure::Bool = false,
                                     target_den::fmpz = zero(fmpz))
  QG = AlgGrp(FlintQQ, G)
  norms_rev = Dict{elem_type(QG), Int}()
  norms = Vector{elem_type(QG)}(undef, length(H))
  for i in 1:length(H)
    norms_rev[sum([QG(H[i][2](h)) for h in H[i][1]])] = i
    norms[i] = sum([QG(H[i][2](h)) for h in H[i][1]])
  end

  n = Int(order(G))

  if pure
    if iszero(target_den)
      m = zero_matrix(FlintQQ, length(H), n)
      for i in 1:length(H)
        for j in 1:n
          m[i, j] = norms[i].coeffs[j]
        end
      end

      onee = matrix(FlintQQ, 1, n, coeffs(one(QG)))

      b, v, K = can_solve_with_kernel(m, onee, side = :left)
    else
      m = zero_matrix(FlintZZ, length(H), n)
      for i in 1:length(H)
        for j in 1:n
          m[i, j] = FlintZZ(norms[i].coeffs[j])
        end
      end

      onee = matrix(FlintZZ, 1, n, coeffs(one(QG)))

      b, w, K = can_solve_with_kernel(m, target_den * onee, side = :left)
      v = 1//target_den * change_base_ring(FlintQQ, w)
    end

    if !b
      return false, zero(FlintZZ), Vector{Tuple{Vector{Tuple{fmpz, GrpAbFinGenElem}}, Vector{GrpAbFinGenElem}}}()
    end

    @assert b

    subgroups_needed = Int[ i for i in 1:length(H) if !iszero(v[1, i])]

    den = denominator(v[1, 1])
    for i in 2:length(H)
      den = lcm!(den, den, denominator(v[1, i]))
    end

    vvv = Vector{Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}}(undef, length(subgroups_needed))
    for i in 1:length(vvv)
      vvv[i] = Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}()
    end

    solutions = Vector{Tuple{Vector{GrpGenElem}, Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}}}()

    for i in 1:length(subgroups_needed)
      push!(vvv[i], (numerator(den * v[1, subgroups_needed[i]]), id(G), id(G)))
      sgroup = [H[subgroups_needed[i]][2](h) for h in H[subgroups_needed[i]][1]]
      push!(solutions, (sgroup, vvv[i]))
    end

    z = zero(QG)
    for cc in 1:length(subgroups_needed)
      z = z + v[1, subgroups_needed[cc]] * norms[subgroups_needed[cc]]
    end

    @assert isone(z)

    return true, den, solutions
  end

  wd = decompose(QG)
  idempotents = [ f(one(A)) for (A, f) in wd]

  nonannihilating = Vector{Vector{Int}}(undef, length(idempotents))

  for j in 1:length(idempotents)
    nonannihilating_ej = Vector{Int}()
    for i in 1:length(norms)
      if !iszero(idempotents[j] * norms[i])
        push!(nonannihilating_ej, i)
      end
    end
    nonannihilating[j] = nonannihilating_ej
  end

  l = length(idempotents)

  subgroups_needed = Int[]

  if any(isempty, nonannihilating)
    return false, zero(FlintZZ), Vector{Tuple{Vector{Tuple{fmpz, GrpAbFinGenElem}}, Vector{GrpAbFinGenElem}}}()
  end

  subgroups_needed = Int[]

  for i in 1:length(nonannihilating)
    if greedy || !large_index
      sort!(nonannihilating[i], by = x -> order(H[x][1]), rev = true)
    elseif large_index
      sort!(nonannihilating[i], by = x -> order(H[x][1]))
    end
  end

  k = nonannihilating[1][1]
  push!(subgroups_needed, k)
  i = 2
  for i in 2:l
    if length(intersect(subgroups_needed, nonannihilating[i])) > 0
      continue
    else
      push!(subgroups_needed, nonannihilating[i][1])
    end
  end

  if !iszero(target_den)
    subgroups_needed = collect(1:length(H))
  end

  if primitive
    # Check if we can replace a subgroup by bigger subgroups
    for i in 1:length(subgroups_needed)
      Q, mQ = quo(G, H[subgroups_needed[i]][1])
      if length(Q) == 1
        continue
      end
      b, den, ls = _has_norm_relation_abstract(Q, [f for f in subgroups(Q) if order(f[1]) > 1])
      if b
        return _has_norm_relation_abstract(G, deleteat!(H, subgroups_needed[i]))
      end
    end
  end

  # Now solve the equation to find a representation 1 = sum_{H} x_H N_H y_H
  n = Int(order(G))

  # We use the following trick to reduce the number of equations
  # Instead of working with the Q-basis (g N_H h)_(H, g in G, h in H), we take
  # (g N_H h)_(H, g in G/H, h in G\N_G(H))

  left_cosets_for_sub = Vector{GrpGenElem}[]
  right_cosets_for_normalizer = Vector{GrpGenElem}[]

  for i in 1:length(subgroups_needed)
    lc = left_cosets(G, H[subgroups_needed[i]][2])
    push!(left_cosets_for_sub, lc)
    NGH = normalizer(G, H[subgroups_needed[i]][2])
    push!(right_cosets_for_normalizer, right_cosets(G, NGH[2]))
  end

  if iszero(target_den)
    onee = matrix(FlintQQ, 1, n, coeffs(one(QG)))

    m = zero_matrix(FlintQQ, dot(length.(left_cosets_for_sub), length.(right_cosets_for_normalizer)), n)

    B = basis(QG)

    help_with_indicies = Vector{Tuple{Int, Int, Int}}(undef, nrows(m))
    cc = 1
    for i in 1:length(subgroups_needed)
      lcosub = length(left_cosets_for_sub[i])
      lconor = length(right_cosets_for_normalizer[i])
      for (k, g) in enumerate(left_cosets_for_sub[i])
        for (l, h) in enumerate(right_cosets_for_normalizer[i])
          for j in 1:n
            m[cc, j] = (QG(g) * norms[subgroups_needed[i]] * QG(h)).coeffs[j]
          end
          help_with_indicies[cc] = (i, k, l)
          cc += 1
        end
      end
    end

    b, w, K = can_solve_with_kernel(m, onee, side = :left)
    v = w
  elseif true
    onee = matrix(FlintZZ, 1, n, coeffs(target_den * one(QG)))

    m = zero_matrix(FlintZZ, dot(length.(left_cosets_for_sub), length.(right_cosets_for_normalizer)), n)

    help_with_indicies = Vector{Tuple{Int, Int, Int}}(undef, nrows(m))
    cc = 1
    for i in 1:length(subgroups_needed)
      for (k, g) in enumerate(left_cosets_for_sub[i])
        for (l, h) in enumerate(right_cosets_for_normalizer[i])
          for j in 1:n
            m[cc, j] = FlintZZ((QG(g) * norms[subgroups_needed[i]] * QG(h)).coeffs[j])
          end
          help_with_indicies[cc] = (i, k, l)
          cc += 1
        end
      end
    end

    b, w, K = can_solve_with_kernel(m, onee, side = :left)

    v = 1//target_den * change_base_ring(FlintQQ, w)
  end

  @assert b

  z = zero(QG)
  for cc in 1:ncols(v)
    if iszero(v[1, cc])
      continue
    else
      i, k, l = help_with_indicies[cc]
      z = z + v[1, cc] *  QG(left_cosets_for_sub[i][k]) * norms[subgroups_needed[i]] * QG(right_cosets_for_normalizer[i][l])
    end
  end

  @assert isone(z)

  den = one(FlintZZ)

  for i in 1:ncols(v)
    den = lcm(den, denominator(v[1, i]))
  end

  solutions = Vector{Tuple{Vector{GrpGenElem}, Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}}}()

  vvv = Vector{Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}}(undef, length(subgroups_needed))
  for i in 1:length(vvv)
    vvv[i] = Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}()
  end

  for cc in 1:ncols(v)
    if iszero(v[1, cc])
      continue
    else
      i, k, l = help_with_indicies[cc]
      push!(vvv[i], (FlintZZ(den * v[1, cc]), left_cosets_for_sub[i][k], right_cosets_for_normalizer[i][l]))
    end
  end

  for i in 1:length(vvv)
    sgroup = [H[subgroups_needed[i]][2](h) for h in H[subgroups_needed[i]][1]]
    if length(vvv[i]) > 0
      push!(solutions, (sgroup, vvv[i]))
    end
  end

  if !iszero(target_den)
    @assert iszero(mod(target_den, den))
  end

  return true, den, solutions
end

################################################################################
#
#  Existence of norm relations
#
################################################################################

function has_useful_brauer_relation(G)
  subs = subgroups(G, conjugacy_classes = true)
  for (H,_) in subs
    if iscyclic(H)
      continue
    end
    fac = factor(order(H))
    if length(fac) > 2
      continue
    end
    if length(fac) == 2
      e = prod(e for (p, e) in fac)
      if e == 1
        return true
      end
    end
    if length(fac) == 1
      for (p, e) in fac
        if e == 2
          return true
        end
      end
    end
  end
  return false
end

const _fermat_primes = Int[3, 5, 17, 257, 65537]

function has_useful_generalized_norm_relation(G)
  subs = subgroups(G, conjugacy_classes = true)
  for (H,_) in subs
    if iscyclic(H)
      continue
    end

    # This is the check for SL(2, 3)
    # SL(2, 5) has order 120
    if order(H) == 24 && find_small_group(H)[1] == (24, 3)
      return true
    end

    fac = factor(order(H))
    if length(fac) > 2
      continue
    end
    if length(fac) == 2
      e = prod(e for (p, e) in fac)
      if e == 1
        return true
      end
    end
    if length(fac) == 1
      for (p, e) in fac
        if e == 2
          return true
        end
      end
    end
  end
  return false
end

################################################################################
#
#  Redo the S-unit computation for Brauer norm relation
#
################################################################################

function _embed(N::NormRelation, i::Int, a::nf_elem)
  b = get(N.embed_cache_triv[i], a, nothing)
  if b === nothing
    _, mk = subfield(N, i)
    c = mk(a)
    N.embed_cache_triv[i][a] = c
    return c
  else
    return b
  end
end

# pure

function _add_sunits_from_brauer_relation!(c, UZK, N)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  for i = 1:length(N)
    k, mk = subfield(N, i)
    @vprint :NormRelation 1 "Looking at the subfield $k \n"
    @vprint :NormRelation 1 "Computing lll basis of maximal order ...\n"
    zk = maximal_order(k)
    zk = lll(zk)
    @vprint :NormRelation 1 "Computing class group ... \n"
    class_group(zk, redo = false, use_aut = true)
    lpk = NfOrdIdl[ P[1] for p in cp for P = prime_decomposition(zk, p)]
    @assert length(lpk) > 0
    @vprint :NormRelation 1 "Computing sunit group for set of size $(length(lpk)) ... \n"
    Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)

    @vprint :NormRelation 1 "Coercing the sunits into the big field ...\n"
    for j in 1:length(N.coefficients_gen[i])
      z = induce_action_just_from_subfield(N, i, lpk, c.FB)

      for l=1:ngens(Szk)
        u = mS(Szk[l])  #do compact rep here???
        valofnewelement = mul(mS.valuations[l], z)
        zz = mk(evaluate(u))
        @hassert :NormRelation 1 sparse_row(FlintZZ, [ (i, valuation(zz, p)) for (i, p) in enumerate(c.FB.ideals) if valuation(zz, p) != 0]) == valofnewelement
        Hecke.class_group_add_relation(c, FacElem(Dict((_embed(N, i, x), v) for (x,v) = u.fac)), valofnewelement)
      end
    end

    @vprint :NormRelation 1 "Coercing the units into the big field ... \n"
    U, mU = unit_group_fac_elem(zk)
    for j=2:ngens(U) # I cannot add a torsion unit. He will hang forever.
      u = mU(U[j])
      Hecke._add_unit(UZK, FacElem(Dict((_embed(N, i, x), v) for (x,v) = u.fac)))
    end
    UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end
  return nothing
end

function induce_action_just_from_subfield(N::NormRelation, i, s, FB)
  S = FB.ideals
  ZK = order(S[1])

  z = zero_matrix(SMat, FlintZZ, 0, length(S))

  mk = embedding(N, i)
  zk = order(s[1])

  @assert mod(degree(ZK), degree(zk)) == 0
  reldeg = divexact(degree(ZK), degree(zk))

  for l in 1:length(s)
    v = Tuple{Int, fmpz}[]
    P = s[l]
    genofsl = elem_in_nf(_embed(N, i, P.gen_two.elem_in_nf))
    pmin = minimum(P, copy = false)
    # Compute the number of ideals
    # Assume that L/K and L/Q are normal
    rele = divexact(ramification_index((FB.fb[pmin].lp)[1][2]), ramification_index(P))
    relf = divexact(degree((FB.fb[pmin].lp)[1][2]), degree(P))
    @assert mod(reldeg, rele * relf) == 0
    numb_ideal = divexact(reldeg, rele * relf)
    found = 0
    for k in 1:length(S)
      Q = S[k]
      if minimum(Q, copy = false) == pmin
        ant = anti_uniformizer(Q)
        if (genofsl * ant) in ZK
          found += 1
          @assert mod(ramification_index(Q), ramification_index(s[l])) == 0
          push!(v, (k, divexact(ramification_index(Q), ramification_index(s[l]))))
        end
      end
      if found == numb_ideal
        break
      end
    end
    sort!(v, by = x -> x[1])
    push!(z, sparse_row(FlintZZ, v))
  end
  return z
end

function sunit_group_fac_elem_quo_via_brauer(K::AnticNumberField, S, n::Int)
  @vprint :NormRelation 1 "Setting up the norm relation context ... \n"
  N = _norm_relation_setup_generic(K, pure = true, small_degree = true); 
  return _sunit_group_fac_elem_quo_via_brauer(N, S, n)
end

function _sunit_group_fac_elem_quo_via_brauer(N::NormRelation, S, n::Int)
  O = order(S[1])

  K = N.K

  c, UZK = Hecke._setup_for_norm_relation_fun(K, S)
  Hecke._add_sunits_from_brauer_relation!(c, UZK, N)

  if gcd(index(N), n) != 1
    # I need to saturate
    @vprint :NormRelation 1 "Saturating at "
    for (p, e) in factor(index(N))
      @vprint :NormRelation 1 "$p "
      b = Hecke.saturate!(c, UZK, Int(p))
      while b
        b = Hecke.saturate!(c, UZK, Int(p))
      end
    end
  end
  @vprint :NormRelation 1 "\n"

  sunitsmodunits = c.R_gen # These are generators for the S-units (mod units, mod n)
  unitsmodtorsion = UZK.units # These are generators for the units (mod n)
  T, mT = torsion_unit_group(O)
  Q, mQ = quo(T, n)
  @assert issnf(Q)
  @assert ngens(Q) == 1
  m = order(Q)

  if !isone(m)
    tomodn = FacElem(elem_in_nf(mT(mQ\Q[1])))
    res_group = DiagonalGroup(append!(fmpz[m], [fmpz(n) for i in 1:(length(sunitsmodunits) + length(unitsmodtorsion))]))

    exp = function(a::GrpAbFinGenElem)
      @assert parent(a) == res_group
      zz = FacElem(convert(Vector{nf_elem_or_fac_elem}, unitsmodtorsion), fmpz[1 + a[i] for i in 1:length(unitsmodtorsion)])
      z = mul!(zz, zz, tomodn)
      zzz = FacElem(convert(Vector{nf_elem_or_fac_elem}, sunitsmodunits), fmpz[a[1 + length(unitsmodtorsion) + i] for i in 1:length(sunitsmodunits)])
      mul!(z, z, zzz)
      
      for (k, v) in z.fac
        if iszero(v)
          delete!(z.fac, k)
        end
      end

      return z
    end

    disclog = function(a)
      throw(NotImplemented())
    end
  else # torsion part is one
    res_group = DiagonalGroup([fmpz(n) for i in 1:(length(sunitsmodunits) + length(unitsmodtorsion))])

    exp = function(a::GrpAbFinGenElem)
      @assert parent(a) == res_group
      z = FacElem(convert(Vector{nf_elem_or_fac_elem}, unitsmodtorsion), fmpz[a[i] for i in 1:length(unitsmodtorsion)])
      # This is madness
      zz = FacElem(convert(Vector{nf_elem_or_fac_elem}, sunitsmodunits), fmpz[a[length(unitsmodtorsion) + i] for i in 1:length(sunitsmodunits)])
      z = mul!(z, z, zz)

      for (k, v) in z.fac
        if iszero(v)
          delete!(z.fac, k)
        end
      end

      return z
    end

    disclog = function(a)
      throw(NotImplemented())
    end
  end

  r = MapSUnitGrpFacElem{typeof(res_group)}()
  r.idl = S
  r.isquotientmap = n

  r.header = MapHeader(res_group, FacElemMon(nf(O)), exp, disclog)
  return res_group, r
end
