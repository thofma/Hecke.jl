################################################################################
#
#  (Generalized) norm relations
#
################################################################################

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

  function NormRelation{T}() where {T}
    z = new{T}()
    z.ispure = false
    z.isabelian = false
    z.isgeneric = false
    z.denominator = 0
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

  println("Computing the subfields ... ")
 
  for i in 1:n
    println("$i/$n")
    @time F, mF = fixed_field(K, NfToNfMor[AtoG[f] for f in ls[i][2]])
    println("I start simplifying")
    @time maximal_order(F)
    @time S, mS = simplify(F)
    println("DONE")
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

function _norm_relation_setup_generic(K::AnticNumberField; small_degree::Bool = true, target_den::fmpz = zero(fmpz))
  A = automorphisms(K)
  G, AtoG, GtoA = generic_group(A, *);
  if iszero(target_den)
    b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(G, conjugacy_classes = true) if order(f[1]) > 1])
  else
    b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(G, conjugacy_classes = true) if order(f[1]) > 1], target_den = target_den)
  end
  @assert b
  n = length(ls)

  z = NormRelation{Int}()
  z.K = K
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = false
 
  for i in 1:n
    F, mF = fixed_field(K, NfToNfMor[GtoA[f] for f in ls[i][1]])
    S, mS = simplify(F)
    L = S
    mL = mS * mF
    z.subfields[i] = L, mL
  end

  z.coefficients_gen = Vector{Vector{Tuple{NfToNfMor, Int}}}(undef, n)

  for i in 1:n
    w = Vector{Tuple{Int, NfToNfMor, NfToNfMor}}(undef, length(ls[i][2]))
    for (j, (expo, auto_pre, auto_post)) in enumerate(ls[i][2])
      w[j] = (expo, GtoA[auto_pre], GtoA[auto_post])
    end
    z.coefficients_gen[i] = w
  end

  z.isabelian = true

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
  z = one(field(N))
  for i in 1:length(N)
    z = z * N(norm(embedding(N, i), a), i)
  end
  return a^index(N) == z
end

function (N::NormRelation)(x::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, i::Int)
  z = one(N.K)
  _, mk = subfield(N, i)
  y = mk(x)
  if ispure(N)
    return y^N.pure_coefficients[i]
  else
    for (auto, expo) in N.coefficients[i]
      z = z * auto(y)^expo
    end
    return z
  end
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
          push!(v, (k, divexact(splitting_type(Q)[1], splitting_type(s[j])[1])))
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

function _add_sunits_from_norm_relation!(c, N)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  for i = 1:length(N)
    k, mk = subfield(N, i)
    println("Computing maximal order ...")
    @time zk = maximal_order(k)
    println("Computing lll basis ... ")
    @show k
    @time zk = lll(zk)
    print("Computing class group of $k... ")
    @time class_group(zk, redo = true, use_aut = false)
    println("done")
    lpk = NfOrdIdl[ P[1] for p in cp for P = prime_decomposition(zk, p)]
    println("Now computing the S-unit group for lp of length $(length(lpk))")
    @assert length(lpk) > 0
    @time Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)
    @time z = induce_action(N, i, lpk, c.FB.ideals) # Careful, don't use S instead of FB.ideals

    # Embedding is expensive, so let us build a cache
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

    print("Feeding in the S-units of the small field ... ")

    for j=1:ngens(Szk)
      print(j, " ")
      u = mS(Szk[j])  #do compact rep here???
      #@show z.rows
      valofnewelement = mul(mS.valuations[j], z)
      #v = zeros(fmpz, length(FB.ideals))
      #v[valofnewelement.pos] = valofnewelement.values
      #@assert [valuation((FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac))), P) for P in FB.ideals] == v
      Hecke.class_group_add_relation(c, FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac)), valofnewelement)
    end

    println("done")

    # Skipping the units
    #U, mU = unit_group_fac_elem(zk)
    #for j=2:ngens(U) # I cannot add a torsion unit. He will hang forever.
    #  u = mU(U[j])
    #  Hecke._add_unit(UZK, FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac)))
    #end
    #UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end

  #UZK.tentative_regulator = Hecke.regulator(UZK.units, 64)
end

function _compute_sunit_group_mod(K::AnticNumberField, N::NormRelation, S)
  ZK = order(S[1])
  FB = NfFactorBase(ZK, S)
  c = class_group_init(FB)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))

  UZK = Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(ZK)

  for i = 1:length(N)
    k, mk = subfield(N, i)
    zk = maximal_order(k)
    print("Computing class group of $k... ")
    class_group(zk, use_aut = true)
    println("done")
    lpk = [ P[1] for p in cp for P = prime_decomposition(zk, p)]
    println("Now computing the S-unit group for lp of length $(length(lpk))")
    @assert length(lpk) > 0
    Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)
    z = induce_action(N, i, lpk, FB.ideals) # Careful, don't use S instead of FB.ideals

    # Embedding is expensive, so let us build a cache
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

    print("Feeding in the S-units of the small field ... ")

    for j=1:ngens(Szk)
      print(j, " ")
      u = mS(Szk[j])  #do compact rep here???
      #@show z.rows
      valofnewelement = mul(mS.valuations[j], z)
      #v = zeros(fmpz, length(FB.ideals))
      #v[valofnewelement.pos] = valofnewelement.values
      #@assert [valuation((FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac))), P) for P in FB.ideals] == v
      Hecke.class_group_add_relation(c, FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac)), valofnewelement)
    end

    println("done")

    U, mU = unit_group_fac_elem(zk)
    for j=2:ngens(U) # I cannot add a torsion unit. He will hang forever.
      u = mU(U[j])
      Hecke._add_unit(UZK, FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac)))
    end
    UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end

  UZK.tentative_regulator = Hecke.regulator(UZK.units, 64)

  println("Now saturating ... ")

  for (p, e) in factor(index(N))
    @show p
    b = Hecke.saturate!(c, UZK, Int(p))
    while b
      @show "SATURATING AGAIN"
      b = Hecke.saturate!(c, UZK, Int(p))
    end
  end
  return c, UZK
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
#  Code for abstract norm relations
#
################################################################################

# TODO:
# This is a mess.
# We first have to figure out the different relation types.
function _has_norm_relation_abstract(G::GrpAb,
                                     H::Vector{Tuple{GrpAbFinGen, GrpAbFinGenMap}};
                                     primitive::Bool = false,
                                     interactive::Bool = false,
                                     greedy::Bool = false,
                                     large_index::Bool = false,
                                     pure::Bool = false)
  QG = AlgGrp(FlintQQ, G)
  wd = decompose(QG)
  idempotents = [ f(one(A)) for (A, f) in wd]
  norms_rev = Dict{elem_type(QG), Int}()
  norms = Vector{elem_type(QG)}(undef, length(H))
  for i in 1:length(H)
    norms_rev[sum([QG(H[i][2](h)) for h in H[i][1]])] = i
    norms[i] = sum([QG(H[i][2](h)) for h in H[i][1]])
  end

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

  for i in 1:length(nonannihilating)
    if greedy || !large_index
      sort!(nonannihilating[i], by = x -> order(H[x][1]), rev = true)
    elseif large_index
      sort!(nonannihilating[i], by = x -> order(H[x][1]))
    end
  end

  if interactive
    println("Which subgroups to choose?:")
    string_read = readline(stdin)
    subgroups_needed = eval(Meta.parse(string_read))
    if any(x -> length(intersect(subgroups_needed, x)) == 0, nonannihilating)
      error("They don't give a relation")
    end
  else
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

  cyc = [h for h in H]# if iscyclic(h[1])]

  if pure
    n = Int(order(G))
    m = zero_matrix(FlintQQ, length(cyc), n)
    for i in 1:length(cyc)
      for j in 1:n
        m[i, j] = norms[i].coeffs[j]
      end
    end

    onee = matrix(FlintQQ, 1, n, coeffs(one(QG)))

    b, v, K = cansolve_with_kernel(m', onee')

    if !b
      return false, zero(FlintZZ), Vector{Tuple{Vector{Tuple{fmpz, GrpAbFinGenElem}}, Vector{GrpAbFinGenElem}}}()
    end

    subgroups_needed = Int[ i for i in 1:nrows(v) if !iszero(v[i, 1])]

    den = one(FlintZZ)

    for i in subgroups_needed
      den = lcm(den, denominator(v[i, 1]))
    end

    solutions_as_group_element_arrays = Vector{Tuple{fmpz, Vector{GrpAbFinGenElem}}}(undef, length(subgroups_needed))

    for i in 1:length(subgroups_needed)
    #  vv = Tuple{fmpz, GrpAbFinGenElem}[]
    #  for (j, g) in enumerate(group(QG))
    #    if !iszero(sol[i].coeffs[j])
    #      push!(vv, (FlintZZ(den*sol[i].coeffs[j]), g))
    #    end
    #  end
      solutions_as_group_element_arrays[i] = (FlintZZ(den * v[subgroups_needed[i], 1]), [H[subgroups_needed[i]][2](h) for h in H[subgroups_needed[i]][1]])
    end

    @assert b
    return true, den, solutions_as_group_element_arrays

  end

  # Now solve the equation to find a representation 1 = sum_{H} x_H N_H
  n = Int(order(G))

  onee = matrix(FlintQQ, 1, n, coeffs(one(QG)))

  m = zero_matrix(FlintQQ, length(subgroups_needed) * n, n)

  B = basis(QG)

  for i in 1:length(subgroups_needed)
    for j in 1:n
      for k in 1:n
        m[(i - 1)*n + k, j] = (B[k] * norms[subgroups_needed[i]]).coeffs[j]
      end
    end
  end

  b, v, K = cansolve_with_kernel(m', onee')

  # Now collect the coefficients again as elements of Q[G]
  sol = Vector{elem_type(QG)}(undef, length(subgroups_needed))
  for i in 1:length(subgroups_needed)
    sol[i] = QG([v[k, 1] for k in ((i - 1)*n + 1):i*n])
  end

  @assert one(QG) == sum(sol[i] * norms[subgroups_needed[i]] for i in 1:length(subgroups_needed))

  den = one(FlintZZ)

  for i in 1:length(subgroups_needed)
    for j in 1:n
      den = lcm(den, denominator(sol[i].coeffs[j]))
    end
  end

  solutions_as_group_element_arrays = Vector{Tuple{Vector{Tuple{fmpz, GrpAbFinGenElem}}, Vector{GrpAbFinGenElem}}}(undef, length(subgroups_needed))

  for i in 1:length(subgroups_needed)
    vv = Tuple{fmpz, GrpAbFinGenElem}[]
    for (j, g) in enumerate(group(QG))
      if !iszero(sol[i].coeffs[j])
        push!(vv, (FlintZZ(den*sol[i].coeffs[j]), g))
      end
    end
    solutions_as_group_element_arrays[i] = (vv, [H[subgroups_needed[i]][2](h) for h in H[subgroups_needed[i]][1]])
  end

  return true, den, solutions_as_group_element_arrays
end

# TODO: Make this great again
function _has_norm_relation_abstract(G::GrpGen, H::Vector{Tuple{GrpGen, GrpGenToGrpGenMor}};
                                     primitive::Bool = false,
                                     greedy::Bool = false,
                                     large_index::Bool = false,
                                     pure::Bool = false,
                                     target_den::fmpz = zero(fmpz))
  QG = AlgGrp(FlintQQ, G)
  wd = decompose(QG)
  idempotents = [ f(one(A)) for (A, f) in wd]
  norms_rev = Dict{elem_type(QG), Int}()
  norms = Vector{elem_type(QG)}(undef, length(H))
  for i in 1:length(H)
    norms_rev[sum([QG(H[i][2](h)) for h in H[i][1]])] = i
    norms[i] = sum([QG(H[i][2](h)) for h in H[i][1]])
  end

  n = Int(order(G))

  if pure
    m = zero_matrix(FlintQQ, length(H), n)
    for i in 1:length(H)
      for j in 1:n
        m[i, j] = norms[i].coeffs[j]
      end
    end

    onee = matrix(FlintQQ, 1, n, coeffs(one(QG)))

    b, v, K = cansolve_with_kernel(m', onee')

    return b
  end

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

  if iszero(target_den)
    onee = matrix(FlintQQ, 1, n, coeffs(one(QG)))

    m = zero_matrix(FlintQQ, length(subgroups_needed) * n * n, n)

    B = basis(QG)

    for i in 1:length(subgroups_needed)
      for k in 1:n
        for l in 1:n
          for j in 1:n
            m[(i - 1)*n^2 + n * (k - 1) + l, j] = (B[k] * norms[subgroups_needed[i]] * B[l]).coeffs[j]
          end
        end
      end
    end


    b, w, K = cansolve_with_kernel(m, onee, side = :left)
    v = w
  elseif true
    onee = matrix(FlintZZ, 1, n, coeffs(target_den * one(QG)))

    m = zero_matrix(FlintZZ, length(subgroups_needed) * n * n, n)

    B = basis(QG)

    for i in 1:length(subgroups_needed)
      for k in 1:n
        for l in 1:n
          for j in 1:n
            m[(i - 1)*n^2 + n * (k - 1) + l, j] = FlintZZ((B[k] * norms[subgroups_needed[i]] * B[l]).coeffs[j])
          end
        end
      end
    end

    @show size(m)

    b, w, K = cansolve_with_kernel(m, onee, side = :left)
    v = 1//target_den * change_base_ring(w, FlintQQ)
    @show v
  end

  @assert b

  # Now collect the coefficients again as elements of Q[G]
  sol = Vector{Tuple{Int, Int, Int, fmpq}}()
  for i in 1:length(subgroups_needed)
    for k in 1:n
      for l in 1:n
        if iszero(v[1, (i - 1)*n^2 + (k - 1) * n + l])
          continue
        else
          push!(sol, (i, k, l, v[1, (i - 1)*n^2 + (k - 1) * n + l]))
        end
      end
    end
  end

  z = zero(QG)
  for (i, k, l, x) in sol
    z = z + x * B[k] * norms[subgroups_needed[i]] * B[l]
  end

  @assert isone(z)

  den = one(FlintZZ)

  for (_,_,_,x) in sol
    den = lcm(den, denominator(x))
  end

  solutions = Vector{Tuple{Vector{GrpGenElem}, Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}}}()
  solutions_as_group_element_arrays = Vector{Tuple{Vector{Tuple{fmpz, GrpAbFinGenElem}}, Vector{GrpAbFinGenElem}}}(undef, length(subgroups_needed))

  for i in 1:length(subgroups_needed)
    sgroup = [H[subgroups_needed[i]][2](h) for h in H[subgroups_needed[i]][1]]
    vv = Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}()
    for (k, g) in enumerate(group(QG))
      for (l, h) in enumerate(group(QG))
        if iszero(v[1, (i - 1)*n^2 + (k - 1) * n + l])
          continue
        else
          push!(vv, (FlintZZ(den * v[1, (i - 1)*n^2 + (k - 1) * n + l]), g, h))
        end
      end
    end
    push!(solutions, (sgroup, vv))
  end

  if !iszero(target_den)
    @assert iszero(mod(target_den, den))
  end

  return true, den, solutions
end

