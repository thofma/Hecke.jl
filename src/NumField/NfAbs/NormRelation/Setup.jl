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
  is_abelian::Bool
  isgeneric::Bool
  coefficients_gen::Vector{Vector{Tuple{Int, NfToNfMor, NfToNfMor}}}
  embed_cache::Dict{Tuple{Int, Int}, Dict{nf_elem, nf_elem}}
  mor_cache::Dict{NfToNfMor, Dict{nf_elem, nf_elem}}
  induced::Dict{NfToNfMor, Perm{Int}}
  embed_cache_triv::Vector{Dict{nf_elem, nf_elem}}
  nonredundant::Vector{Int}
  isoptimal::Int
  is_normal::BitArray{1} # if i-th subfield is normal

  function NormRelation{T}() where {T}
    z = new{T}()
    z.ispure = false
    z.is_abelian = false
    z.isgeneric = false
    z.denominator = 0
    z.embed_cache = Dict{Tuple{Int, Int}, Dict{nf_elem, nf_elem}}()
    z.mor_cache = Dict{NfToNfMor, Dict{nf_elem, nf_elem}}()
    z.induced = Dict{NfToNfMor, Perm{Int}}()
    z.isoptimal = -1
    return z
  end
end

function Base.show(io::IO, N::NormRelation)
  if !isdefined(N, :K)
    print(io, "Invalid norm relation")
    return
  end

  print(io, "Norm relation of\n  ", N.K, "\nof index ", index(N), " and the subfields")
  for i in 1:length(N)
    print(io, "\n  ", subfields(N)[i][1])
    N.is_normal[i] ? print(io, " (normal)") : nothing
  end
end

function _norm_relation_setup_abelian(K::AnticNumberField; small_degree::Bool = true, pure::Bool = true, index::ZZRingElem = zero(ZZRingElem))
  G = automorphism_list(K)
  A, GtoA, AtoG = Hecke.find_isomorphism_with_abelian_group(G);
  if iszero(index)
    subs = [f for f in subgroups(A) if order(f[1]) > 1]
  else
    subs = [f for f in subgroups(A) if order(f[1]) > 1 && order(f[1]) == index || order(f[1]) == index^2]
  end

  b, den, ls = Hecke._has_norm_relation_abstract(A, subs, large_index = !small_degree, pure = pure)
  @assert b
  n = length(ls)

  z = NormRelation{Int}()
  z.K = K
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = false

  for i in 1:n
    F, mF = Hecke.fixed_field1(K, NfToNfMor[AtoG[f] for f in ls[i][2]])
    S, mS = simplify(F, cached = false)
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

  z.is_abelian = true

  return z
end

function _norm_relation_for_sunits(K::AnticNumberField; small_degree::Bool = true,  pure::Bool = false, target_den::ZZRingElem = zero(ZZRingElem), max_degree::Int = degree(K))
  @vprint :NormRelation 1 "Computing automorphisms\n"
  A = automorphism_list(K)
  G, AtoG, GtoA = generic_group(A, *)
  if iszero(target_den)
     b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(G, conjugacy_classes = false) if order(f[1]) > 1 && div(order(G), order(f[1])) <= max_degree], pure = pure, large_index = small_degree)
  else
    b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(G, conjugacy_classes = false) if order(f[1]) > 1 && div(order(G), order(f[1])) <= max_degree], target_den = target_den, pure = pure, large_index = small_degree)
  end

  if !b
    @show find_small_group(G)
    error("Galois group does not admit Brauer relation")
  end

  nonredundant = trues(length(ls))

  for i in 1:length(ls)
    if !nonredundant[i]
      continue
    end
    for j = i+1:length(ls)
      if Base.issubset(ls[j][1], ls[i][1])
        nonredundant[i] = false
        break
      elseif Base.issubset(ls[i][1], ls[j][1])
        nonredundant[j] = false
      end
    end
  end
  nsubs = findall(nonredundant)
  n = length(nsubs)

  z = NormRelation{Int}()
  z.K = K
  z.is_normal = falses(n)
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = pure
  z.embed_cache_triv = Vector{Dict{nf_elem, nf_elem}}(undef, n)
  z.nonredundant = Int[i for i = 1:n]

  for i in 1:n
    z.embed_cache_triv[i] = Dict{nf_elem, nf_elem}()
  end

  @vprint :NormRelation 1 "Computing subfields\n"
  for i in 1:n
    @vprint :NormRelation 3 "Computing subfield $i / $n \n"
		auts = NfToNfMor[GtoA[f] for f in ls[nsubs[i]][1]]
    @vtime :NormRelation 3 F, mF = Hecke.fixed_field1(K, auts)
    @vprint :NormRelation 1 "Simplifying \n $F\n"
    @vtime :NormRelation 3 S, mS = simplify(F, cached = false)
    L = S
    mL = mS * mF
    z.subfields[i] = L, mL
    z.is_normal[i] = Hecke._isnormal(ls[i][1])
  end
  z.is_abelian = false

  return z
end

function _norm_relation_setup_generic(K::AnticNumberField; small_degree::Bool = true, pure::Bool = false, target_den::ZZRingElem = zero(ZZRingElem), max_degree::Int = degree(K))
  @vprint :NormRelation 1 "Computing automorphisms\n"
  A = automorphism_list(K)
  G, AtoG, GtoA = generic_group(A, *)
  if iszero(target_den)
     b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(G, conjugacy_classes = false) if order(f[1]) > 1 && div(order(G), order(f[1])) <= max_degree], pure = pure, large_index = small_degree)
  else
    b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(G, conjugacy_classes = false) if order(f[1]) > 1 && div(order(G), order(f[1])) <= max_degree], target_den = target_den, pure = pure, large_index = small_degree)
  end

  if !b
    @show find_small_group(G)
    error("Galois group does not admit Brauer relation")
  end
  n = length(ls)

  nonredundant = Dict{Int, Bool}()

  for i in 1:length(ls)
    red = false
    for j in keys(nonredundant)
      if Base.issubset(ls[j][1], ls[i][1])
        red = true
        break
      elseif Base.issubset(ls[i][1], ls[j][1])
        delete!(nonredundant, j)
        nonredundant[i] = true
      end
    end

    if !red
      nonredundant[i] = true
    end
  end

  z = NormRelation{Int}()
  z.K = K
  z.is_normal = falses(n)
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = pure
  z.embed_cache_triv = Vector{Dict{nf_elem, nf_elem}}(undef, n)
  z.nonredundant = collect(keys(nonredundant))

  for i in 1:n
    z.embed_cache_triv[i] = Dict{nf_elem, nf_elem}()
  end

  @vprint :NormRelation 1 "Computing subfields\n"
  for i in 1:n
    @vprint :NormRelation 3 "Computing subfield $i / $n \n"
		auts = NfToNfMor[GtoA[f] for f in ls[i][1]]
    @vtime :NormRelation 3 F, mF = Hecke.fixed_field1(K, auts)
    @vprint :NormRelation 1 "Simplifying \n $F\n"
    @vtime :NormRelation 3 S, mS = simplify(F, cached = false)
    L = S
    mL = mS * mF
    z.subfields[i] = L, mL
    z.is_normal[i] = Hecke._isnormal(ls[i][1])
  end

  z.coefficients_gen = Vector{Vector{Tuple{Int, NfToNfMor, NfToNfMor}}}(undef, n)

  for i in 1:n
    w = Vector{Tuple{Int, NfToNfMor, NfToNfMor}}(undef, length(ls[i][2]))
    for (j, (expo, auto_pre, auto_post)) in enumerate(ls[i][2])
      w[j] = (expo, GtoA[auto_pre], GtoA[auto_post])
    end
    z.coefficients_gen[i] = w
  end

  z.is_abelian = false

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
      z = z * N([Hecke.norm(embedding(N, i), auto(a)^exp) for  (exp, auto, _) in N.coefficients_gen[i]], i)
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

  z = SMat{ZZRingElem}[zero_matrix(SMat, FlintZZ, 0, length(S)) for i in 1:degree(field(N))]

  mk = embedding(N, i)
  zk = order(s[1])

  if length(cache) == 0
    cache = resize!(cache, length(s))
    cached = false
  else
    cached = true
  end

  autos = automorphism_list(field(N), copy = false)

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
      v = Tuple{Int, ZZRingElem}[]
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
      push!(z[i], sparse_row(FlintZZ, r, sort = false))
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

  @assert mod(degree(ZK), degree(zk)) == 0
  reldeg = divexact(degree(ZK), degree(zk))

  for l in 1:length(s)
    if cached
      v = cache[l]
    else
      v = Tuple{Int, ZZRingElem}[]
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
    push!(z, sparse_row(FlintZZ, r, sort = false))
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
    error("Not implemented yet")
  end
  ZK = order(S[1])
  z = zero_matrix(SMat, FlintZZ, 0, length(S))
  mk = embedding(N, i)
  for j in 1:length(s)
    v = Tuple{Int, ZZRingElem}[]
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

    push!(z, N.pure_coefficients[i] * sparse_row(FlintZZ, v, sort = false))
  end
  return z
end

one(T::FacElemMon{AnticNumberField}) = T()

function Hecke.simplify(c::Hecke.ClassGrpCtx)
  d = Hecke.class_group_init(c.FB, SMat{ZZRingElem}, add_rels = false)
  U = Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(order(d))

  Hecke.module_trafo_assure(c.M)
  trafos = c.M.trafo

  for i=1:length(c.FB.ideals)
    x = zeros(ZZRingElem, length(c.R_gen) + length(c.R_rel))
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
  d = Hecke.class_group_init(c.FB, SMat{ZZRingElem}, add_rels = false)
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
  rel = QQFieldElem[]
  for i in 1:length(N)
    v = N.coefficients_gen[i]
    push!(rel, QQFieldElem(v[1][1] * divexact(degree(N.K), degree(N.subfields[i][1]))) // index(N))
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
                                     index_bound::Int = -1,
                                     target_den::ZZRingElem = zero(ZZRingElem))
  if index_bound != -1
    H = [h for h in H if order(G) <= order(h[1]) * index_bound]
  end

  sort!(H, by = x -> order(x[1]))

  if large_index
    reverse!(H)
  end

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

      onee = matrix(FlintQQ, 1, n, coefficients(one(QG)))

      b, v, K = can_solve_with_kernel(m, onee, side = :left)
    else
      m = zero_matrix(FlintZZ, length(H), n)
      for i in 1:length(H)
        for j in 1:n
          m[i, j] = FlintZZ(norms[i].coeffs[j])
        end
      end

      onee = matrix(FlintZZ, 1, n, coefficients(one(QG)))

      b, w, K = can_solve_with_kernel(m, target_den * onee, side = :left)
      v = 1//target_den * change_base_ring(FlintQQ, w)
    end

    if !b
      return false, zero(FlintZZ), Vector{Tuple{Vector{Tuple{ZZRingElem, GrpAbFinGenElem}}, Vector{GrpAbFinGenElem}}}()
    end

    @assert b

    if iszero(target_den)
      v = _reduce_modulo(v, K)
    end

    subgroups_needed = Int[ i for i in 1:length(H) if !iszero(v[1, i])]

    den = denominator(v[1, 1])
    for i in 2:length(H)
      den = lcm!(den, den, denominator(v[1, i]))
    end

    vvv = Vector{Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}}(undef, length(subgroups_needed))
    for i in 1:length(vvv)
      vvv[i] = Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}()
    end

    solutions = Vector{Tuple{Vector{GrpGenElem}, Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}}}()

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
    return false, zero(FlintZZ), Vector{Tuple{Vector{Tuple{ZZRingElem, GrpAbFinGenElem}}, Vector{GrpAbFinGenElem}}}()
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
    lc = Hecke.left_cosets(G, H[subgroups_needed[i]][2])
    push!(left_cosets_for_sub, lc)
    NGH = Hecke.normalizer(G, H[subgroups_needed[i]][2])
    push!(right_cosets_for_normalizer, Hecke.right_cosets(G, NGH[2]))
  end

  if iszero(target_den)
    onee = matrix(FlintQQ, 1, n, coefficients(one(QG)))

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
    onee = matrix(FlintZZ, 1, n, coefficients(target_den * one(QG)))

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

  solutions = Vector{Tuple{Vector{GrpGenElem}, Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}}}()

  vvv = Vector{Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}}(undef, length(subgroups_needed))
  for i in 1:length(vvv)
    vvv[i] = Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}()
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
    if is_cyclic(H)
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
    if is_cyclic(H)
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
#  Get smallest norm relation coprime to something
#
################################################################################

function _smallest_scalar_norm_relation_coprime(G::GrpGen, m::ZZRingElem)

  primes = ZZRingElem[ p for (p, _) in factor(m)]

  S = localization(FlintZZ, primes)

  all_non_trivial_subs = [ (H, mH) for (H, mH) in subgroups(G) if order(H) > 1]

  sort!(all_non_trivial_subs, by = x -> order(x[1]))

  reverse!(all_non_trivial_subs)

  QG = AlgGrp(FlintQQ, G)
  norms_rev = Dict{elem_type(QG), Int}()
  norms = Vector{elem_type(QG)}(undef, length(all_non_trivial_subs))
  for i in 1:length(all_non_trivial_subs)
    norms_rev[sum([QG(all_non_trivial_subs[i][2](h)) for h in all_non_trivial_subs[i][1]])] = i
    norms[i] = sum([QG(all_non_trivial_subs[i][2](h)) for h in all_non_trivial_subs[i][1]])
  end

  n = Int(order(G))

  M = zero_matrix(S, length(all_non_trivial_subs), n)

  for i in 1:length(all_non_trivial_subs)
    for j in 1:n
      M[i, j] = norms[i].coeffs[j]
    end
  end

  onee = matrix(S, 1, n, coefficients(one(QG)))

  fl, v = can_solve_with_solution(M, onee, side = :left)

  if !fl
    solutions = Vector{Tuple{Vector{GrpGenElem}, Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}}}()
    return false, ZZRingElem(0), solutions
  end

  k = 0

  for i in 1:length(all_non_trivial_subs)
    fl, v = can_solve_with_solution(view(M, 1:i, 1:ncols(M)), onee, side = :left)
    if fl
      k = i
      break
    end
  end

  _,_, K = can_solve_with_kernel(view(M, 1:k, 1:ncols(M)), onee, side = :left)

  v = _reduce_modulo(v, K)

  subgroups_needed = Int[ i for i in 1:k if !iszero(v[1, i])]

  den = denominator(v[1, 1])
  for i in 2:k
    den = lcm!(den, den, denominator(v[1, i]))
  end

  @assert is_coprime(den, m)

  vvv = Vector{Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}}(undef, length(subgroups_needed))
  for i in 1:length(vvv)
    vvv[i] = Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}()
  end

  solutions = Vector{Tuple{Vector{GrpGenElem}, Vector{Tuple{ZZRingElem, GrpGenElem, GrpGenElem}}}}()

  for i in 1:length(subgroups_needed)
    push!(vvv[i], (numerator(den * v[1, subgroups_needed[i]]), id(G), id(G)))
    sgroup = [all_non_trivial_subs[subgroups_needed[i]][2](h) for h in all_non_trivial_subs[subgroups_needed[i]][1]]
    push!(solutions, (sgroup, vvv[i]))
  end

  z = zero(QG)
  for cc in 1:length(subgroups_needed)
    z = z + v[1, subgroups_needed[cc]].data * norms[subgroups_needed[cc]]
  end

  @assert isone(z)

  return true, den, solutions
end

function has_coprime_norm_relation(K::AnticNumberField, m::ZZRingElem)
  G, mG = automorphism_group(K)
  b, den, ls = _smallest_scalar_norm_relation_coprime(G, m)

  if !b
    return false, NormRelation{Int}()
  end

  nonredundant = Dict{Int, Bool}()

  for i in 1:length(ls)
    red = false
    for j in keys(nonredundant)
      if Base.issubset(ls[j][1], ls[i][1])
        red = true
        break
      elseif Base.issubset(ls[i][1], ls[j][1])
        delete!(nonredundant, j)
        nonredundant[i] = true
      end
    end

    if !red
      nonredundant[i] = true
    end
  end

  n = length(ls)

  z = NormRelation{Int}()
  z.K = K
  z.is_normal = falses(n)
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = true
  z.embed_cache_triv = Vector{Dict{nf_elem, nf_elem}}(undef, n)
  z.nonredundant = collect(keys(nonredundant))

  for i in 1:n
    z.embed_cache_triv[i] = Dict{nf_elem, nf_elem}()
  end

  for i in 1:n
    F, mF = Hecke.fixed_field1(K, NfToNfMor[mG(f) for f in ls[i][1]])
    S, mS = simplify(F, cached = false)
    L = S
    mL = mS * mF
    z.subfields[i] = L, mL
    z.is_normal[i] = Hecke._isnormal(ls[i][1])
  end

  z.coefficients_gen = Vector{Vector{Tuple{Int, NfToNfMor, NfToNfMor}}}(undef, n)

  for i in 1:n
    w = Vector{Tuple{Int, NfToNfMor, NfToNfMor}}(undef, length(ls[i][2]))
    for (j, (expo, auto_pre, auto_post)) in enumerate(ls[i][2])
      w[j] = (expo, mG(auto_pre), mG(auto_post))
    end
    z.coefficients_gen[i] = w
  end

  z.is_abelian = false
  z.isoptimal = m

  return true, z
end

function _reduce_modulo(v, K)
  H = hnf(K)
  w = deepcopy(v)
  for i in nrows(H):-1:1
    k = ncols(H)
    while iszero(H[i, k])
      k = k - 1
    end
    if !iszero(w[1, k])
      fl, c = divides(w[1, k], H[i, k])
      if fl
        for j in 1:ncols(H)
          w[1, j] = w[1, j] - c * H[i, j]
        end
      end
    end
  end
  return w
end
