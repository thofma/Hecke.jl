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

function _norm_relation_setup_abelian(K::AnticNumberField; small_degree::Bool = true)
  G = automorphisms(K)
  A, GtoA, AtoG = find_isomorphism_with_abelian_group(G, *);
  b, den, ls = _has_norm_relation_abstract(A, [f for f in subgroups(A) if order(f[1]) > 1], large_index = !small_degree)
  @assert b
  n = length(ls)

  z = NormRelation{Int}()
  z.K = K
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = false
 
  for i in 1:n
    F, mF = FixedField(K, NfToNfMor[AtoG[f] for f in ls[i][2]])
    S, mS = simplify(F)
    L = S
    mL = mF * mS
    z.subfields[i] = L, mL
  end

  z.coefficients = Vector{Vector{Tuple{NfToNfMor, Int}}}(undef, n)
  for i in 1:n
    w = Vector{Tuple{NfToNfMor, Int}}(undef, length(ls[i][1]))
    for (j, (expo, auto)) in enumerate(ls[i][1])
      w[j] = (AtoG[auto], expo)
    end
    z.coefficients[i] = w
  end

  z.isabelian = true

  return z
end

function _norm_relation_setup_generic(K::AnticNumberField; small_degree::Bool = true)
  A = automorphisms(K)
  G, AtoG, GtoA = generic_group(G, *);
  b, den, ls = _has_norm_relation_abstract(G, [f for f in subgroups(A) if order(f[1]) > 1])
  @assert b
  n = length(ls)

  z = NormRelation{Int}()
  z.K = K
  z.subfields = Vector{Tuple{AnticNumberField, NfToNfMor}}(undef, n)
  z.denominator = den
  z.ispure = false
 
  for i in 1:n
    F, mF = FixedField(K, NfToNfMor[GtoA[f] for f in ls[i][1]])
    S, mS = simplify(F)
    L = S
    mL = mF * mS
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

function image(f::NfToNfMor, a::FacElem{nf_elem, AnticNumberField})
  D = Dict{nf_elem, fmpz}(f(b) => e for (b, e) in a)
  return FacElem(D)
end

function check_relation(N::NormRelation, a::nf_elem)
  @assert !iszero(a)
  z = one(field(N))
  for i in 1:length(N)
    z = z * embedding(N, i)(norm(embedding(N, i), N(a, i)))
  end
  return a^index(N) == z
end

function (N::NormRelation)(x::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, i::Int)
  z = one(N.K)
  for (auto, expo) in N.coefficients[i]
    z = z * auto(x)^expo
  end
  return z
end

# TODO:
# If it is abelian, then a subgroup is redundant, if and only if the quotient group is not cyclic
# Use this to avoid endless recursions
function _has_norm_relation_abstract(G::GrpAb, H::Vector{Tuple{GrpAbFinGen, GrpAbFinGenMap}}; primitive::Bool = false, interactive::Bool = false, greedy::Bool = false, large_index::Bool = false)
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

  subgroups_needed = Int[]

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

  b, v, K = cansolve_with_nullspace(m', onee')

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

# TODO:
# If it is abelian, then a subgroup is redundant, if and only if the quotient group is not cyclic
# Use this to avoid endless recursions
function _has_norm_relation_abstract(G::GrpGen, H::Vector{Tuple{GrpGen, GrpGenToGrpGenMor}}; primitive::Bool = false, greedy::Bool = false, large_index::Bool = false)
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

  b, v, K = cansolve_with_nullspace(m', onee')

  @assert b

  # Now collect the coefficients again as elements of Q[G]
  sol = Vector{Tuple{Int, Int, Int, fmpq}}()
  for i in 1:length(subgroups_needed)
    for k in 1:n
      for l in 1:n
        if iszero(v[(i - 1)*n^2 + (k - 1) * n + l, 1])
          continue
        else
          push!(sol, (i, k, l, v[(i - 1)*n^2 + (k - 1) * n + l, 1]))
        end
      end
    end
  end

  @show sol

  z = zero(QG)
  for (i, k, l, x) in sol
    z = z + x * B[k] * norms[subgroups_needed[i]] * B[l]
  end

  @assert isone(z)

  den = one(FlintZZ)

  for (_,_,_,x) in sol
    den = lcm(den, denominator(x))
  end

  @show length(sol)

  solutions = Vector{Tuple{Vector{GrpGenElem}, Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}}}()
  solutions_as_group_element_arrays = Vector{Tuple{Vector{Tuple{fmpz, GrpAbFinGenElem}}, Vector{GrpAbFinGenElem}}}(undef, length(subgroups_needed))

  for i in 1:length(subgroups_needed)
    sgroup = [H[subgroups_needed[i]][2](h) for h in H[subgroups_needed[i]][1]]
    vv = Vector{Tuple{fmpz, GrpGenElem, GrpGenElem}}()
    for (k, g) in enumerate(group(QG))
      for (l, h) in enumerate(group(QG))
        if iszero(v[(i - 1)*n^2 + (k - 1) * n + l, 1])
          continue
        else
          push!(vv, (FlintZZ(den * v[(i - 1)*n^2 + (k - 1) * n + l, 1]), g, h))
        end
      end
    end
    push!(solutions, (sgroup, vv))
  end

  @show solutions

  return true, den, solutions
end

function _compute_class_group_with_relations(K::AnticNumberField, N::NormRelation, B::Int = factor_base_bound_grh(maximal_order(K)))
  ZK = maximal_order(K)
  c = Hecke.class_group_init(ZK, B, complete = false, add_rels = false, min_size = 0)
  cp = Set(minimum(x) for x = c.FB.ideals)

  for i = 1:length(N)
    k, mk = subfield(N, i)
    zk = maximal_order(k)
    print("Computing class group of $k... ")
    class_group(zk, use_aut = true)
    println("done")
    lp = prime_ideals_up_to(zk, Int(B), complete = false)
    lp = [ x for x = lp if minimum(x) in cp]
    println("Now computing the S-unit group for lp of length $(length(lp))")
    if length(lp) > 0
      S, mS = Hecke.sunit_group_fac_elem(lp)
    else
      S, mS = Hecke.unit_group_fac_elem(zk)
    end
    for j=2:ngens(S) # don't need torsion here - it's the "same" everywhere
      @show j,ngens(S)
      u = mS(S[j])  #do compact rep here???
      u = Hecke.compact_presentation(u, 2, decom = Dict((P, valuation(u, P)) for P = lp))
      Hecke.class_group_add_relation(c, FacElem(Dict((N(mk(x), i), v) for (x,v) = u.fac)))
    end
  end

  torsion_units(ZK)
  u = units(c)
  for (p, e) in factor(index(N))
    b = Hecke.saturate!(c, u, Int(p))
    while b
      b = Hecke.saturate!(c, u, Int(p))
    end
  end
  return c, u
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

function create_mat(K::T,A::Array{S,1}) where {T <: Union{AnticNumberField, Hecke.NfRel}, S <: Union{Hecke.NfRelElem, nf_elem}}
    arrtemp = [base_field(K)(0) for i in 1:degree(K)*length(A)];
    m = matrix(base_field(K),degree(K),length(A),arrtemp);
    for j in 1:length(A)
        artemp = [coeff(A[j],i) for i in 0:degree(K)-1];
        for i in 1:degree(K)
            m[i,j] = artemp[i];
        end
    end
    return m;
end

#returns array with base elems for Q(A)
function get_fieldbase(K::T, A::Array{S,1}) where {T <: Union{AnticNumberField, Hecke.NfRel}, S <: Union{nf_elem, Hecke.NfRelElem}}
    if length(A)<1
        return res=[K(1)]
    end
    f = minpoly(A[1]);
    res = Array{S,1}(undef,degree(f));
    ar_deg = Array{Int64,1}(undef,length(A));
    for i in 1:degree(f)
        res[i]=A[1]^(i-1)
    end
    ar_deg[1] = degree(f);
    matA = create_mat(K,res);
    for l in 2:length(A)
        matB = create_mat(K,[A[l]]);
        k=1;
        temp_k = A[l];
        while !cansolve(matA,matB)[1]
            res = vcat(res,[temp_k]);
            matA = hcat(matA,create_mat(K,[temp_k]));
            k=k+1;
            temp_k *= A[l];
            matB = create_mat(K,[temp_k]);
        end
        #println(res);
        ar_deg[l] = k;
        #println(ar_deg);
        deg_curr = 1;
        for i in 1:l
        deg_curr *= ar_deg[i];
        end
        indx = 1;
        while length(res) < deg_curr && indx < 2^length(res)-1
            temp_prod = digits(indx, base=2);
            xn = K(1);
            for i in 1:length(temp_prod)
                if temp_prod[i] == 1
                    xn *= res[i];
                end
            end
            matB = create_mat(K,[xn]);
            if !cansolve(matA,matB)[1]
                temp = [xn];
                res = vcat(res,temp);
                matA = hcat(matA,create_mat(K,temp));
            end
            indx += 1;
        end
    end
    return res
end

#returns minimal subfield of K containing Q and a
function subfield(K::T, a::S, b::String = "b") where {T <: Union{AnticNumberField, Hecke.NfRel}, S <: Union{nf_elem, Hecke.NfRelElem}}
    f = minpoly(a);
    L,b = NumberField(f,b, cached = false);
    return(L,hom(L,K,a));
end


#returns minimal subfield of K containing Q and A
function subfield(K::T, A::Array{P, 1}; alg::String = "Z", base::Bool = false) where {T <: Union{AnticNumberField, Hecke.NfRel}, P <: Union{nf_elem, Hecke.NfRelElem}}
 #use input array as base
    if base
        for i in 1:2^(length(A))-1
            temp = digits(i,base=2)
            s = K(0);
            for j in 1:length(temp)
                s += temp[j] * A[j];
            end
            #test primitive elem
            if (degree(minpoly(s))==length(A))
                return subfield(K,s)
            end
        end
        @error("Doch keine Basis");
    end

    B = get_fieldbase(K,A);
    #Zassenhaus
    if alg=="Z"
            for i in 1:2^(length(B))-1
                temp = digits(i,base=2)
                s = K(0);
                for j in 1:length(temp)
                    s += temp[j] * B[j];
                end
                #test primitive elem
                if (degree(minpoly(s))==length(B))
                    #println(s);
                    return subfield(K,s)
                end
            end
    end

    #Lenstra
    if alg=="L"
        G_ar = [minpoly(B[i]) for i in 1:length(B)];
        K_ar = Array{fmpz,1}(undef,length(B));
        D_ar = Array{fmpz,1}(undef,length(B)+1);
        D_ar[1] = 1;
        for i in 1:length(B)
            k = ZZ(1);
            for j in 1:degree(G_ar[i])
                k *= denominator(coeff(G_ar[1],j));
            end
            K_ar[i]=k;
            fi = G_ar[i]*x*K_ar[i]^(degree(G_ar[i])-1);
            dfi = ZZ(discriminant(fi));
            d=2
            while gcd(dfi,d^2)!=1
                d=d+1;
            end
            D_ar[i+1]=d;
        end
        D_ar = D_ar[1:length(B)];
        Al = [B[i]*K_ar[i] for i in 1:length(B)];
        D_ar = accumulate(*,D_ar);
        return subfield(K,Al'*D_ar)
    end
end


FixedField(K::T,S::M...) where {T <: Union{AnticNumberField, Hecke.NfRel}, M <: Union{NfToNfMor, Hecke.NfRelToNfRelMor}} = FixedField(K,[f for f in S])

function FixedField(K::T,S::Array{M,1}) where {T <: Union{AnticNumberField, Hecke.NfRel}, M <: Union{NfToNfMor, Hecke.NfRelToNfRelMor}}
    # calculates the fixed field of an field K corresponding to morphisms sigma

    if length(S)==0
        return K,M(K,K,gen(K))
    end
    F = base_field(K)
    a = gen(K);
    n = degree(K);
    ar_mat = Array{MatElem,1}(undef,length(S));
    for index in 1:length(S)
        as = S[index](a);
        ar_bs = [as^i for i in 0:n-1];
        ar_mat[index] = create_mat(K,ar_bs);
    end
    mat_ones = matrix(F,n,n,[F(0) for i in 1:n^2]);
    for i in 1:n
        mat_ones[i,i] = F(1);
    end
    mat_nulls = ar_mat[1] - mat_ones;
    for i in 2:length(S)
        mat_nulls = vcat(mat_nulls, ar_mat[i]-mat_ones);
    end
    nulls = nullspace(mat_nulls);
    nn = nulls[2]
    d = one(FlintZZ)
    for i in 1:nrows(nn)
      for j in 1:ncols(nn)
        d = lcm(d, denominator(nn[i, j]))
      end
    end
    nn = d * nn
    nn = matrix(FlintZZ, nn)
    #@show nn
    #@show nrows(nn), ncols(nn)
    nn = transpose(saturate(transpose(nn)))
    nn = lll(nn')'
    ar_fixed = Array{typeof(gen(K)),1}(undef,nulls[1]);
    for i in 1:nulls[1]
        ar_fixed[i] = K(0);
        for j in 1:degree(K)
            ar_fixed[i] += nn[j,i] * a^(j-1); #ident vectors with nf_elems
        end
    end
    return subfield(K,ar_fixed,alg = "Z",base = true) #ar_fixed is already base
end

base_field(K::AnticNumberField) = QQ
