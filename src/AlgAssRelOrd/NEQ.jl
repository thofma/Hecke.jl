################################################################################
#
#  Some types
#
################################################################################

# Given maximal order O_1, ..., O_k in the algebra A over a field K, this
# helps to construct field extensions of K of degree sqrt(dim(A)), whose
# maximal order is a submodule of one of the O_i.
mutable struct FieldOracle{S, T, U}
  algebra::S
  maximal_orders::Vector{T}

  hnf_basis_pmats::Vector{<: PMat}
  small_elements::Vector{U}
  fields::Vector{Vector{NfRelToAbsAlgAssMor}}
  phase::Int
  rounds::Int
  last_generated_field::Vector{Int}
  last_returned_field::Vector{Int}
  rand_coeff_bound::Int

  function FieldOracle{S, T, U}(A::S, orders::Vector{T}) where { S, T, U}
    z = new{S, T, U}()
    z.algebra = A
    z.maximal_orders = orders

    # basis_pmatrices of orders are not required to be in HNF, so we compute them here
    z.hnf_basis_pmats = Vector{typeof(basis_pmatrix(orders[1], copy = false))}(undef, length(orders))
    for i = 1:length(orders)
      z.hnf_basis_pmats[i] = pseudo_hnf(basis_pmatrix(orders[i], copy = false), :lowerleft, true)
    end
    z.small_elements = Vector{elem_type(A)}()
    for O in orders
      append!(z.small_elements, small_elements(O))
    end

    z.fields = Vector{Vector{NfRelToAbsAlgAssMor}}(undef, length(orders))

    for i = 1:length(orders)
      z.fields[i] = Vector{NfRelToAbsAlgAssMor}()
    end

    z.phase = 1
    # Phase 1: Construct fields using all possible sums of elements in
    #          small_elements with <= z.rounds summands.
    # Phase 2: Use random linear combinations of elements in small_elements.

    z.rounds = 10 # Magic number
    z.last_generated_field = zeros(Int, z.rounds)
    z.last_returned_field = zeros(Int, length(orders))
    z.rand_coeff_bound = Int(ceil(log(length(z.small_elements), 10^6))) # So we get around 10^6 random fields. Hopefully that's enough.

    return z
  end
end

function FieldOracle(A::AbsAlgAss, orders::Vector{<: AlgAssRelOrd})
  return FieldOracle{typeof(A), typeof(orders[1]), elem_type(A)}(A, orders)
end

mutable struct NormCache{S, T, U}
  algebra::S
  maximal_orders::Vector{T}

  field_oracle::FieldOracle{S, T, U}

  a::NfAbsOrdElem
  primes::Vector{NfAbsOrdIdl}
  valuations::Vector{Int}
  fac_elem_mon::FacElemMon{S}
  partial_solutions::Vector{Dict{Set{Int}, Vector{FacElem{U, S}}}}
  solutions_mod_units::Vector{Dict{FacElem{U, S},  GrpAbFinGenElem}}
  UktoOk::MapUnitGrp
  GtoUk::Vector{GrpAbFinGenMap}
  GtoUk_surjective::BitVector
  fields_in_product::Vector{Vector{Tuple{NfRelToAbsAlgAssMor, NfToNfRel}}}

  function NormCache{S, T, U}(A::S, orders::Vector{T}, a::NfAbsOrdElem) where { S, T, U}
    z = new{S, T, U}()
    z.algebra = A
    z.maximal_orders = orders
    z.field_oracle = FieldOracle(A, orders)

    Ok = parent(a)
    Uk, UktoOk = unit_group(Ok)
    z.UktoOk = UktoOk
    z.a = a
    z.primes = collect(keys(factor(a*Ok)))
    z.valuations = [ valuation(a, p) for p in z.primes ]
    z.fac_elem_mon = FacElemMon(A)
    z.partial_solutions = Vector{Dict{Set{Int}, Vector{FacElem{U, S}}}}(undef, length(orders))
    z.solutions_mod_units = Vector{Dict{FacElem{U, S}, GrpAbFinGenElem}}(undef, length(orders))
    z.GtoUk = Vector{GrpAbFinGenMap}(undef, length(orders))
    z.GtoUk_surjective = falses(length(orders))
    z.fields_in_product = Vector{Vector{Tuple{NfRelToAbsAlgAssMor, NfToNfRel}}}(undef, length(orders))
    for i = 1:length(orders)
      z.partial_solutions[i] = Dict{Set{Int}, Vector{FacElem{U, S}}}()
      z.partial_solutions[i][Set{Int}()] = [ z.fac_elem_mon() ]
      z.solutions_mod_units[i] = Dict{FacElem{U, S}, GrpAbFinGenElem}()
      z.GtoUk[i] = hom([ GrpAbFinGen(fmpz[])() ], [ Uk() ])
      z.fields_in_product[i] = Vector{Tuple{NfRelToAbsAlgAssMor, NfToNfRel}}()
    end

    return z
  end
end

function NormCache(A::AbsAlgAss, orders::Vector{<: AlgAssRelOrd}, a::NfAbsOrdElem)
  return NormCache{typeof(A), typeof(orders[1]), elem_type(A)}(A, orders, a)
end

################################################################################
#
#  Integral norm equations
#
################################################################################

# Returns the solution of the norm equation and the number of the order, in which
# the solution was found.
function norm_equation(orders::Vector{ <: AlgAssRelOrd }, a::NfAbsOrdElem)
  A = algebra(orders[1])
  if iszero(a)
    return A(), 1
  end
  d, i = norm_equation_fac_elem(orders, a)
  return evaluate(d), i
end

function norm_equation_fac_elem(orders::Vector{ <: AlgAssRelOrd }, a::NfAbsOrdElem)
  A = algebra(orders[1])
  @assert !iszero(a) # We cannot represent 0 as a FacElem
  NC = NormCache(A, orders, a)
  while true
    # We test the orders alternately until we find a solution in one of them
    for i = 1:length(orders)
      b, d = _norm_equation(NC, i)
      if b
        return d, i
      end
    end
  end
end

# This tests max_num_fields fields. If max_num_fields == 0, we try until we
# find a solution (although at some point NC.field_oracle does not return any
# new fields).
function _norm_equation(NC::NormCache, order_num::Int; max_num_fields::Int = 10)
  A = NC.algebra
  primes = NC.primes
  vals = NC.valuations
  full_set = Set(1:length(primes))
  Ok = parent(NC.a)
  mUk = NC.UktoOk
  Uk = domain(mUk)
  partial_solutions = NC.partial_solutions[order_num]
  solutions_mod_units = NC.solutions_mod_units[order_num]
  GtoUk = NC.GtoUk[order_num]
  G = domain(GtoUk)
  fields_in_product = NC.fields_in_product[order_num]

  m = 0
  while max_num_fields == 0 || m < max_num_fields
    m += 1
    LtoA = get_new_field(NC.field_oracle, order_num)
    L = domain(LtoA)
    OL = maximal_order(L)

    K, KtoL, ktoK = simplified_absolute_field(L)
    OK = maximal_order_via_relative(K, KtoL)

    good_primes = __neq_find_good_primes(NC, OL)

    if !isempty(good_primes)
      sols = __neq_sunit(ktoK, [ primes[i] for i in good_primes ], [ vals[i] for i in good_primes ])
      if !isempty(sols)
        # We better evaluate s here: Some factors may not be integral which can
        # become a problem since the multiplication in A is non-commutative.
        # Also, multiplications and computing inverses in K are cheap.
        add_partial_solutions!(NC, order_num, good_primes, [ NC.fac_elem_mon(LtoA(KtoL(evaluate(s)))) for s in sols ])
      end
    end

    if !NC.GtoUk_surjective[order_num]
      UK, mUK = unit_group(OK)
      N = hom(UK, Uk, [ mUk\(norm(ktoK, K(mUK(g)))) for g in gens(UK) ])
      if ngens(G) == 0
        G = UK
        GtoUk = N
        push!(fields_in_product, (LtoA, KtoL))
        if issurjective(GtoUk)
          NC.GtoUk_surjective[order_num] = true
        end
      else
        # Check whether this group brings anything new
        skip = true
        for g in gens(UK)
          b = haspreimage(GtoUk, N(g))[1]
          if !b
            skip = false
            break
          end
        end

        if !skip
          push!(fields_in_product, (LtoA, KtoL))

          G, pi = direct_product(G, UK, task = :prod)
          GtoUk = hom(gens(G), [ GtoUk(pi[1](g)) + N(pi[2](g)) for g in gens(G) ])
          if issurjective(GtoUk)
            NC.GtoUk_surjective[order_num] = true
          end
        end
      end
      NC.GtoUk[order_num] = GtoUk
    end

    if !haskey(partial_solutions, full_set)
      continue
    end

    sols = partial_solutions[full_set]
    for s in sols
      u = get!(solutions_mod_units, s) do
        return mUk\divexact(NC.a, Ok(normred(s)))
      end
      b, v = haspreimage(GtoUk, u)
      if !b
        continue
      end
      x = __neq_lift_unit(NC, order_num, v)
      return true, s*x
    end
  end
  return false, NC.fac_elem_mon()
end

################################################################################
#
#  Some helpers
#
################################################################################

# Let S be the set of primes lying over primes_in_k.
# This finds a set of representatives of the S-units of K modulo units of O_K,
# whose norm has the valuations vals at the primes primes_in_k.
function __neq_sunit(ktoK::NfToNfMor, primes_in_k::Vector{ <: NfAbsOrdIdl}, vals::Vector{Int})
  K = codomain(ktoK)
  OK = maximal_order(K)
  primes_in_K = Vector{ideal_type(OK)}()
  for p in primes_in_k
    p1 = minimum(p)
    p2 = uniformizer(p)
    @assert p == p1*order(p) + p2*order(p)
    P = p1*OK + OK(ktoK(elem_in_nf(p2, copy = false)))*OK
    append!(primes_in_K, collect(keys(factor(P))))
  end
  class_group(K)
  SK, mSK = sunit_mod_units_group_fac_elem(primes_in_K)
  M = zero_matrix(FlintZZ, length(primes_in_k), ngens(SK))
  N = zero_matrix(FlintZZ, length(primes_in_K), ngens(SK))
  b = zero_matrix(FlintZZ, length(primes_in_k), 1)
  for c = 1:ngens(SK)
    g = mSK(SK[c])
    ng = norm(ktoK, g)
    for r = 1:length(primes_in_k)
      M[r, c] = valuation(ng, primes_in_k[r])
      b[r, 1] = vals[r]
    end
    for r = 1:length(primes_in_K)
      N[r, c] = valuation(g, primes_in_K[r])
    end
  end

  sols = try
    solve_mixed(M, b, N)
  catch e
    if e isa UndefVarError
      error("This function requires Polymake.jl (original error message follows)")
    else
      rethrow(e)
    end
  end
  return elem_type(codomain(mSK))[ mSK(SK(s)) for s in sols ]
end

function __neq_lift_unit(NC::NormCache, order_num::Int, g::GrpAbFinGenElem)
  if isone(g)
    return one(NC.algebra)
  end

  fields_in_product = NC.fields_in_product[order_num]
  G = domain(NC.GtoUk[order_num])
  if length(fields_in_product) == 1
    LtoA, KtoL = fields_in_product[1]
    K = domain(KtoL)
    mUK = unit_group(maximal_order(K))[2]
    return LtoA(KtoL(elem_in_nf(mUK(g), copy = false)))
  end

  GtoH = flat(G)
  H = codomain(GtoH)
  h = GtoH(g)
  x = NC.fac_elem_mon()
  for j = 1:length(fields_in_product)
    LtoA, KtoL = fields_in_product[j]
    pi = canonical_projection(H, j)
    h = pi(h)
    K = domain(KtoL)
    mUK = unit_group(maximal_order(K))[2]
    x *= LtoA(KtoL(elem_in_nf(mUK(h), copy = false)))
  end
  return x
end

function __neq_find_good_primes(NC::NormCache, OL::NfRelOrd, verbose::Bool = false)
  good_primes = Set{Int}()
  for j = 1:length(NC.primes)
    p = NC.primes[j]
    pdec = prime_decomposition(OL, p, compute_uniformizer = false)
    for (q, e) in pdec
      if q.splitting_type[2] <= NC.valuations[j]
        push!(good_primes, j)
        break
      end
    end
  end
  return good_primes
end

################################################################################
#
#  Functions for FieldOracle and NormCache
#
################################################################################

# Let K = base_ring(A). Then this returns the field K(x) and a map to A.
function _as_subfield(A::AbsAlgAss{T}, x::AbsAlgAssElem{T}) where { T <: Union{ nf_elem, NfRelElem } }
  return _as_subfield(A, x, minpoly(x))
end

function _as_subfield(A::AbsAlgAss{T}, x::AbsAlgAssElem{T}, f::PolyElem{T}) where { T <: Union{ nf_elem, NfRelElem } }
  s = one(A)
  M = zero_matrix(base_ring(A), degree(f), dim(A))
  elem_to_mat_row!(M, 1, s)
  for i = 2:degree(f)
    s = mul!(s, s, x)
    elem_to_mat_row!(M, i, s)
  end
  K = number_field(f)[1]
  return K, NfRelToAbsAlgAssMor(K, A, M)
end

# The matrices in modules should generate full lattices in A.
# This returns the numbers of the modules of which LtoA(O) is a submodule.
function _issubmodule(modules::Vector{ <: PMat}, O::NfRelOrd, LtoA::NfRelToAbsAlgAssMor)
  L = domain(LtoA)
  A = codomain(LtoA)
  B = absolute_basis(O)
  M = zero_matrix(base_ring(A), length(B), dim(A))
  for i = 1:length(B)
    elem_to_mat_row!(M, i, LtoA(B[i]))
  end
  PM = pseudo_hnf_kb(PseudoMatrix(M), :lowerleft)
  for i = 1:nrows(PM)
    if !iszero_row(PM.matrix, i)
      PM = sub(PM, i:nrows(PM), 1:ncols(PM))
      break
    end
  end
  result = Vector{Int}()
  for i = 1:length(modules)
    if _spans_subset_of_pseudohnf(PM, modules[i], :lowerleft)
      push!(result, i)
    end
  end
  return result
end

# Returns a LLL-reduced basis of O
function small_elements(O::AlgAssRelOrd)
  A = algebra(O)
  K = base_ring(A)
  B, AtoB, BtoA = restrict_scalars(A, FlintQQ)
  pbO = pseudo_basis(O, copy = false)
  M = zero_matrix(FlintQQ, dim(B), dim(B))
  for i = 1:degree(O)
    for j = 1:degree(K)
      t = basis(pbO[i][2])[j]*pbO[i][1]
      elem_to_mat_row!(M, (i - 1)*degree(K) + j, AtoB(t))
    end
  end
  MM = FakeFmpqMat(M)
  L = lll(MM.num)
  res = Vector{elem_type(A)}()
  for i = 1:dim(B)
    t = elem_from_mat_row(B, L, i, MM.den)
    push!(res, BtoA(t))
  end
  return res
end

# Adds a field for order number i (and possibly for other orders too)
function add_field(FO::FieldOracle, i::Int)
  A = FO.algebra
  function _add_field(x::AbsAlgAssElem)
    f = minpoly(x)
    if degree(f)^2 != dim(A)
      return false
    end

    L, LtoA = _as_subfield(A, x, f)
    # Find the orders in which maximal_order(L) lies
    good_orders = _issubmodule(FO.hnf_basis_pmats, maximal_order(L), LtoA)
    for o in good_orders
      push!(FO.fields[o], LtoA)
    end
    if i in good_orders
      # We found one in the order we wanted
      return true
    end
    return false
  end

  function _increase_counter(k::Int)
    j = FO.last_generated_field[k]
    if j != length(FO.small_elements) - FO.rounds + k
      FO.last_generated_field[k] += 1
      return true
    end

    if k == 1
      return false
    end

    b = _increase_counter(k - 1)
    if !b
      return false
    end
    FO.last_generated_field[k] = FO.last_generated_field[k - 1] + 1
    return true
  end

  while true
    if FO.phase == 1
      if !_increase_counter(FO.rounds)
        FO.phase = 2
        continue
      end
      x = sum([ j != 0 ? FO.small_elements[j] : zero(A) for j in FO.last_generated_field ])
    else
      coeffs = rand(-FO.rand_coeff_bound:FO.rand_coeff_bound, length(FO.small_elements))
      x = sum( coeffs[i]*FO.small_elements[i] for i = 1:length(FO.small_elements) )
    end
    if !isintegral(x)
      continue
    end
    if _add_field(x)
      return nothing
    end
  end
end

# Returns a "new" field for order i
function get_new_field(FO::FieldOracle, i::Int)
  if isempty(FO.fields[i])
    add_field(FO, i)
  end

  return pop!(FO.fields[i])
end

function add_partial_solutions!(NC::NormCache{T1, T2, T3}, order_num::Int, S::Set{Int}, sols::Vector{FacElem{T3, T1}}) where { T1, T2, T3 }
  partial_solutions = NC.partial_solutions[order_num]
  @assert haskey(partial_solutions, Set{Int}())
  for T in keys(partial_solutions)
    if !isempty(intersect(S, T))
      continue
    end

    ST = union(S, T)
    sols2 = Vector{FacElem{T3, T1}}()
    for b in sols
      for c in partial_solutions[T]
        bc = b*c
        push!(sols2, bc)
      end
    end
    if haskey(partial_solutions, ST)
      append!(partial_solutions[ST], sols2)
    else
      partial_solutions[ST] = sols2
    end
  end
  return nothing
end
