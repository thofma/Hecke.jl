################################################################################
#
#  Integral norm equations
#
################################################################################

# Returns the solution of the norm equation and the number of the order, in which
# the solution was found.
function norm_equation(orders::Vector{<: AlgAssRelOrd}, a::AbsNumFieldOrderElem)
  A = algebra(orders[1])
  if iszero(a)
    return A(), 1
  end
  d, i = norm_equation_fac_elem(orders, a)
  return evaluate(d), i
end

function norm_equation_fac_elem(orders::Vector{<: AlgAssRelOrd}, a::AbsNumFieldOrderElem)
  A = algebra(orders[1])
  @assert !iszero(a) # We cannot represent 0 as a FacElem
  NC = NormCache(A, orders, a)
  while true
    # We test the orders alternately until we find a solution in one of them
    for i = 1:length(orders)
      b, d = _norm_equation_relative(NC, i)
      if b
        return d, i
      end
    end
  end
end

# This tests max_num_fields fields. If max_num_fields == 0, we try until we
# find a solution (although at some point NC.field_oracle does not return any
# new fields).
function _norm_equation_relative(NC::NormCache, order_num::Int; max_num_fields::Int = 10)
  A = NC.algebra
  n = NC.n
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

    K, KtoL = simplified_absolute_field(L)
    ktoK = restrict(inv(KtoL), base_field(L))
    OK = maximal_order_via_relative(K, KtoL)

    good_primes = __neq_find_good_primes(NC, OL)

    local vals2::Vector{Int}

    if !isempty(good_primes)
      if degree(L) != n
        n2 = degree(L)//n
        vals2 = [ Int(n2*vals[i]) for i = 1:length(vals) ]
      else
        vals2 = vals
      end

      remaining_primes = Set{Int}()
      # First search for solutions for single primes
      for p in good_primes
        sols = __neq_sunit(ktoK, eltype(primes)[ primes[p] ], Int[ vals2[p] ])
        if !isempty(sols)
          # We better evaluate s here: Some factors may not be integral which can
          # become a problem since the multiplication in A is non-commutative.
          # Also, multiplications and computing inverses in K are cheap.
          add_partial_solutions!(NC, order_num, Set(p), [ NC.fac_elem_mon(LtoA(KtoL(evaluate(s::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})))) for s in sols ])
        else
          push!(remaining_primes, p)
        end
      end

      if !isempty(remaining_primes)
        # Now the primes together, for which have not found a solution yet
        sols = __neq_sunit(ktoK, eltype(primes)[ primes[i] for i in remaining_primes ], Int[ vals2[i] for i in remaining_primes ])
        if !isempty(sols)
          add_partial_solutions!(NC, order_num, remaining_primes, [ NC.fac_elem_mon(LtoA(KtoL(evaluate(ss::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})))) for ss in sols ])
        elseif length(remaining_primes) < length(good_primes)
          # If this also failed, we test all primes together
          sols = __neq_sunit(ktoK, [ primes[i] for i in good_primes ], [ vals2[i] for i in good_primes ])
          if !isempty(sols)
            add_partial_solutions!(NC, order_num, good_primes, [ NC.fac_elem_mon(LtoA(KtoL(evaluate(ss::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})))) for ss in sols ])
          end
        end
      end
    end

    if !NC.GtoUk_surjective[order_num] && degree(L) == n
      UK, mUK = unit_group(OK)
      N = hom(UK, Uk, [ mUk\(norm(ktoK, K(mUK(g)))) for g in gens(UK) ])
      if ngens(G) == 0
        G = UK
        GtoUk = N
        push!(fields_in_product, (LtoA, KtoL))
        if is_surjective(GtoUk)
          NC.GtoUk_surjective[order_num] = true
        end
      else
        # Check whether this group brings anything new
        skip = true
        for g in gens(UK)
          b = has_preimage_with_preimage(GtoUk, N(g))[1]
          if !b
            skip = false
            break
          end
        end

        if !skip
          push!(fields_in_product, (LtoA, KtoL))

          G, pi = direct_product(G, UK, task = :prod)::Tuple{FinGenAbGroup, Tuple{FinGenAbGroupHom, FinGenAbGroupHom}}
          GtoUk = hom(gens(G), [ GtoUk(pi[1](g)) + N(pi[2](g)) for g in gens(G) ])
          if is_surjective(GtoUk)
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
      b, v = has_preimage_with_preimage(GtoUk, u)
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
#  Integral norm equations - valuations only
#
################################################################################

# A special case needed for principal_generator_eichler.
# Finds a in O such that v_{p_i}(normred(a)) == v_i where p_i = primes[i] and
# v_i = valuations[i] and such that v_q(normred(a)) == 0 for all other primes q,
# assuming that such an element exists.
function _norm_equation_valuations_only(O::AlgAssRelOrd, primes::Vector{<: AbsNumFieldOrderIdeal}, valuations::Vector{Int})
  @assert !isempty(primes)
  @assert length(primes) == length(valuations)
  A = algebra(O)
  _K = base_ring(A)
  Ok = order(primes[1])
  NC = NormCache(A, typeof(O)[ O ], Ok, primes, valuations)
  n = NC.n
  full_set = Set(1:length(primes))
  partial_solutions = NC.partial_solutions[1]

  while true
    LtoA = get_new_field(NC.field_oracle, 1, no_restriction = true)
    L = domain(LtoA)::_ext_type(elem_type(_K))
    OL = maximal_order(L)

    K, KtoL = simplified_absolute_field(L)
    ktoK = restrict(inv(KtoL), base_field(L))
    OK = maximal_order_via_relative(K, KtoL)

    good_primes = __neq_find_good_primes(NC, OL)

    if !isempty(good_primes)
      cache = Vector{Any}(undef, 3) # Used in __neq_find_sol_in_order
      if degree(L) != n
        n2 = degree(L)//n
        vals2 = Int[ Int(n2*valuations[i]) for i = 1:length(valuations) ]
      else
        vals2 = valuations
      end

      remaining_primes = Set{Int}()
      # First search for solutions for single primes
      for p in good_primes
        if haskey(partial_solutions, Set(p))
          continue
        end
        b, sss::elem_type(A) = __neq_find_sol_in_order(O, LtoA, KtoL, ktoK, eltype(primes)[ primes[p] ], eltype(vals2)[ vals2[p] ], cache)
        if b
          add_partial_solutions!(NC, 1, Set(p), [ NC.fac_elem_mon(sss) ])
        else
          push!(remaining_primes, p)
        end
      end

      if !isempty(remaining_primes) && !haskey(partial_solutions, remaining_primes)
        # Now the primes together, for which have not found a solution yet
        b, s = __neq_find_sol_in_order(O, LtoA, KtoL, ktoK, eltype(primes)[ primes[i] for i in remaining_primes ], [ vals2[i] for i in remaining_primes ], cache)
        if b
          add_partial_solutions!(NC, 1, remaining_primes, [ NC.fac_elem_mon(s) ])
        elseif length(remaining_primes) < length(good_primes)
          # If this also failed, we test all primes together
          b, s = __neq_find_sol_in_order(O, LtoA, KtoL, ktoK, eltype(primes)[ primes[i] for i in good_primes ], [ vals2[i] for i in good_primes ], cache)
          if b
            add_partial_solutions!(NC, 1, good_primes, [ NC.fac_elem_mon(s) ])
          end
        end
      end
    end

    if haskey(partial_solutions, full_set)
      s = first(partial_solutions[full_set])
      return s
    end
  end
end

# Finds any a \in O \cap L such that v_p(nr(a)) = vals[i] for p = primes[i].
function __neq_find_sol_in_order(O::AlgAssRelOrd, LtoA::NfRelToAbsAlgAssMor, KtoL::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}, ktoK::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}, primes_in_k::Vector{<: AbsNumFieldOrderIdeal}, vals::Vector{Int}, cache::Vector{Any})
  A = algebra(O)
  sols = __neq_sunit(ktoK, primes_in_k, vals)
  if isempty(sols)
    return false, A()
  end

  K = codomain(ktoK)
  L = domain(LtoA)
  sols_eval = Vector{elem_type(K)}()
  for s in sols
    s_eval = evaluate(s)
    t = LtoA(KtoL(s_eval))
    if t in O
      return true, t
    end
    push!(sols_eval, s_eval)
  end

  # None of the found solutions lies in O.
  # We assume that equation_order(L) \subseteq O and try to adjust one of the
  # elements of sols by a unit.
  OK = maximal_order(K)
  UK, mUK = unit_group(OK)
  if !isassigned(cache, 1)
    cache[1] = Order(K, [ KtoL\b for b in absolute_basis(equation_order(L)) ], check = false, isbasis = true)
  end
  OE = cache[1]
  if !isassigned(cache, 2)
    cache[2] = OO_mod_F_mod_O_mod_F(OE)
  end
  G, GtoQ, OKtoQ = cache[2]
  sols2 = Vector{elem_type(K)}()
  for s in s_eval
    sinQ = OKtoQ(OK(s))
    if !is_invertible(sinQ)[1]
      push!(s, sols2)
    end
    # s is coprime to the conductor

    g = GtoQ\sinQ
    h = hom(UK, G, [ GtoQ\(OKtoQ(mUK(UK[i]))) for i = 1:ngens(UK) ])
    b, u = has_preimage_with_preimage(h, g)
    if b
      Q, toQ = quo(UK, kernel(h)[1])
      u = toQ\(toQ(u)) # Reduce the coefficient size (hopefully)
      s = s*inv(elem_in_nf(mUK(u), copy = false))
      return true, LtoA(KtoL(s))
    end
  end

  if !isassigned(cache, 3)
    UE, mUE = unit_group(OE)
    UEinUK = [ mUK\(OK(elem_in_nf(mUE(UE[i]), copy = false))) for i = 1:ngens(UE) ]
    cache[3] = quo(UK, UEinUK)
  end
  Q, toQ = cache[3]
  for (i, g) in enumerate(Q)
    u = mUK(toQ\g)
    for s in sols2
      su = LtoA(KtoL(s*u))
      if su in O
        return true, su
      end
    end
  end
  return false, A()
end

################################################################################
#
#  Some helpers
#
################################################################################

# Let S be the set of primes lying over primes_in_k.
# This finds a set of representatives of the S-units of K modulo units of O_K,
# whose norm has the valuations vals at the primes primes_in_k.
function __neq_sunit(ktoK::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}, primes_in_k::Vector{<: AbsNumFieldOrderIdeal}, vals::Vector{Int})
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
  return elem_type(codomain(mSK))[ mSK(SK(sols[i, :])) for i in 1:nrows(sols) ]
end

function __neq_lift_unit(NC::NormCache, order_num::Int, g::FinGenAbGroupElem)
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
    h2 = pi(h)
    K = domain(KtoL)
    mUK = unit_group(maximal_order(K))[2]
    x *= LtoA(KtoL(elem_in_nf(mUK(h2), copy = false)))
  end
  return x
end

function __neq_find_good_primes(NC::NormCache, OL::RelNumFieldOrder)
  n = NC.n
  m = degree(nf(OL))
  mn = m//n
  good_primes = Set{Int}()
  for j = 1:length(NC.primes)
    v = NC.valuations[j]*mn
    if !isone(denominator(v))
      continue
    end
    p = NC.primes[j]
    pdec = prime_decomposition(OL, p, compute_uniformizer = false)
    for (q, e) in pdec
      if q.splitting_type[2] <= v
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
function _as_subfield(A::AbstractAssociativeAlgebra{T}, x::AbstractAssociativeAlgebraElem{T}) where { T <: Union{ QQFieldElem, AbsSimpleNumFieldElem, RelSimpleNumFieldElem } }
  return _as_subfield(A, x, minpoly(x))
end

function _as_subfield(A::AbstractAssociativeAlgebra{QQFieldElem}, x::AbstractAssociativeAlgebraElem{QQFieldElem}, f::PolyRingElem{QQFieldElem})
  s = one(A)
  M = zero_matrix(FlintQQ, degree(f), dim(A))
  elem_to_mat_row!(M, 1, s)
  for i = 2:degree(f)
    s = mul!(s, s, x)
    elem_to_mat_row!(M, i, s)
  end
  K = number_field(f)[1]
  return K, NfAbsToAbsAlgAssMor(K, A, M)
end

function _as_subfield(A::AbstractAssociativeAlgebra{T}, x::AbstractAssociativeAlgebraElem{T}, f::PolyRingElem{T}) where { T <: Union{ AbsSimpleNumFieldElem, RelSimpleNumFieldElem } }
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
function _issubmodule(modules::Vector{<: PMat}, O::RelNumFieldOrder, LtoA::NfRelToAbsAlgAssMor)
  L = domain(LtoA)
  A = codomain(LtoA)
  B = absolute_basis(O)
  M = zero_matrix(base_ring(A), length(B), dim(A))
  for i = 1:length(B)
    elem_to_mat_row!(M, i, LtoA(B[i]))
  end
  PM = pseudo_hnf_kb(pseudo_matrix(M), :lowerleft)
  for i = 1:nrows(PM)
    if !is_zero_row(PM.matrix, i)
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

function _issubmodule(modules::Vector{<: AlgAssAbsOrd}, O::AbsNumFieldOrder, LtoA::NfAbsToAbsAlgAssMor)
  L = domain(LtoA)
  A = codomain(LtoA)
  B = basis(O)
  result = Vector{Int}()
  for i = 1:length(modules)
    issub = true
    for b in B
      if !(LtoA(elem_in_nf(b, copy = false)) in modules[i])
        issub = false
        break
      end
    end
    if issub
      push!(result, i)
    end
  end
  return result
end

_issubmodule(FO::FieldOracle, OL::RelNumFieldOrder, LtoA::NfRelToAbsAlgAssMor) = _issubmodule(FO.hnf_basis_pmats, OL, LtoA)
_issubmodule(FO::FieldOracle, OL::AbsNumFieldOrder, LtoA::NfAbsToAbsAlgAssMor) = _issubmodule(FO.maximal_orders, OL, LtoA)

# Returns a LLL-reduced basis of O
function small_elements(O::AlgAssRelOrd)
  A = algebra(O)
  K = base_ring(A)
  B, BtoA = restrict_scalars(A, FlintQQ)
  pbO = pseudo_basis(O, copy = false)
  M = zero_matrix(FlintQQ, dim(B), dim(B))
  for i = 1:degree(O)
    for j = 1:degree(K)
      t = basis(pbO[i][2])[j]*pbO[i][1]
      elem_to_mat_row!(M, (i - 1)*degree(K) + j, BtoA\(t))
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

function small_elements(O::AlgAssAbsOrd)
  A = algebra(O)
  M = basis_matrix(O, copy = false)
  L = lll(M.num)
  res = Vector{elem_type(A)}()
  for i = 1:dim(A)
    t = elem_from_mat_row(A, L, i, M.den)
    push!(res, t)
  end
  return res
end

# Adds a field for order number i (and possibly for other orders too)
function add_field(FO::FieldOracle, i::Int; no_restriction::Bool = false)
  A = FO.algebra
  function _add_field(x::AbstractAssociativeAlgebraElem)
    f = minpoly(x)
    L, LtoA = _as_subfield(A, x, f)

    if no_restriction
      # The users wants no restriction on the fields. Let's hope he/she knows
      # what he/she is doing.
      for j = 1:length(FO.fields)
        push!(FO.fields[j], LtoA)
      end
      return true
    end

    # Find the orders in which maximal_order(L) lies
    good_orders = _issubmodule(FO, maximal_order(L), LtoA)
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
    if !is_integral(x)
      continue
    end
    if !is_irreducible(minpoly(x))
      continue
    end
    if _add_field(x)
      return nothing
    end
  end
end

# Returns a "new" field for order i
function get_new_field(FO::FieldOracle, i::Int; no_restriction::Bool = false)
  if isempty(FO.fields[i])
    add_field(FO, i, no_restriction = no_restriction)
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
