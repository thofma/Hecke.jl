################################################################################
#
#  Some types
#
################################################################################

# Given maximal orders O_1, ..., O_k in the algebra A over a field K, this
# helps to construct field extensions of K, whose maximal order is a submodule
# of one of the O_i.
mutable struct FieldOracle{S, T, U, M}
  algebra::S
  maximal_orders::Vector{T}

  hnf_basis_pmats::Vector{<: PMat}
  small_elements::Vector{U}
  fields::Vector{Vector{M}}
  phase::Int
  rounds::Int
  last_generated_field::Vector{Int}
  last_returned_field::Vector{Int}
  rand_coeff_bound::Int

  function FieldOracle{S, T, U, M}(A::S, orders::Vector{T}) where { S, T, U, M }
    z = new{S, T, U, M}()
    z.algebra = A
    z.maximal_orders = orders

    if A isa AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}
      # basis_pmatrices of orders are not required to be in HNF, so we compute them here
      z.hnf_basis_pmats = Vector{typeof(basis_pmatrix(orders[1], copy = false))}(undef, length(orders))
      for i = 1:length(orders)
        z.hnf_basis_pmats[i] = pseudo_hnf(basis_pmatrix(orders[i], copy = false), :lowerleft, true)
      end
    end

    z.small_elements = Vector{U}()
    for O in orders
      append!(z.small_elements, small_elements(O))
    end

    z.fields = Vector{Vector{M}}(undef, length(orders))

    for i = 1:length(orders)
      z.fields[i] = Vector{M}()
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

function FieldOracle(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, orders::Vector{<: AlgAssRelOrd})
  return FieldOracle{typeof(A), typeof(orders[1]), elem_type(A), NfRelToAbsAlgAssMor}(A, orders)
end

function FieldOracle(A::AbstractAssociativeAlgebra{QQFieldElem}, orders::Vector{<: AlgAssAbsOrd})
  return FieldOracle{typeof(A), typeof(orders[1]), elem_type(A), NfAbsToAbsAlgAssMor}(A, orders)
end

mutable struct NormCache{S, T, U, M, T2, T3}
  algebra::S
  maximal_orders::Vector{T}
  n::Int # n^2 == dim(algebra)

  field_oracle::FieldOracle{S, T, U, M}

  a::T2
  primes::Vector{T3}
  valuations::Vector{Int}
  fac_elem_mon::FacElemMon{S}
  partial_solutions::Vector{Dict{Set{Int}, Vector{FacElem{U, S}}}}
  solutions_mod_units::Vector{Dict{FacElem{U, S},  FinGenAbGroupElem}}

  # Only used if S <: AbstractAssociativeAlgebra{QQFieldElem}
  norm_minus_one::Vector{U}

  # These fields are only set if S <: AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}
  UktoOk::MapUnitGrp
  GtoUk::Vector{FinGenAbGroupHom}
  GtoUk_surjective::BitVector
  fields_in_product::Vector{Vector{Tuple{NfRelToAbsAlgAssMor, NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}}}}

  function NormCache{S, T, U, M, T2, T3}(A::S, orders::Vector{T}, a::T2) where { S <: AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, T, U, M, T2 <: AbsNumFieldOrderElem, T3}
    primes = collect(keys(factor(a*parent(a))))
    vals = [ valuation(a, p) for p in primes ]
    z = NormCache{S, T, U, M, T2, T3}(A, orders, parent(a), primes, vals)
    z.a = a
    return z
  end

  function NormCache{S, T, U, M, T2, T3}(A::S, orders::Vector{T}, a::T2) where { S <: AbstractAssociativeAlgebra{QQFieldElem}, T, U, M, T2 <: ZZRingElem, T3}
    primes = collect(keys(factor(a).fac))
    vals = [ valuation(a, p) for p in primes ]
    z = NormCache{S, T, U, M, T2, T3}(A, orders, primes, vals)
    z.a = a
    return z
  end

  function NormCache{S, T, U, M, T2, T3}(A::S, orders::Vector{T}, Ok::AbsNumFieldOrder, primes::Vector{T3}, valuations::Vector{Int}) where { S <: AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, T, U, M, T2, T3 }
    z = new{S, T, U, M, T2, T3}()
    z.algebra = A
    z.maximal_orders = orders
    z.n = isqrt(dim(A))
    @assert z.n^2 == dim(A)

    z.field_oracle = FieldOracle(A, orders)

    Uk, UktoOk = unit_group(Ok)
    z.UktoOk = UktoOk
    z.primes = primes
    z.valuations = valuations
    z.fac_elem_mon = FacElemMon(A)
    z.partial_solutions = Vector{Dict{Set{Int}, Vector{FacElem{U, S}}}}(undef, length(orders))
    z.solutions_mod_units = Vector{Dict{FacElem{U, S}, FinGenAbGroupElem}}(undef, length(orders))
    z.GtoUk = Vector{FinGenAbGroupHom}(undef, length(orders))
    z.GtoUk_surjective = falses(length(orders))
    z.fields_in_product = Vector{Vector{Tuple{NfRelToAbsAlgAssMor, NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}}}}(undef, length(orders))
    for i = 1:length(orders)
      z.partial_solutions[i] = Dict{Set{Int}, Vector{FacElem{U, S}}}()
      z.partial_solutions[i][Set{Int}()] = [ z.fac_elem_mon() ]
      z.solutions_mod_units[i] = Dict{FacElem{U, S}, FinGenAbGroupElem}()
      z.GtoUk[i] = hom([ FinGenAbGroup(ZZRingElem[])() ], [ Uk() ])
      z.fields_in_product[i] = Vector{Tuple{NfRelToAbsAlgAssMor, NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}}}()
    end

    return z
  end

  function NormCache{S, T, U, M, T2, T3}(A::S, orders::Vector{T}, primes::Vector{T3}, valuations::Vector{Int}) where { S <: AbstractAssociativeAlgebra{QQFieldElem}, T, U, M, T2, T3 }
    z = new{S, T, U, M, T2, T3}()
    z.algebra = A
    z.maximal_orders = orders
    z.n = isqrt(dim(A))
    @assert z.n^2 == dim(A)

    z.field_oracle = FieldOracle(A, orders)
    z.norm_minus_one = Vector{U}(undef, length(orders))

    z.primes = primes
    z.valuations = valuations
    z.fac_elem_mon = FacElemMon(A)
    z.partial_solutions = Vector{Dict{Set{Int}, Vector{FacElem{U, S}}}}(undef, length(orders))
    z.solutions_mod_units = Vector{Dict{FacElem{U, S}, FinGenAbGroupElem}}(undef, length(orders))
    for i = 1:length(orders)
      z.partial_solutions[i] = Dict{Set{Int}, Vector{FacElem{U, S}}}()
      z.partial_solutions[i][Set{Int}()] = [ z.fac_elem_mon() ]
      z.solutions_mod_units[i] = Dict{FacElem{U, S}, FinGenAbGroupElem}()
    end

    return z
  end
end

function NormCache(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, orders::Vector{<: AlgAssRelOrd}, a::AbsNumFieldOrderElem)
  return NormCache{typeof(A), typeof(orders[1]), elem_type(A), NfRelToAbsAlgAssMor, typeof(a), ideal_type(parent(a))}(A, orders, a)
end

function NormCache(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, orders::Vector{<: AlgAssRelOrd}, Ok::AbsNumFieldOrder, primes::Vector{<: AbsNumFieldOrderIdeal}, valuations::Vector{Int})
  return NormCache{typeof(A), typeof(orders[1]), elem_type(A), NfRelToAbsAlgAssMor, elem_type(Ok), ideal_type(Ok)}(A, orders, Ok, primes, valuations)
end

function NormCache(A::AbstractAssociativeAlgebra{QQFieldElem}, orders::Vector{<: AlgAssAbsOrd}, a::ZZRingElem)
  return NormCache{typeof(A), typeof(orders[1]), elem_type(A), NfAbsToAbsAlgAssMor, ZZRingElem, ZZRingElem}(A, orders, a)
end

function NormCache(A::AbstractAssociativeAlgebra{QQFieldElem}, orders::Vector{<: AlgAssAbsOrd}, primes::Vector{ZZRingElem}, valuations::Vector{Int})
  return NormCache{typeof(A), typeof(orders[1]), elem_type(A), NfAbsToAbsAlgAssMor, ZZRingElem, ZZRingElem}(A, orders, primes, valuations)
end

################################################################################
#
#  Integral norm equations
#
################################################################################

# Returns the solution of the norm equation and the number of the order, in which
# the solution was found.
function norm_equation(orders::Vector{<: AlgAssAbsOrd}, a::ZZRingElem)
  A = algebra(orders[1])
  if iszero(a)
    return A(), 1
  end
  d, i = norm_equation_fac_elem(orders, a)
  return evaluate(d), i
end

function norm_equation_fac_elem(orders::Vector{<: AlgAssAbsOrd}, a::ZZRingElem)
  A = algebra(orders[1])
  @assert !iszero(a) # We cannot represent 0 as a FacElem
  if isone(a)
    return one(A), 1
  end
  NC = NormCache(A, orders, a)
  while true
    # We test the orders alternately until we find a solution in one of them
    for i = 1:length(orders)
      b, d = _norm_equation_absolute(NC, i)
      if b
        return d, i
      end
    end
  end
end

# This tests max_num_fields fields. If max_num_fields == 0, we try until we
# find a solution (although at some point NC.field_oracle does not return any
# new fields).
function _norm_equation_absolute(NC::NormCache, order_num::Int; max_num_fields::Int = 10)
  A = NC.algebra
  n = NC.n
  primes = NC.primes
  vals = NC.valuations
  full_set = Set(1:length(primes))
  partial_solutions = NC.partial_solutions[order_num]
  solutions_mod_units = NC.solutions_mod_units[order_num]

  m = 0
  while max_num_fields == 0 || m < max_num_fields
    m += 1
    KtoA = get_new_field(NC.field_oracle, order_num)
    K = domain(KtoA)
    OK = maximal_order(K)

    good_primes = __neq_find_good_primes(NC, OK)

    if !isempty(good_primes)
      if degree(K) != n
        n2 = degree(K)//n
        vals2 = [ Int(n2*vals[i]) for i = 1:length(vals) ]
      else
        vals2 = vals
      end

      remaining_primes = Set{Int}()
      # First search for solutions for single primes
      for p in good_primes
        sols = __neq_sunit(K, [ primes[p] ], [ vals2[p] ])
        if !isempty(sols)
          # We better evaluate s here: Some factors may not be integral which can
          # become a problem since the multiplication in A is non-commutative.
          # Also, multiplications and computing inverses in K are cheap.
          add_partial_solutions!(NC, order_num, Set(p), [ NC.fac_elem_mon(KtoA(evaluate(s))) for s in sols ])
        else
          push!(remaining_primes, p)
        end
      end

      if !isempty(remaining_primes)
        # Now the primes together, for which have not found a solution yet
        sols = __neq_sunit(K, [ primes[i] for i in remaining_primes ], [ vals2[i] for i in remaining_primes ])
        if !isempty(sols)
          add_partial_solutions!(NC, order_num, remaining_primes, [ NC.fac_elem_mon(KtoA(evaluate(s))) for s in sols ])
        elseif length(remaining_primes) < length(good_primes)
          # If this also failed, we test all primes together
          sols = __neq_sunit(K, [ primes[i] for i in good_primes ], [ vals2[i] for i in good_primes ])
          if !isempty(sols)
            add_partial_solutions!(NC, order_num, good_primes, [ NC.fac_elem_mon(KtoA(evaluate(s))) for s in sols ])
          end
        end
      end
    end

    if degree(K) == n
      UK, mUK = unit_group_fac_elem(OK)
      i = findfirst(x -> norm(mUK(x)) == -1, gens(UK))
      if i !== nothing
        NC.norm_minus_one[order_num] = KtoA(evaluate(mUK(UK[i])))
      end
    end

    if !haskey(partial_solutions, full_set)
      continue
    end

    sols = partial_solutions[full_set]
    for s in sols
      if normred(s) != NC.a
        if !isassigned(NC.norm_minus_one, order_num)
          continue
        end
        s *= NC.norm_minus_one[order_num]
      end
      return true, s
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
function _norm_equation_valuations_only(O::AlgAssAbsOrd, primes::Vector{ZZRingElem}, valuations::Vector{Int})
  @assert !isempty(primes)
  @assert length(primes) == length(valuations)
  A = algebra(O)
  NC = NormCache(A, [ O ], primes, valuations)
  n = NC.n
  full_set = Set(1:length(primes))
  partial_solutions = NC.partial_solutions[1]

  while true
    KtoA = get_new_field(NC.field_oracle, 1, no_restriction = true)
    K = domain(KtoA)
    OK = maximal_order(K)

    good_primes = __neq_find_good_primes(NC, OK)

    if !isempty(good_primes)
      cache = Vector{Any}(undef, 2) # Used in __neq_find_sol_in_order
      if degree(K) != n
        n2 = degree(K)//n
        vals2 = [ Int(n2*valuations[i]) for i = 1:length(valuations) ]
      else
        vals2 = valuations
      end

      remaining_primes = Set{Int}()
      # First search for solutions for single primes
      for p in good_primes
        if haskey(partial_solutions, Set(p))
          continue
        end
        b, s = __neq_find_sol_in_order(O, KtoA, [ primes[p] ], [ vals2[p] ], cache)
        if b
          add_partial_solutions!(NC, 1, Set(p), [ NC.fac_elem_mon(s) ])
        else
          push!(remaining_primes, p)
        end
      end

      if !isempty(remaining_primes) && !haskey(partial_solutions, remaining_primes)
        # Now the primes together, for which have not found a solution yet
        b, s = __neq_find_sol_in_order(O, KtoA, [ primes[i] for i in remaining_primes ], [ vals2[i] for i in remaining_primes ], cache)
        if b
          add_partial_solutions!(NC, 1, remaining_primes, [ NC.fac_elem_mon(s) ])
        elseif length(remaining_primes) < length(good_primes)
          # If this also failed, we test all primes together
          b, s = __neq_find_sol_in_order(O, KtoA, [ primes[i] for i in good_primes ], [ vals2[i] for i in good_primes ], cache)
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

# Finds any a \in O \cap K such that v_p(nr(a)) = vals[i] for p = primes[i].
function __neq_find_sol_in_order(O::AlgAssAbsOrd, KtoA::NfAbsToAbsAlgAssMor, primes::Vector{ZZRingElem}, vals::Vector{Int}, cache::Vector{Any})
  A = algebra(O)
  K = domain(KtoA)
  sols = __neq_sunit(K, primes, vals)
  if isempty(sols)
    return false, A()
  end

  K = domain(KtoA)
  sols_eval = Vector{elem_type(K)}()
  for s in sols
    s_eval = evaluate(s)
    t = KtoA(s_eval)
    if t in O
      return true, t
    end
    push!(sols_eval, s_eval)
  end

  # None of the found solutions lies in O.
  # We assume that equation_order(K) \subseteq O and try to adjust one of the
  # elements of sols by a unit.
  OK = maximal_order(K)
  UK, mUK = unit_group(OK)
  OE = equation_order(K)
  if !isassigned(cache, 1)
    cache[1] = OO_mod_F_mod_O_mod_F(OE)
  end
  G, GtoQ, OKtoQ = cache[1]
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
      return true, KtoA(s)
    end
  end

  if !isassigned(cache, 2)
    UE, mUE = unit_group(OE)
    UEinUK = [ mUK\(OK(elem_in_nf(mUE(UE[i]), copy = false))) for i = 1:ngens(UE) ]
    cache[2] = quo(UK, UEinUK)
  end
  Q, toQ = cache[2]
  for (i, g) in enumerate(Q)
    u = mUK(toQ\g)
    for s in sols2
      su = KtoA(s*u)
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

# Let S be the set of primes lying over primes.
# This finds a set of representatives of the S-units of K modulo units of O_K,
# whose norm has the valuations vals at the primes primes.
function __neq_sunit(K::AbsSimpleNumField, primes::Vector{ZZRingElem}, vals::Vector{Int})
  OK = maximal_order(K)
  primes_in_K = prime_ideals_over(OK, primes)
  class_group(K)
  SK, mSK = sunit_mod_units_group_fac_elem(primes_in_K)
  M = zero_matrix(FlintZZ, length(primes), ngens(SK))
  N = zero_matrix(FlintZZ, length(primes_in_K), ngens(SK))
  b = zero_matrix(FlintZZ, length(primes), 1)
  for c = 1:ngens(SK)
    g = mSK(SK[c])
    ng = norm(g)
    for r = 1:length(primes)
      M[r, c] = valuation(ng, primes[r])
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

function __neq_find_good_primes(NC::NormCache, OK::AbsNumFieldOrder)
  n = NC.n
  m = degree(nf(OK))
  mn = m//n
  good_primes = Set{Int}()
  for j = 1:length(NC.primes)
    v = NC.valuations[j]*mn
    if !isone(denominator(v))
      continue
    end
    p = NC.primes[j]
    pdec = prime_decomposition(OK, p)
    for (q, e) in pdec
      if q.splitting_type[2] <= v
        push!(good_primes, j)
        break
      end
    end
  end
  return good_primes
end
