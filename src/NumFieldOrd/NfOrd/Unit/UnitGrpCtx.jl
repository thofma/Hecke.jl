################################################################################
#
#  Field access
#
################################################################################

order(u::UnitGrpCtx) = u.order
nf(u::UnitGrpCtx) = nf(order(u))

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, U::UnitGrpCtx)
  print(io, "Unit group context of\n$(order(U))")
end

################################################################################
#
#  Initialization
#
################################################################################

function _unit_group_init(O::AbsSimpleNumFieldOrder)
  u = UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(O)
  return u
end

function _search_rational_relation(U::UnitGrpCtx{S}, y::S, bound::ZZRingElem) where S
  p = _rel_add_precision(U)
  r = rank(U)

  @v_do :UnitGroup 1 pushindent()
  p, B = _conj_log_mat_cutoff_inv(U, p)

  @v_do :UnitGroup 1 popindent()
  @vprintln :UnitGroup 2 "Precision is now $p"

  Ar = base_ring(B)
  b = zero_matrix(Ar, 1, r)
  conlog = conjugates_arb_log(y, p)
  for i in 1:r
    b[1, i] = conlog[i]
  end

  @vprintln :UnitGroup 3 "For $p element b: $b"
  v = b*B
  @vprintln :UnitGroup 3 "For $p the vector v: $v"
  rel = Array{ZZRingElem}(undef, r + 1)
  for i in 1:r+1
    rel[i] = zero(FlintZZ)
  end

  @vprintln :UnitGroup 2 "First iteration to find a rational relation ..."
  while !_find_rational_relation!(rel, v, bound)
    @vprintln :UnitGroup 2 "Precision not high enough, increasing from $p to $(2*p)"
    p =  2*p
    p, B = _conj_log_mat_cutoff_inv(U, p)

    @assert p > 0

    conlog = conjugates_arb_log(y, p)

    # This is not totally fool proof.
    # It could still be the case that conlog has higher precision then the
    # elements in B.
    b = zero_matrix(base_ring(B), 1, r)

    for i in 1:r
      b[1, i] = conlog[i]
    end

    @vprintln :UnitGroup 3 "For $p element b: $b"
    v = b*B
    @vprintln :UnitGroup 3 "For $p the vector v: $v"
  end
  return rel, p
end

function _add_dependent_unit!(U::UnitGrpCtx{S}, y::S, ::Val{rel_only} = Val(false); post_reduction::Bool = true) where {S <: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, rel_only}
  @assert has_full_rank(U)

  K = nf(order(U))

  deg = degree(K)
  r = rank(U)

  rreg = tentative_regulator(U)
  bound = _denominator_bound_in_relation(rreg, K)
  @vprintln :UnitGroup 1 "Adding dependent unit ..."
  rel, p = _search_rational_relation(U, y, bound)
  @vprintln :UnitGroup 3 "For $p rel: $rel"
  @vprintln :UnitGroup 2 "Second iteration to check relation ..."

  while !_check_relation_mod_torsion(U.units, y, rel, p)
    @vprintln :UnitGroup 2 "Precision not high enough, increasing from $p to $(2*p)"
    p = 2*p
    @assert p > 0
    p, B = _conj_log_mat_cutoff_inv(U, p)

    @assert p != 0

    conlog = conjugates_arb_log(y, p)

    b = zero_matrix(parent(conlog[1]), 1, r)

    for i in 1:r
      b[1, i] = conlog[i]
    end

    @vprintln :UnitGroup 3 "For $p element b: $b"
    v = b*B
    @vprintln :UnitGroup 3 "For $p the vector v: $v"
    _find_rational_relation!(rel, v, bound)
    @vprintln :UnitGroup 3 "For $p rel: $rel"
  end

  if rel_only
    return rel
  end

  if abs(rel[r + 1]) == 1 || rel[r + 1] == 0
    U.rel_add_prec = p
    return false
  end

  m = _find_new_basis(rel)

  U.units =  _transform(vcat(U.units, y), m)

  U.conj_log_mat_cutoff = Dict{Int, ArbMatrix}()
  U.conj_log_mat_cutoff_inv = Dict{Int, ArbMatrix}()
  U.tentative_regulator = regulator(U.units, 64)
  U.rel_add_prec = p
  @vprintln :UnitGroup 1 "reduction of the new unit group...index improved by $(abs(rel[r+1]))"
  if post_reduction
    @vtime :UnitGroup 1 U.units = reduce(U.units, p)
  end
  #test reduction:
  #  LLL -> prod |b_i| <= 2^? disc
  @hassert :UnitGroup 1 prod(sum(x*x for x = conjugates_arb_log(u, 64)) for u = U.units)/U.tentative_regulator^2 < ZZRingElem(1)<< (2*length(U.units))
  return true
end

function _conj_log_mat_cutoff(x::UnitGrpCtx, p::Int)
  #if haskey(x.conj_log_mat_cutoff,  p)
  #  @vprintln :UnitGroup 3 "Conj matrix for $p cached"
  #  return x.conj_log_mat_cutoff[p]
  #else
    @vprintln :UnitGroup 2 "Conj matrix for $p not cached"
    x.conj_log_mat_cutoff[p] = _conj_log_mat_cutoff(x.units, p)
    return x.conj_log_mat_cutoff[p]
  #end
end

function _conj_log_mat_cutoff_inv(x::UnitGrpCtx, p::Int)
  @vprintln :UnitGroup 2 "Computing inverse of conjugates log matrix (starting with prec $p) ..."
  if haskey(x.conj_log_mat_cutoff_inv,  p)
    @vprintln :UnitGroup 2 "Inverse matrix cached for $p"
    return p, x.conj_log_mat_cutoff_inv[p]
  else
    @vprintln :UnitGroup 2 "Inverse matrix not cached for $p"
    @vprintln :UnitGroup 2 "Trying to invert conj matrix with prec $p"
    local y
    try
      y = _conj_log_mat_cutoff(x, p)
    catch e
      #println("I failed to find the _conj_log_mat_cutoff(x, p) for $p")
      println("Error computing the cutoff matrix with precision $p")
      rethrow(e)
    end
    local yy
    try
      yy = inv(y)
      x.conj_log_mat_cutoff_inv[p] = yy
      return p, x.conj_log_mat_cutoff_inv[p]
    catch e
      if !(e isa ErrorException)
        rethrow(e)
      end
      @vprintln :UnitGroup 2 "Could not invert with prec $p"
      @vprintln :UnitGroup 2 "Increasing precision .. (error was $e)"
      @v_do :UnitGroup 2 pushindent()
      r = _conj_log_mat_cutoff_inv(x, 2 * p)
      @v_do :UnitGroup 2 popindent()
      return r
    end
  end
end

function _isindependent(u::UnitGrpCtx{T}, y::FacElem{T}) where T
  K = _base_ring(x[1])
  p = u.indep_prec

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  # This can be made more memory friendly
  while true
    @assert p != 0

    A = _conj_log_mat(u.units, p)

    B = A*transpose(A)
    @vprintln :UnitGroup 1 "Computing det of $(nrows(B))x$(ncols(B)) matrix with precision $(p) ..."
    d = det(B)

    y = (Ar(1)//Ar(r))^r * (Ar(21)//Ar(128) * log(Ar(deg))//(Ar(deg)^2))^(2*r)
    if isfinite(d) && is_positive(y - d)
      return false, p
    elseif isfinite(d) && is_positive(d)
      return true, p
    end
    p = 2*p
  end
end

function _rel_add_precision(U)
  return U.rel_add_prec
end

function  _conj_log_mat(x::Vector{T}, p::Int) where T
  conlog = conjugates_arb_log(x[1], p)

  r, s = signature(_base_ring(x[1]))
  rr = r + s

  A = zero_matrix(parent(conlog[1]), length(x), rr)

  for i in 1:rr
    A[1, i] = conlog[i]
  end

  Ar = base_ring(A)

  for k in 2:length(x)
    conlog = conjugates_arb_log(x[k], p)
    for i in 1:rr
      A[k, i] = conlog[i]
    end
  end
  return A
end

function _conj_log_mat_cutoff(x::Vector{T}, p::Int) where T
  r = length(x)

  conlog = Vector{Vector{ArbFieldElem}}(undef, length(x))
  q = 2
  for i in 1:length(x)
    conlog[i] = conjugates_arb_log(x[i], p)
    for j in 1:length(conlog[i])
      q = max(q, bits(conlog[i][j]))
    end
  end

  A = zero_matrix(ArbField(q, cached = false), r, r)

  for i in 1:r
    for j in 1:r
      A[i, j] = conlog[i][j]
    end
  end

  return A
end

# The return value fl of add_unit indicates the following
#
# if has_full_rank(u) && fl
#   -> unit group enlarged
# if has_full_rank(u) && !fl
#   -> unit group has full rank and x is already contained
#
# if !has_full_rank(u) && fl
#   -> x is/was independent and rank of the unit group increased by one
#
# if !has_full_rank(u) && !fl
#   -> element x is not independent, but I did not use it to increase the unit
#      group
function add_unit!(u::UnitGrpCtx, x::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
  if has_full_rank(u)
    fl = _add_dependent_unit!(u, x)
    return fl
  end
  isindep, p = is_independent(vcat(u.units, [x]), u.indep_prec)
  u.indep_prec = max(p, u.indep_prec)
  if isindep
    push!(u.units, x)
    u.full_rank = (length(u.units) == full_unit_rank(u))
    return true
  else
    return false
  end
end

function tentative_regulator(U::UnitGrpCtx)
  if isdefined(U, :tentative_regulator)
    rreg = U.tentative_regulator
  else
    @vprintln :UnitGroup 1 "Computing regulator of independent units with 64 bits ..."
    rreg = regulator(U.units, 64)
    U.tentative_regulator = rreg
    @vprintln :UnitGroup 1 "done"
  end
  return rreg
end

has_full_rank(u::UnitGrpCtx) = u.full_rank

rank(u::UnitGrpCtx) = length(u.units)

full_unit_rank(u::UnitGrpCtx) = unit_group_rank(u.order)

function automorphism_list(u::UnitGrpCtx)
  if isdefined(u, :auts)
    return u.auts::Vector{morphism_type(AbsSimpleNumField, AbsSimpleNumField)}
  else
    auts = automorphism_list(nf(order(u)))
    u.auts = auts
    u.cache = Dict{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}[ Dict{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}() for i in 1:length(u.auts) ]
    return u.auts::Vector{morphism_type(AbsSimpleNumField, AbsSimpleNumField)}
  end
end

function apply_automorphism(u::UnitGrpCtx, i::Int, x::AbsSimpleNumFieldElem)
  c = u.cache[i]
  v = get!(() -> automorphism_list(u)[i](x), c, x)::AbsSimpleNumFieldElem
  return v
end

function apply_automorphism(u::UnitGrpCtx, i::Int, x::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
  D = Dict{AbsSimpleNumFieldElem, ZZRingElem}(apply_automorphism(u, i, b) => e for (b, e) in x)
  return FacElem(D)
end

################################################################################
#
#  New basis for transformed units
#
################################################################################

function _find_new_basis(rel)
  r = length(rel)
  m = matrix(FlintZZ, reshape(rel, r, 1))

  h, u = hnf_with_transform(m)

  @assert h[1,1] == 1

  u = inv(u)

  m = sub(u, 1:r, 2:r)
  m = transpose(lll(transpose(m)))
  return m
end

function _find_new_basis2(rel)
  r = length(rel)
  m = zero_matrix(FlintZZ, r, r)
  #m = matrix(FlintZZ, reshape(rel, r + 1, 1))
  for i in 1:r
    m[i, 1] = rel[i]
  end
  for j in 2:r
    m[j, j] = 1
  end

  h, u = hnf_with_transform(m)

  @assert h[1,1] == 1

  u = inv(u)

  m = sub(u, 1:r, 2:r)
  m = transpose(lll(transpose(m)))
  return m
end
