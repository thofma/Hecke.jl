################################################################################
#
#  Field access
#
################################################################################

order(u::UnitGrpCtx) = u.order

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, U::UnitGrpCtx)
  print(io, "Unit group context of\n$(order(U))\n")
end
################################################################################
#
#  Initialization 
#
################################################################################

function _unit_group_init(O::NfOrd)
  u = UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(O)
  return u
end

function _add_dependent_unit(U::UnitGrpCtx{S}, y::T; rel_only = false) where {S, T}
  K = nf(order(U))
  
  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  p = _rel_add_prec(U)

  #p = 64

  zz = Array{fmpz}(undef, r + 1)

  @vprint :UnitGroup 1 "Adding dependent unit ... \n"

  @v_do :UnitGroup 1 pushindent()
  p, B = _conj_log_mat_cutoff_inv(U, p)
  @v_do :UnitGroup 1 popindent()
  @vprint :UnitGroup 2 "Precision is now $p\n"

  Ar = base_ring(B)

  b = ArbMatSpace(Ar, 1, r, false)()

  conlog = conjugates_arb_log(y, p)

  for i in 1:r
    b[1, i] = conlog[i]
  end

  # I should do this using lu decomposition and caching
  # The inversion could go wrong,
  # Then we again have to increase the precision

  inv_succesful = true

  @vprint :UnitGroup 3 "For $p element b: $b\n"
  v = b*B
  @vprint :UnitGroup 3 "For $p the vector v: $v\n"

  z = Array{fmpq}(undef, r)

  rreg = arb()

  if isdefined(U, :tentative_regulator)
    rreg = U.tentative_regulator
  else
    @vprint :UnitGroup 1 "Computing regulator of independent units with 64 bits ... \n" 
    rreg = regulator(U.units, 64)
    @vprint :UnitGroup 1 "done \n" 
  end

  bound = _denominator_bound_in_relation(rreg, K)

  rel = Array{fmpz}(undef, r + 1)
  for i in 1:r+1
    rel[i] = zero(FlintZZ)
  end

  @vprint :UnitGroup 2 "First iteration to find a rational relation ... \n"
  while !_find_rational_relation!(rel, v, bound)
    @vprint :UnitGroup 2 "Precision not high enough, increasing from $p to $(2*p)\n"
    p =  2*p
    p, B = _conj_log_mat_cutoff_inv(U, p)

    @assert p > 0

    conlog = conjugates_arb_log(y, p)

    # This is not totally fool proof.
    # It could still be the case that conlog has higher precision then the
    # elements in B.
    b = ArbMatSpace(base_ring(B), 1, r, false)()

    for i in 1:r
      b[1, i] = conlog[i]
    end

    @vprint :UnitGroup 3 "For $p element b: $b\n"

    v = b*B
    @vprint :UnitGroup 3 "For $p the vector v: $v\n"
  end

  @vprint :UnitGroup 3 "For $p rel: $rel\n"

  @vprint :UnitGroup 2 "Second iteration to check relation ... \n"

  while !_check_relation_mod_torsion(U.units, y, rel, p)
    @vprint :UnitGroup 2 "Precision not high enough, increasing from $p to $(2*p)\n"
    p = 2*p
    @assert p > 0
    p, B = _conj_log_mat_cutoff_inv(U, p)

    @assert p != 0

    conlog = conjugates_arb_log(y, p)

    b = ArbMatSpace(parent(conlog[1]), 1, r, false)()

    for i in 1:r
      b[1, i] = conlog[i]
    end

    @vprint :UnitGroup 3 "For $p element b: $b\n"
    v = b*B
    @vprint :UnitGroup 3 "For $p the vector v: $v\n"
    _find_rational_relation!(rel, v, bound)
    @vprint :UnitGroup 3 "For $p rel: $rel\n"
  end

  if rel_only
    return rel
  end

  if abs(rel[r + 1]) == 1 || rel[r + 1] == 0
    U.rel_add_prec = p
    return false
  end

  m = matrix(FlintZZ, reshape(rel, r + 1, 1))

  h, u = hnf_with_transform(m)

  @assert h[1,1] == 1

  u = inv(u)

  m = sub(u, 1:r+1, 2:r+1)
  m = lll(m')'

  U.units =  _transform(vcat(U.units, y), m)

  U.conj_log_mat_cutoff = Dict{Int, arb_mat}()
  U.conj_log_mat_cutoff_inv = Dict{Int, arb_mat}()
  U.tentative_regulator = regulator(U.units, 64)
  U.rel_add_prec = p
  @vprint :UnitGroup 1 "reduction of the new unit group...index improved by $(abs(rel[r+1]))\n"
  @vtime :UnitGroup 1 U.units = reduce(U.units, p)
  return true
end

function _conj_log_mat_cutoff(x::UnitGrpCtx, p::Int)
  #if haskey(x.conj_log_mat_cutoff,  p)
  #  @vprint :UnitGroup 2 "Conj matrix for $p cached\n"
  #  return x.conj_log_mat_cutoff[p]
  #else
    @vprint :UnitGroup 2 "Conj matrix for $p not cached\n"
    x.conj_log_mat_cutoff[p] = _conj_log_mat_cutoff(x.units, p)
    return x.conj_log_mat_cutoff[p]
  #end
end

function _conj_log_mat_cutoff_inv(x::UnitGrpCtx, p::Int)
  @vprint :UnitGroup 2 "Computing inverse of conjugates log matrix (starting with prec $p) ... \n"
  if haskey(x.conj_log_mat_cutoff_inv,  p)
    @vprint :UnitGroup 2 "Inverse matrix cached for $p\n"
    return p, x.conj_log_mat_cutoff_inv[p]
  else
    @vprint :UnitGroup 2 "Inverse matrix not cached for $p\n"
    @vprint :UnitGroup 2 "Trying to invert conj matrix with prec $p \n"
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
      @vprint :UnitGroup 2 "Could not invert with prec $p \n"
      @vprint :UnitGroup 2 "Increasing precision .. (error was $e)\n"
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
    @vprint :UnitGroup 1 "Computing det of $(rows(B))x$(cols(B)) matrix with precision $(p) ... \n"
    d = det(B)

    y = (Ar(1)//Ar(r))^r * (Ar(21)//Ar(128) * log(Ar(deg))//(Ar(deg)^2))^(2*r)
    if isfinite(d) && ispositive(y - d)
      return false, p
    elseif isfinite(d) && ispositive(d)
      return true, p
    end
    p = 2*p
  end
end

function _rel_add_prec(U)
  return U.rel_add_prec
end

function  _conj_log_mat(x::Array{T, 1}, p::Int) where T
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

function _conj_log_mat_cutoff(x::Array{T, 1}, p::Int) where T
  r = length(x)

  conlog = Vector{Vector{arb}}(undef, length(x))
  q = 2
  for i in 1:length(x)
    conlog[i] = conjugates_arb_log(x[i], p)
    for j in 1:length(conlog[i])
      q = max(q, bits(conlog[i][j]))
    end
  end

  A = zero_matrix(ArbField(q, false), r, r)

  for i in 1:r
    for j in 1:r
      A[i, j] = conlog[i][j]
    end
  end

  return A
end

# Powering function for fmpz exponents
function _pow(x::Array{T, 1}, y::Array{fmpz, 1}) where T
  K = _base_ring(x[1])

  zz = deepcopy(y)

  z = Array{fmpz}(undef, length(x))

  for i in 1:length(x)
    z[i] = mod(zz[i], 2)
    zz[i] = zz[i] - z[i]
  end

  r = K(1)

  return zz
end

function _add_unit(u::UnitGrpCtx, x::FacElem{nf_elem, AnticNumberField})
  isindep, p = isindependent(vcat(u.units, [x]), u.indep_prec)
  u.indep_prec = max(p, u.indep_prec)
  if isindep
    push!(u.units, x)
  end
end


