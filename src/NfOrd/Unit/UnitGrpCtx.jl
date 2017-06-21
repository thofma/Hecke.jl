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

function _add_dependent_unit{S, T}(U::UnitGrpCtx{S}, y::T; rel_only = false)
  K = nf(order(U))
  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  p = _rel_add_prec(U)

  #p = 64

  zz = Array{fmpz}(r + 1)

  @vprint :UnitGroup 1 "Adding dependent unit ... \n"
  @v_do :UnitGroup 1 pushindent()
  p, B = _conj_log_mat_cutoff_inv(U, p)
  @v_do :UnitGroup 1 popindent()
  @vprint :UnitGroup 2 "Precision is now $p\n"

  Ar = base_ring(B)

  b = ArbMatSpace(Ar, 1, r)()

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

  z = Array{fmpq}(r)

  rreg = arb()

  if isdefined(U, :tentative_regulator)
    rreg = U.tentative_regulator
  else
    @vprint :UnitGroup 1 "Computing regulator of independent units with 64 bits ... \n" 
    rreg = regulator(U.units, 64)
    @vprint :UnitGroup 1 "done \n" 
  end

  bound = _denominator_bound_in_relation(rreg, K)

    rel = Array{fmpz}(r + 1)
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

    b = ArbMatSpace(parent(conlog[1]), 1, r)()

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

    b = ArbMatSpace(parent(conlog[1]), 1, r)()

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

  m = MatrixSpace(FlintZZ, r + 1, 1)(reshape(rel, r + 1, 1))

  h, u = hnf_with_transform(m)

  @assert h[1,1] == 1

  u = inv(u)

  m = submat(u, 1:r+1, 2:r+1)

  U.units =  _transform(vcat(U.units, y), m)

  U.conj_log_mat_cutoff = Dict{Int, arb_mat}()
  U.conj_log_mat_cutoff_inv = Dict{Int, arb_mat}()
  U.tentative_regulator = regulator(U.units, 64)
  U.rel_add_prec = p
  if abs(rel[r+1]) > 100 # we enlarged
    U.units = reduce(U.units, p)
  end
  return true
end

function _conj_log_mat_cutoff(x::UnitGrpCtx, p::Int)
  if haskey(x.conj_log_mat_cutoff,  p)
    @vprint :UnitGroup 2 "Conj matrix for $p cached\n"
    return x.conj_log_mat_cutoff[p]
  else
    @vprint :UnitGroup 2 "Conj matrix for $p not cached\n"
    x.conj_log_mat_cutoff[p] = _conj_log_mat_cutoff(x.units, p)
    return x.conj_log_mat_cutoff[p]
  end
end

function _conj_log_mat_cutoff_inv(x::UnitGrpCtx, p::Int)
  @vprint :UnitGroup 2 "Computing inverse of conjugates log matrix (starting with prec $p) ... \n"
  if haskey(x.conj_log_mat_cutoff_inv,  p)
    @vprint :UnitGroup 2 "Inverse matrix cached for $p\n"
    return p, x.conj_log_mat_cutoff_inv[p]
  else
    @vprint :UnitGroup 2 "Inverse matrix not cached for $p\n"
    try
      @vprint :UnitGroup 2 "Trying to invert conj matrix with prec $p \n"
      @vprint :UnitGroup 3 "Matrix to invert is $(_conj_log_mat_cutoff(x, p))"
      x.conj_log_mat_cutoff_inv[p] = inv(_conj_log_mat_cutoff(x, p))
      @vprint :UnitGroup 2 "Successful. Returning with prec $p \n"
      @vprint :UnitGroup 3 "$(x.conj_log_mat_cutoff_inv[p])\n"
      return p, x.conj_log_mat_cutoff_inv[p]
    catch e
      # I should check that it really is that error
      @vprint :UnitGroup 2 "Increasing precision .. (error was $e)\n"
      @v_do :UnitGroup 2 pushindent()
      r = _conj_log_mat_cutoff_inv(x, 2*p)
      @v_do :UnitGroup 2 popindent()
      return r
    end
  end
end

function _isindependent{T}(u::UnitGrpCtx{T}, y::FacElem{T})
  K = _base_ring(x[1])
  p = u.indep_prec

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  # This can be made more memory friendly
  while true
    @assert p != 0

#    if length(u.units) == 0
#      A = _conj_log_mat([y], p)
#      B = MatrixSpace(base_ring(A), rows(A), rows(A))
#      z.conj_log_mat_tranpose = (transpose(A), p)
#      mul!(B, A, z.conj_log_mat_transpose)
#      z.conj_log_mat = (A, p)
#      z.conj_log_mat_times_transpose = (B, p)
#    end
#
#    if z.conj_log_mat[2] == p # the old matrix has the same precision as our working precision
#      A = z.conj_log_mat[1]
#      conjlog = conjugates_arb_log(y, p)
#      newrow = MatrixSpace(base_ring(A), 1, cols(A))()
#      newcol = MatrixSpace(base_ring(A), cols(A), 1)()
#      z.conj_log_mat = (vcat(A, newrow), p)
#      z.conj_log_mat_transpose = (hcat(z.conj_log_mat_transpose[1], newcol), p)
#
#      for i in 1:cols(A)
#        z.conj_log_mat[1][rows(A) + 1, i] = conjlog[i]
#        z.conj_log_mat_transpose[1][i, rows(A) + 1]
#      end
#      A = z.conj_log_mat[1]
#    end
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

function  _conj_log_mat{T}(x::Array{T, 1}, p::Int)
  conlog = conjugates_arb_log(x[1], p)

  r, s = signature(_base_ring(x[1]))
  rr = r + s

  A = MatrixSpace(parent(conlog[1]), length(x), rr)()

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

function _conj_log_mat_cutoff{T}(x::Array{T, 1}, p::Int)
  r = length(x)
  conlog = conjugates_arb_log(x[1], p)
  A = ArbMatSpace(parent(conlog[1]), r, r)()

  for i in 1:r
    A[1, i] = conlog[i]
  end

  for k in 2:r
    conlog = conjugates_arb_log(x[k], p)
    for i in 1:r
      A[k, i] = conlog[i]
    end
  end
  return A
end

# Powering function for fmpz exponents
function _pow{T}(x::Array{T, 1}, y::Array{fmpz, 1})
  K = _base_ring(x[1])

  zz = deepcopy(y)

  z = Array{fmpz}(length(x))

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


