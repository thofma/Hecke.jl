###########################################################################################
#
#   Row module reduction
#
###########################################################################################

# Reduce the row module of M to a basis of it, with the kernel selected by
#   _row_reduction_trait of the coefficient ring.
#
# Contract: M is m x n with m >= n and its row module has full rank n
#  (the zero ideal is handled by the callers, before any reduction).
# The result is an n x n matrix generating the same row module.
#
# NOTE: mutating variants, while mutating the given matrix, might return
#   the different matrix, constructed from the rows of the input
#   in the case of non-full row rank
#
# NOTE: modulus, when given, must be a multiple of the largest elementary divisor of
#   the row module. Reduction kernels that do not canonicalize ignore it.

function _reduce_row_module!(::HNFRedTrait, M::MatElem; modulus = nothing)
  n = ncols(M)
  H = modulus === nothing ? _hnf_left!(M) : hnf_modular_eldiv_left!(M, modulus)

  # the canonical basis occupies the bottom n rows
  @hassert :GenOrd 1 all(is_zero_row(H, i) for i in 1:(nrows(H) - n))
  return nrows(H) == n ? H : sub(H, (nrows(H) - n + 1):nrows(H), 1:n)
end

function _reduce_row_module!(::PopovRedTrait, M::MatElem; modulus = nothing)
  return _basis_rows(_weak_popov!(M))
end

# Popov leaves the zero rows in place; full rank means exactly n rows survive.
function _basis_rows(M::MatElem)
  n = ncols(M)
  keep = [i for i in 1:nrows(M) if !is_zero_row(M, i)]
  @hassert :GenOrd 1 length(keep) == n

  return length(keep) == nrows(M) ? M : sub(M, keep, 1:n)
end

function _reduce_row_module!(M::MatElem; reduction = _row_reduction_trait(M), modulus = nothing)
  return _reduce_row_module!(reduction, M; modulus = modulus)
end

################################################################################
#
#  Helpers
#
################################################################################

# uniform access to the principal / two-element data of integral and fractional ideals

_has_princ_gen(I::GenOrdIdl) = has_princ_gen(I)
_has_two_gens(I::GenOrdIdl)  = has_2_elem(I)

_has_princ_gen(I::GenOrdFracIdl) = isdefined(I, :num) && has_princ_gen(I.num)
_has_two_gens(I::GenOrdFracIdl)  = isdefined(I, :num) && has_2_elem(I.num)

# princ_gen/gen_one/gen_two are declared with abstract types: type assertions restore inference
# TODO: should we add public accessors for this? (similar to basis_matrix)

_princ_gen(I::GenOrdIdl{S, T}) where {S, T} = I.princ_gen::elem_type(GenOrd{S, T})
_gen_one(I::GenOrdIdl{S, T}) where {S, T}   = I.gen_one::elem_type(T)
_gen_two(I::GenOrdIdl{S, T}) where {S, T}   = I.gen_two::elem_type(GenOrd{S, T})

_princ_gen(I::GenOrdFracIdl) = _princ_gen(I.num)
_gen_one(I::GenOrdFracIdl)   = _gen_one(I.num)
_gen_two(I::GenOrdFracIdl)   = _gen_two(I.num)

# the matrix whose rows generate the module, for use in the arithmetic stacks

_basis_matrix(a::GenOrdIdl)     = basis_matrix(a; copy = false)
_basis_matrix(a::GenOrdFracIdl) = _basis_matrix_numerator(a)

# modulus for modular HNF

_eldiv_modulus(::RowModuleReductionTrait, ::GenOrdIdl)      = nothing
_eldiv_modulus(::RowModuleReductionTrait, ::GenOrdFracIdl)  = nothing

_eldiv_modulus(::HNFRedTrait, a::GenOrdIdl)         = minimum(a; copy = false)
_eldiv_modulus(red::HNFRedTrait, a::GenOrdFracIdl)  = isdefined(a, :num) ? _eldiv_modulus(red, a.num) : nothing

# Wraps a matrix plus denominator into a fractional ideal.
# For HNF reduction, fractional ideal's basis matrix will just duplicate integral ideal,
#   so we can always force create the integral ideal
# NOTE: for Popov reduction we do not need to reduce the input matrix
# The kwarg is here to handle both "create from already reduced matrix" (used in arithmetic)
#   and "create from user-provided matrix" (used in constructors)

function _fractional_ideal_from_basis_matrix(::HNFRedTrait, O::GenOrd, M::MatElem, d::RingElem; reduced::Bool)
  return fractional_ideal(ideal(O, M; M_in_hnf = reduced), d)
end

function _fractional_ideal_from_basis_matrix(::RowModuleReductionTrait, O::GenOrd, M::MatElem, d::RingElem; reduced::Bool)
  M, d = _strip_pair_content(M, d)
  return GenOrdFracIdl(O, M, d)
end

function _fractional_ideal_from_basis_matrix(O::GenOrd, M::MatElem, d::RingElem; reduced::Bool)
  return _fractional_ideal_from_basis_matrix(_row_reduction_trait(O), O, M, d; reduced = reduced)
end

###########################################################################################
#
#   Multiplication
#
###########################################################################################

function _mul_impl_matrix_stack(red::RowModuleReductionTrait, a, b)
  # make a the simpler of the two: fewer generators means fewer blocks in the stack
  if _has_princ_gen(b) || (_has_two_gens(b) && !_has_princ_gen(a))
    a, b = b, a
  end

  Mb = _basis_matrix(b)
  V = if _has_princ_gen(a)
    Mb * representation_matrix(_princ_gen(a))
  elseif _has_two_gens(a)
    vcat(Mb * _gen_one(a), Mb * representation_matrix(_gen_two(a)))
  else
    O = order(a)
    n = degree(O)
    Ma = _basis_matrix(a)
    reduce(vcat, [Mb * _representation_matrix(O, view(Ma, i, 1:n)) for i in 1:n])
  end

  ha, hb = _eldiv_modulus(red, a), _eldiv_modulus(red, b)
  modulus = (ha === nothing || hb === nothing) ? nothing : ha*hb
  return _reduce_row_module!(red, V; modulus = modulus)
end

function Base.:*(a::GenOrdFracIdl{S, T}, b::GenOrdFracIdl{S, T}) where {S, T}
  @req order(a) === order(b) "Ideals must have same order"

  is_zero(a) && return a
  is_zero(b) && return b
  is_one(a) && return b
  is_one(b) && return a

  O = order(a)
  red = _row_reduction_trait(O)
  d = denominator(a; copy = false) * denominator(b; copy = false)

  # For Popov reduction, bypass integral ideals to avoid HNF degree/height swell
  # TODO: swell is the issue only on Q(x)
  # TODO: we need to revisit this after we have extracted two-element representation
  if red isa HNFRedTrait && isdefined(a, :num) && isdefined(b, :num)
    c = numerator(a; copy = false)*numerator(b; copy = false)
    return fractional_ideal(c, d)
  end

  M = _mul_impl_matrix_stack(red, a, b)
  return _fractional_ideal_from_basis_matrix(red, O, M, d; reduced = true)
end

Base.:*(A::GenOrdIdl{S, T}, B::GenOrdFracIdl{S, T}) where {S, T} = fractional_ideal(A)*B
Base.:*(A::GenOrdFracIdl{S, T}, B::GenOrdIdl{S, T}) where {S, T} = A*fractional_ideal(B)

###########################################################################################
#
#   Colon/inv
#
###########################################################################################

# We do matrix inverse in colon implementation.
# Having a HNF input to matrix inverse is favorable for the performance:
#   having a triangular shape, inverse becomes almost free.
# Of course, HNF results in coefficient swell over Q(x), so it should never be used here
# As surprising as it may sound, for F_q(x) it is way faster to do HNF + inverse
#   instead of inverting matrix directly
# NOTE: we will check for extra HNF only when Popov reduction is used
# NOTE: of course we will be using HNF on *small* matrix, the result of the Popov
#   reduction of the matrix stack
_allow_hnf_for_colon(::Type{<:Ring}) = false
_allow_hnf_for_colon(::Type{<:PolyRing{<:FinFieldElem}}) = true

# The colon (A : B) = N/d
# A is represented by the inverse of basis matrix in the form Ma/da
# B is represented by the basis matrix in the form Mb/db
function _colon_matrix_stack(O::GenOrd{S, T}, Ma::MatElem, da, Mb::MatElem, db; reduction = _row_reduction_trait(base_ring(O))) where {S, T}
  # With b_i the i-th basis element of B and v the coordinate vector of x,
  #   x*b_i in A  <=>  v*R_i*Ma in (da*db)*R^n,  R_i = _representation_matrix(O, Mb[i, :]),
  #   giving v*[R_1*Ma | ... | R_n*Ma] in g*R^(n^2),  g = da*db.
  # The condition only depends on the *column* module of that block matrix, so we
  #   reduce it through the transpose to a square W, and then
  #   { v : v*W in g*R^n } = row module of g*W^{-1}.
  n = degree(O)
  blocks = [_representation_matrix(O, view(Mb, i, 1:n)) for i in 1:n]

  if !is_one(Ma)
    blocks = [Ri * Ma for Ri in blocks]
  end

  W = _reduce_row_module!(reduction, transpose(reduce(hcat, blocks)))
  if reduction isa PopovRedTrait && _allow_hnf_for_colon(typeof(base_ring(O)))
    W = _reduce_row_module!(HNFRedTrait(), W)
  else

  end

  K = base_field(field(O))::base_field_type(S)
  X, e = _inv_pair(transpose(W), K)
  M, d = _strip_pair_content(da*db * X, e)
  return _reduce_row_module!(reduction, M), d
end

_basis_matrix_pair(I::GenOrdIdl) = basis_matrix(I; copy = false), one(base_ring(order(I)))

function _colon_impl(red::RowModuleReductionTrait, O::GenOrd, a, b)
  Ma, da = _basis_matrix_inv_pair(a)
  Mb, db = _basis_matrix_pair(b)
  M, d = _colon_matrix_stack(O, Ma, da, Mb, db; reduction = red)
  return _fractional_ideal_from_basis_matrix(red, O, M, d; reduced = true)
end

function Hecke.colon(I::GenOrdFracIdl{S, T}, J::GenOrdFracIdl{S, T}) where {S, T}
  @req order(I) === order(J) "Ideals must lie in the same order"
  # (I : 0) is all of F, which is not a fractional ideal
  @req !is_zero(J) "Second ideal must be nonzero"
  is_zero(I) && return I

  O = order(I)
  red = _row_reduction_trait(O)
  return _colon_impl(red, O, I, J)
end

function Hecke.colon(I::GenOrdIdl{S, T}, J::GenOrdIdl{S, T}) where {S, T}
  @req order(I) === order(J) "Ideals must lie in the same order"
  # (I : 0) is all of F, which is not a fractional ideal
  @req !is_zero(J) "Second ideal must be nonzero"
  is_zero(I) && return fractional_ideal(I)

  O = order(I)
  return _colon_impl(HNFRedTrait(), O, I, J)
end

Hecke.colon(I::GenOrdIdl, J::GenOrdFracIdl) = colon(fractional_ideal(I), J)
Hecke.colon(I::GenOrdFracIdl, J::GenOrdIdl) = colon(I, fractional_ideal(J))

Base.://(I::GenOrdFracIdl, J::GenOrdFracIdl) = colon(I, J)

function _inv_impl(red::RowModuleReductionTrait, O::GenOrd, I)
  R = base_ring(O)
  Ma, da = identity_matrix(R, degree(O)), one(R)
  Mb, db = _basis_matrix_pair(I)
  M, d = _colon_matrix_stack(O, Ma, da, Mb, db; reduction = red)
  return _fractional_ideal_from_basis_matrix(red, O, M, d; reduced = true)
end

# NOTE: currently we do not use integral ideal (even if present)
function inv(I::GenOrdFracIdl)
  @req !is_zero(I) "Ideal must be nonzero"

  O = order(I)
  red = _row_reduction_trait(O)
  return _inv_impl(red, O, I)
end
