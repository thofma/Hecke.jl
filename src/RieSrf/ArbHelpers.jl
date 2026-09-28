################################################################################
#
#  Small wrappers around FLINT (arb/acb) functions used by the Riemann surface
#  code, for which Nemo/Hecke have no equivalent (checked against Nemo 0.56).
#  Operations that do exist are used directly: one!, zero!, div!, mul!
#  (acb x arb), Hecke.set!, Hecke.abs!, Nemo._acb_set, Nemo._arb_set.
#
#  Unless stated otherwise the precision is taken from the parent of the
#  result, as in Nemo's in-place functions.
#
################################################################################

# _acb_pow_si!: In place, precision from parent(z). Nemo has no in-place acb^Int.
# z <- v^e for any Int e (handles negative exponents), in place
_acb_pow_si!(z::AcbFieldElem, v::AcbFieldElem, e::Int) =
  ccall((:acb_pow_si, libflint), Nothing,
        (Ref{AcbFieldElem}, Ref{AcbFieldElem}, Int, Int), z, v, e, precision(parent(z)))

# _acb_dot_ptr!: acb_dot on raw contiguous acb arrays (Ptr{acb_struct}); Nemo has no
# dot product on acb vectors.
# res <- sum_{i < len} x[i] * y[i]   (x, y contiguous acb arrays)
_acb_dot_ptr!(res::Ptr{acb_struct}, x::Ptr{acb_struct}, y::Ptr{acb_struct}, len::Int, prec::Int) =
  ccall((:acb_dot, libflint), Nothing,
        (Ptr{acb_struct}, Ptr{acb_struct}, Cint, Ptr{acb_struct}, Int, Ptr{acb_struct}, Int, Int, Int),
        res, C_NULL, 0, x, 1, y, 1, len, prec)
_acb_dot_ptr!(res::AcbFieldElem, x::Ptr{acb_struct}, y::Ptr{acb_struct}, len::Int, prec::Int) =
  ccall((:acb_dot, libflint), Nothing,
        (Ref{AcbFieldElem}, Ptr{acb_struct}, Cint, Ptr{acb_struct}, Int, Ptr{acb_struct}, Int, Int, Int),
        res, C_NULL, 0, x, 1, y, 1, len, prec)

# _acb_powers_ptr!: Powers 1, x, ..., x^n into a raw contiguous acb array, for _acb_dot_ptr!.
# p[0..n] <- 1, x, x^2, ..., x^n
function _acb_powers_ptr!(p::Ptr{acb_struct}, x::AcbFieldElem, n::Int, prec::Int)
  sz = sizeof(acb_struct)
  ccall((:acb_one, libflint), Nothing, (Ptr{acb_struct},), p)
  n >= 1 || return p
  ccall((:acb_set, libflint), Nothing, (Ptr{acb_struct}, Ref{AcbFieldElem}), p + sz, x)
  for i in 2:n
    ccall((:acb_mul, libflint), Nothing,
          (Ptr{acb_struct}, Ptr{acb_struct}, Ref{AcbFieldElem}, Int),
          p + i*sz, p + (i - 1)*sz, x, prec)
  end
  return p
end

# _arb_mul_si!: arb * Int in place, precision from parent(z). Not in Nemo.
_arb_mul_si!(z::ArbFieldElem, x::ArbFieldElem, n::Int) =
  ccall((:arb_mul_si, libflint), Nothing, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, Int, Int),
        z, x, n, precision(parent(z)))

# _acb_set_round_ptr!: Set and round from a raw acb pointer. Nemo._acb_set(z, x, prec)
# only accepts an AcbFieldElem as source.
_acb_set_round_ptr!(z::AcbFieldElem, p::Ptr{acb_struct}) =
  ccall((:acb_set_round, libflint), Nothing, (Ref{AcbFieldElem}, Ptr{acb_struct}, Int),
        z, p, precision(parent(z)))

# _acb_mid: Midpoint of an acb as a new element. Nemo only has midpoint(::ArbFieldElem).
_acb_mid(x::AcbFieldElem) = (r = parent(x)();
  ccall((:acb_get_mid, libflint), Nothing, (Ref{AcbFieldElem}, Ref{AcbFieldElem}), r, x); r)

# radius_bound: Upper bound for the radius of an acb ball, as an ArbFieldElem.
radius_bound(x::AcbFieldElem) = abs(x - _acb_mid(x))

# _acb_get_mid!: Midpoint of an acb, in place. Nemo only has midpoint(::ArbFieldElem).
_acb_get_mid!(z::AcbFieldElem, x::AcbFieldElem) =
  ccall((:acb_get_mid, libflint), Nothing, (Ref{AcbFieldElem}, Ref{AcbFieldElem}), z, x)

# _arb_mid_f64: Midpoint of an arb as Float64 without allocation (Float64(::ArbFieldElem)
# allocates a temporary arf_struct); used in the step control of the adaptive
# continuation. The arb_t starts with its midpoint arf_t; 4 = ARF_RND_NEAR.
_arb_mid_f64(x::ArbFieldElem) =
  ccall((:arf_get_d, libflint), Float64, (Ref{ArbFieldElem}, Int), x, 4)

# _acb_poly_evaluate!: In-place polynomial evaluation, precision from parent(r). Nemo
# only has the allocating evaluate(p, x).
_acb_poly_evaluate!(r::AcbFieldElem, p::AcbPolyRingElem, x::AcbFieldElem) =
  ccall((:acb_poly_evaluate, libflint), Nothing,
        (Ref{AcbFieldElem}, Ref{AcbPolyRingElem}, Ref{AcbFieldElem}, Int),
        r, p, x, precision(parent(r)))

function acos(x::AcbFieldElem)
  z = parent(x)()
  prec = precision(parent(x))
  @ccall libflint.acb_acos(z::Ref{AcbFieldElem}, x::Ref{AcbFieldElem}, prec::Int)::Nothing
  return z
end

function atanh(x::AcbFieldElem)
  z = parent(x)()
  prec = precision(parent(x))
  @ccall libflint.acb_atanh(z::Ref{AcbFieldElem}, x::Ref{AcbFieldElem}, prec::Int)::Nothing
  return z
end

function asinh(x::AcbFieldElem)
  z = parent(x)()
  prec = precision(parent(x))
  @ccall libflint.acb_asinh(z::Ref{AcbFieldElem}, x::Ref{AcbFieldElem}, prec::Int)::Nothing
  return z
end

function acosh(x::AcbFieldElem)
  z = parent(x)()
  prec = precision(parent(x))
  @ccall libflint.acb_acosh(z::Ref{AcbFieldElem}, x::Ref{AcbFieldElem}, prec::Int)::Nothing
  return z
end

# Roots of p, refined to (almost) the working precision.
#
# Nemo's roots(p; initial_prec = prec) returns as soon as the roots are
# isolated. Its first attempt starts from scratch with at most
# min(max(deg, 32), prec) iterations, so near a cluster of roots the balls can
# be much wider than the precision allows (for g4 at 1053 bits one fiber was
# only good to 411 bits, which capped the whole period matrix). With `target`
# Nemo keeps refining, from the roots found so far at doubled working
# precision, until every radius is at most 2^-target. Well-conditioned
# polynomials meet the target in the first attempt at no extra cost.
#
# slack: the roots are refined to 2^-(prec - slack). In the period computation
# prec is the working precision W = T + _rounding_guard_bits(), so the slack
# must stay below that guard: with slack = 64 the roots were only good to
# 2^-(T - 32), which capped the periods of g4 at about prec + 1 bits and made
# the precision retry useless there.
function _accurate_roots(p::AcbPolyRingElem, prec::Int; slack::Int = _rounding_guard_bits() - 8)
  return roots(p, initial_prec = prec, target = max(prec - slack, 0))
end

# Linear algebra with balls.
#
# FLINT's acb_mat_solve (and acb_mat_inv, which calls it) uses Gaussian
# elimination in ball arithmetic (acb_mat_solve_lu) when the precision is large
# compared to the size of the matrix (n <= 4 or prec > 10n), and
# preconditioning by an approximate inverse (acb_mat_solve_precond) otherwise.
# The LU variant can overestimate the radii by a lot: for the small period
# matrix it cost 60-110 bits for genus 22-36 at 550 bits, while the
# preconditioned solver lost almost nothing. So always precondition.
function _solve_precond(A::AcbMatrix, B::AcbMatrix)
  X = zero_matrix(base_ring(A), ncols(A), ncols(B))
  ok = ccall((:acb_mat_solve_precond, libflint), Cint,
             (Ref{AcbMatrix}, Ref{AcbMatrix}, Ref{AcbMatrix}, Int),
             X, A, B, precision(base_ring(A)))
  if ok == 0
    # The preconditioned solver can fail where Gaussian elimination still
    # gives (wide) balls, e.g. for a badly conditioned matrix at the limit of
    # the working precision: fall back to FLINT's default.
    ok = ccall((:acb_mat_solve, libflint), Cint,
               (Ref{AcbMatrix}, Ref{AcbMatrix}, Ref{AcbMatrix}, Int),
               X, A, B, precision(base_ring(A)))
  end
  ok == 0 && error("Matrix is singular or too badly conditioned for the working precision.")
  return X
end

function _solve_precond(A::ArbMatrix, B::ArbMatrix)
  X = zero_matrix(base_ring(A), ncols(A), ncols(B))
  ok = ccall((:arb_mat_solve_precond, libflint), Cint,
             (Ref{ArbMatrix}, Ref{ArbMatrix}, Ref{ArbMatrix}, Int),
             X, A, B, precision(base_ring(A)))
  if ok == 0
    # The preconditioned solver can fail where Gaussian elimination still
    # gives (wide) balls, e.g. for a badly conditioned matrix at the limit of
    # the working precision: fall back to FLINT's default.
    ok = ccall((:arb_mat_solve, libflint), Cint,
               (Ref{ArbMatrix}, Ref{ArbMatrix}, Ref{ArbMatrix}, Int),
               X, A, B, precision(base_ring(A)))
  end
  ok == 0 && error("Matrix is singular or too badly conditioned for the working precision.")
  return X
end

_inv_precond(A::Union{AcbMatrix, ArbMatrix}) = _solve_precond(A, identity_matrix(base_ring(A), nrows(A)))
