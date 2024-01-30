#=
CF: according to git grep: this is not called.
Quite likely, it has been replaced by the other reduction functions
################################################################################
#
#  Size reduction
#
################################################################################

function _reduce_size(x::Vector{T}, prec::Int = 64) where T
  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  conlog = conjugates_arb_log(x[1], prec)

  A = zero_matrix(parent(conlog[1]), length(x), rr)

  B = zero_matrix(FlintZZ, nrows(A), ncols(A))

  for i in 1:rr
    A[1, i] = conlog[i]
  end

  Ar = base_ring(A)

  for i in 1:nrows(A)
    for j in 1:ncols(A)
      b, y = unique_integer(ceil(ldexp(A[i, j], 64)))
      @assert b
      B[i, j] = y
    end
  end

  L, U = lll_with_transform(B)
end

=#

################################################################################
#
#  Reduce units using LLL
#
################################################################################

function scaled_log_matrix(u::Vector{T}, pr::Int = 32) where T

  r,s = signature(_base_ring(u[1]))
  A = zero_matrix(FlintZZ, length(u), r + s)
  @vprintln :UnitGroup 1 "starting prec in scaled_log_matrix: $pr"

  for i in 1:length(u)
    c = conjugates_arb_log(u[i], pr)
    for k in 1:length(c)
      @assert radiuslttwopower(c[k], -pr)
    end

    if any(x->radius(x) > 1e-9, c)  # too small...
      @vprintln :UnitGroup 1 "increasing prec in scaled_log_matrix, now: $pr"
      pr *= 2
      if pr > 2^30
        error("cannot do lll on units")
        break
      end
      return scaled_log_matrix(u, pr)
    end
    for j in 1:length(c)
      tt = ZZRingElem()
      t = ccall((:arb_mid_ptr, libarb), Ptr{arf_struct}, (Ref{ArbFieldElem}, ), c[j])
      l = ccall((:arf_get_fmpz_fixed_si, libarb), Int, (Ref{ZZRingElem}, Ptr{arf_struct}, Int), tt, t, -pr)
      A[i, j] = tt
    end
  end
  return A, pr
end

function row_norm(A::ZZMatrix, i::Int)
  return sum(ZZRingElem[A[i,j]^2 for j=1:ncols(A)])
end

function row_norms(A::ZZMatrix)
  return ZZRingElem[row_norm(A, i) for i=1:nrows(A)]
end

function reduce(u::Vector{T}, prec::Int = 32) where T
  @vprintln :UnitGroup 1 "prec in reduce, now: $prec"
  r = length(u)
  if r == 0
    return u
  end

  while true
    @vtime :UnitGroup 2 A, prec = scaled_log_matrix(u, prec)

    @vtime :UnitGroup 2 L, U = lll_with_transform(A)
    if isone(U)
      return u
    end
    @vprintln :UnitGroup 2 "reducing units by $U"
    pA = prod(row_norms(A))
    pL = prod(row_norms(L))
    @vprintln :UnitGroup 1 "reducing norms of logs from 2^$(nbits(pA)) -> 2^$(nbits(pL)), rat is $(Float64(1.0*pA//pL))"
    u = transform(u, transpose(U))
    if nbits(pL) >= nbits(pA)
    #  u = [compact_presentation(x, decom = factor(1*maximal_order(base_ring(x)))) for x = u]
      return u
    end
    @vprintln :UnitGroup 1 "trying to reduce further..."
  end
end

