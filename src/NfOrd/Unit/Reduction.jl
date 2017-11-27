################################################################################
#
#  Size reduction
#
################################################################################

function _reduce_size(x::Array{T, 1}, prec::Int = 64) where T
  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  conlog = conjugates_arb_log(x[1], prec)

  A = zero_matrix(parent(conlog[1]), length(x), rr)

  B = zero_matrix(FlintZZ, rows(A), cols(A))

  for i in 1:rr
    A[1, i] = conlog[i]
  end

  Ar = base_ring(A)

  for i in 1:rows(A)
    for j in 1:cols(A)
      b, y = unique_integer(ceil(ldexp(A[i, j], 64)))
      @assert b
      B[i, j] = y
    end
  end

  L, U = lll_with_transform(B)
end

################################################################################
#
#  Reduce units using LLL
#
################################################################################

function scaled_log_matrix(u::Array{T, 1}, prec::Int = 32) where T

  r,s = signature(_base_ring(u[1]))
  A = zero_matrix(FlintZZ, length(u), r + s)
  prec = max(prec, maximum([nbits(maxabs_exp(U))+nbits(length(U.fac)) for U = u]))
  @vprint :UnitGroup 2 "starting prec in scaled_log_matrix: $prec\n"

  for i in 1:length(u)
    c = conjugates_arb_log(u[i], prec)
    for k in 1:length(c)
      #@show T
      @assert radiuslttwopower(c[k], -prec)
    end

    if any(x->radius(x) > 1e-9, c)  # too small...
      @vprint :UnitGroup 2 "increasing prec in scaled_log_matrix, now: $prec\n"
      prec *= 2
      if prec > 2^30
        error("cannot do lll on units")
        break
      end
      return scaled_log_matrix(u, prec)
    end
    for j in 1:length(c)
      tt = fmpz()
      t = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &c[j])
      l = ccall((:arf_get_fmpz_fixed_si, :libarb), Int, (Ptr{fmpz}, Ptr{arf_struct}, Int), &tt, t, -prec)
      A[i, j] = tt
    end
  end
  return A, prec
end

function row_norm(A::fmpz_mat, i::Int)
  return sum([A[i,j]^2 for j=1:cols(A)])
end

function row_norms(A::fmpz_mat)
  return [row_norm(A, i) for i=1:rows(A)]
end

function reduce(u::Array{T, 1}, prec::Int = 32) where T
  r = length(u)
  if r == 0
    return u
  end

  while true
    A, prec = scaled_log_matrix(u, prec)

    L, U = lll_with_transform(A)
    @vprint :UnitGroup 2 "reducing units by $U\n"
    pA = prod(row_norms(A))
    pL = prod(row_norms(L))
    @vprint :UnitGroup 1 "reducing norms of logs from $pA -> $pL, rat is $(Float64(1.0*pA//pL))\n"
    u = transform(u, transpose(U))
    if pL >= pA
      return u
    end
  end  
end

