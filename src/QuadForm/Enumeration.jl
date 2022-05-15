################################################################################
#
#  Lattice enumeration for finding all vectors
#
################################################################################

################################################################################
#
#  Pseudo cholesky decomposition
#
################################################################################

function _pseudo_cholesky(G::fmpz_mat)
  return _pseudo_cholesky(G, fmpq_mat)
end

function _pseudo_cholesky(G::fmpz_mat, ::Type{fmpq_mat})
  n = ncols(G)
  C = zero_matrix(FlintQQ, n, n)
  return __pseudo_cholesky!(C, G)
end

function _pseudo_cholesky(G::fmpz_mat, ::Type{Matrix{fmpq}})
  n = ncols(G)
  C = Matrix{fmpq}(undef, n, n)
  return __pseudo_cholesky!(C, G)
end

function _pseudo_cholesky(G::fmpz_mat, ::Type{Matrix{S}}) where {T, S <: Union{Rational{T}, UnsafeRational{T}}}
  n = ncols(G)
  z = Matrix{S}(undef, n, n)
  C = _pseudo_cholesky(G, Matrix{fmpq})
  for i in 1:n
    for j in 1:n
      z[i, j] = S(T(numerator(C[i, j])), T(denominator(C[i, j])))
    end
  end
  return z
end

function __pseudo_cholesky!(C::fmpq_mat, G)
  n = ncols(G)
  limit = n

  for i=1:limit
    for j=1:limit
      C[i, j] = G[i, j]
    end
  end
  for i = 1:limit-1
    for j = i+1:limit
      C[j, i] = deepcopy(C[i, j])
      C[i, j] = divexact(C[i, j], C[i, i])
    end
    for k = i+1:limit
      for l = i+1:limit
        C[k,l] = C[k,l] - C[k,i] * C[i,l]
      end
    end
  end
  for j = 1:limit-1
    if C[j,j] <= 0
      throw(LowPrecisionCholesky())
    end
    for i=j+1:limit
      C[i, j] = zero!(C[i, j])
    end
  end
  if C[limit, limit] <= 0
    throw(LowPrecisionCholesky())
  end
  return C
end

function __pseudo_cholesky!(C::Matrix{fmpq}, G)
  n = ncols(G)
  limit = n
  t = fmpq()

  for i=1:limit
    for j=1:limit
      C[i, j] = G[i, j]
    end
  end
  for i = 1:limit-1
    for j = i+1:limit
      C[j, i] = _deepcopy_cheap(C[i, j])
      #C[i, j] = divexact(C[i, j], C[i, i])
      C[i, j] = divexact!(C[i, j], C[i, j], C[i, i])
    end
    for k = i+1:limit
      for l = i+1:limit
        t = mul!(t, C[k, i], C[i, l])
        C[k, l] = sub!(C[k, l], C[k, l], t)
        #C[k,l] = C[k,l] - C[k,i] * C[i,l]
      end
    end
  end
  for j = 1:limit-1
    if C[j,j] <= 0
      throw(LowPrecisionCholesky())
    end
    for i=j+1:limit
      C[i, j] = zero!(C[i, j])
    end
  end
  if C[limit, limit] <= 0
    throw(LowPrecisionCholesky())
  end
  return C
end

################################################################################
#
#  Lattice enumeration
#
################################################################################

# We pass l === nothing around to indicate that there is no lower bound.
# This allows us to turn off the lower bound checking during compilation.

function __enumerate_gram(G::fmpz_mat, l::Union{Nothing, Int}, c::Int)
  # This is the "high" level function
  Q = _pseudo_cholesky(G, Matrix{fmpq})
  n = nrows(G)
  d = lcm([denominator(Q[i]) for i in 1:length(G)])
  @vprint :Lattice 1 "Denominator of pseudo-Cholesky of bit size $(nbits(d))\n"
  k = nbits(d) + nbits(n) + 2
  isbig = Int == Int64
  if 2 * k < (isbig ? 32 : 64)
    @vprint :Lattice 1 "Enumerating using Int\n"
    Qint = Matrix{UnsafeRational{Int}}([Int(numerator(q))//Int(denominator(q)) for q in Q])
    res = __enumerate_cholesky(Qint, c)
    @hassert :Lattice 1 length(__enumerate_gram(G, l, c, Rational{Int})) == length(res)
  elseif 2 * k < 64
    @vprint :Lattice 1 "Enumerating using Int64\n"
    Qint64 = Matrix{UnsafeRational{Int64}}([Int64(numerator(q))//Int64(denominator(q)) for q in Q])
    res = __enumerate_cholesky(Qint64, c)
    @hassert :Lattice 1 length(__enumerate_gram(G, l, c, Rational{Int64})) == length(res)
  elseif 2 * k < 128
    Qint128 = Matrix{UnsafeRational{Int128}}([Int128(numerator(q))//Int128(denominator(q)) for q in Q])
    @vprint :Lattice 1 "Enumerating using Int128\n"
    res = __enumerate_cholesky(Qint128, c)
    @hassert :Lattice 1 length(__enumerate_gram(G, l, c, Rational{Int128})) == length(res)
  else
    @vprint :Lattice 1 "Enumerating using fmpq\n"
    res = __enumerate_cholesky(Q, c)
  end
  @hassert :Lattice 1 length(__enumerate_gram(G, l, c, fmpq)) == length(res)
  return res
end

function __enumerate_gram(G::fmpz_mat, l::Union{Int, fmpz, Nothing}, c::Union{Int, fmpz}, ::Type{T}) where {T}
  Q = _pseudo_cholesky(G, Matrix{T})
  v = __enumerate_cholesky(Q, l, c)
  return v
end

function __enumerate_cholesky(Q::fmpq_mat, l::Union{Int, Nothing}, c::Int)
  return __enumerate(Matrix(Q), l, c)
end

function __enumerate_cholesky(Q::Matrix{fmpq}, l::Union{Int, fmpz, Nothing}, c::S) where {S <: Union{Int, fmpz}}
  res = Tuple{Vector{S}, S}[]
  n = nrows(Q)
  i = n
  T = Vector{fmpq}(undef, n)
  U = Vector{fmpq}(undef, n)

  for i in 1:n
    T[i] = fmpq()
    U[i] = fmpq()
  end
  x = Vector{S}(undef, n)
  L = Vector{S}(undef, n)

  T[i] = c
  U[i] = 0

  t1 = fmpq()
  t2 = fmpz()
  t3 = fmpz()
  t4 = fmpz()
  t5 = fmpz()

  Qd = Vector{fmpq}(undef, n) # diagonal of Q
  @inbounds for i in 1:n
    Qd[i] = Q[i, i]
  end

  @label compute_bounds

  # For debugging purposes. This gives the tightest bounds
  #xc = -U[i]
  #while (Q[i, i] * (xc + U[i])^2 <= T[i])
  #  xc -= 1
  #end
  #x[i] = Int(FlintZZ(floor(xc)))

  #upperbound_can = -U[i]
  #while (Q[i, i] * (upperbound_can + U[i])^2 <= T[i])
  #  upperbound_can += 1
  #end
  #L[i] = Int(FlintZZ(ceil(upperbound_can)))

  # For debugging purposes: Fast, but allocating
  #
  #_t = isqrt(FlintZZ(floor(divexact(T[i], Q[i, i]))))
  #_new_upp = Int(FlintZZ(ceil(_t + 2 - U[i])))
  #_new_low = Int(FlintZZ(floor(-(_t + 2) - U[i]))) - 1

  @inbounds _new_upp, _new_low = _compute_bounds(T[i], Qd[i], U[i], t1, t2, t3, t4, t5)

  @inbounds x[i] = _new_low
  @inbounds L[i] = _new_upp

  @label main_loop

  @inbounds x[i] = x[i] + 1

  @inbounds if x[i] > L[i]
    i = i + 1
    @goto main_loop
  else
    if i > 1
      #T[i - 1] = T[i] - Q[i, i] * (x[i] + U[i])^2
      @inbounds update_T!(T, i, Qd, x, U, t1)
      @inbounds if is_negative(T[i - 1])
        @goto main_loop
      end
      i = i - 1
      #U[i] = sum(Q[i, j] * x[j] for j in (i + 1):n)
      update_U!(U, Q, i, n, x, t1, t2)
      @goto compute_bounds
    end
  end

  if iszero(x)
    return res
  else
    #len = c - T[1] + Q[1, 1]*(x[1] + U[1])^2
    t1 = compute_len!(t1, c, T, Q, x, U)
    t2 = numerator!(t2, t1)
    _short_enough = false
    if S === Int
      _len = ccall((:fmpz_get_si, libflint), Int, (Ref{fmpz}, ), t2)
      _short_enough = _len <= c
      if !(l isa Nothing)
        _short_enough = _short_enough && _len >= l
      end
      len = _len
    else
      _short_enough = t2 <= c
      if !(l isa Nothing)
        _short_enough = _short_enouh && t2 >= l
      end

      len = deepcopy(t2)
    end

    if _short_enough
      # t1 must be a UInt
      #z = fmpq()
      #ccall((:fmpq_set, libflint), Cvoid, (Ref{fmpq}, Ref{fmpq}), z, t1)
      # Todo
      y = Vector{S}(undef, n)
      if S === fmpz
        for i in 1:n
          @inbounds y[i] = deepcopy(x[i])
        end
      else
        for i in 1:n
          @inbounds y[i] = x[i]
        end
      end
      push!(res, (y, len))
    end
    @goto main_loop
  end
end

function __enumerate_cholesky(Q::Matrix{S}, l::Union{Int, Nothing}, c::Int) where {S <: Union{Rational, UnsafeRational}}
  res = Tuple{Vector{Int}, Int}[]
  n = nrows(Q)
  i = n
  T = Vector{S}(undef, n)
  U = Vector{S}(undef, n)
  L = Vector{S}(undef, n)
  #for i in 1:n
  #  T[i] = 0
  #  U[i] = 0
  #end
  x = Vector{Int}(undef, n)

  T[i] = c
  U[i] = 0

  Qd = Vector{S}(undef, n)
  for i in 1:n
    Qd[i] = Q[i, i]
  end

  #@show d = lcm(Int[denominator(a) for a in Q])
  #@show nbits(d)

  @label compute_bounds

  # For debugging purposes. This gives the tightest bounds
  #xc = -U[i]
  #while (Q[i, i] * (xc + U[i])^2 <= T[i])
  #  xc -= 1
  #end
  #x[i] = Int(FlintZZ(floor(xc)))

  #upperbound_can = -U[i]
  #while (Q[i, i] * (upperbound_can + U[i])^2 <= T[i])
  #  upperbound_can += 1
  #end
  #L[i] = Int(FlintZZ(ceil(upperbound_can)))

  # For debugging purposes: Fast, but allocating
  #
  #_t = isqrt(FlintZZ(floor(divexact(T[i], Q[i, i]))))
  #_new_upp = Int(FlintZZ(ceil(_t + 2 - U[i])))
  #_new_low = Int(FlintZZ(floor(-(_t + 2) - U[i]))) - 1

  _new_upp, _new_low = @inbounds _compute_bounds(T[i], Qd[i], U[i])

  @inbounds x[i] = _new_low
  @inbounds L[i] = _new_upp

  @label main_loop

  @inbounds x[i] = x[i] + 1

  @inbounds if x[i] > L[i]
    i = i + 1
    @goto main_loop
  else
    if i > 1
      #T[i - 1] = T[i] - Q[i, i] * (x[i] + U[i])^2
      @inbounds update_T!(T, i, Qd, x, U)
      @inbounds if is_negative(T[i - 1])
        @goto main_loop
      end
      i = i - 1
      #U[i] = sum(Q[i, j] * x[j] for j in (i + 1):n)
      update_U!(U, Q, i, n, x)

      @goto compute_bounds
    end
  end

  if iszero(x)
    return res
  else
    #len = c - T[1] + Q[1, 1]*(x[1] + U[1])^2
    len = Int(compute_len!(c, T, Q, x, U))
    if len <= c
      if l isa Int
        if len >= l
          y = Vector{Int}(undef, n)
          @inbounds for i in 1:n
            y[i] = x[i]
          end
          push!(res, (y, len))
        end
      else
        y = Vector{Int}(undef, n)
        @inbounds for i in 1:n
          y[i] = x[i]
        end
        push!(res, (y, len))
      end
    end
    @goto main_loop
  end
end

@inline function _compute_bounds(Ti, Qi, Ui, t1 = fmpq(),
                                             t2 = fmpz(),
                                             t3 = fmpz(),
                                             t4 = fmpz(),
                                             t5 = fmpz())
  t1 = divexact!(t1, Ti, Qi)
  t2 = floor!(t2, t1, t3, t4)
  t2 = isqrt!(t2, t2)
  # Now t2 = ceil(sqrt(Ti/Qi))
  t2 = add_two!(t2, t2)
  # Now t2 = ceil(sqrt(Ti/Qi)) + 2

  t1 = sub!(t1, Ui, t2)
  t1 = neg!(t1, t1)
  t5 = ceil!(t5, t1, t3, t4)
  ub = ccall((:fmpz_get_si, libflint), Int, (Ref{fmpz}, ), t5)

  t1 = add!(t1, Ui, t2)
  t1 = neg!(t1, t1)
  t5 = floor!(t5, t1, t3, t4)
  lb = ccall((:fmpz_get_si, libflint), Int, (Ref{fmpz}, ), t5) - 1

  return ub, lb
end

@inline function _compute_bounds(Ti::Union{UnsafeRational, Rational{<:Integer}}, Qi, Ui)
  t1 = Ti//Qi
  t2 = Int(floor(t1))
  t2 = isqrt(t2)
  # Now t2 = ceil(sqrt(Ti/Qi))
  t2 += 2
  # Now t2 = ceil(sqrt(Ti/Qi)) + 2

  t1 = Ui - t2
  t1 = -t1
  t5 = Int(ceil(t1))
  ub = t5

  t1 = Ui + t2
  t1 = -t1
  t5 = Int(floor(t1))
  lb = t5

  return ub, lb - 1
end

@inline function update_T!(T, i, Qd, x, U, t = fmpq())
  @inbounds t = add!(t, U[i], x[i])
  t = mul!(t, t, t)
  t = mul!(t, t, Qd[i])
  sub!(T[i - 1], T[i], t)
end

@inline function update_T!(T::Vector{S}, i, Qd, x, U) where S <: Union{Rational{<:Integer}, UnsafeRational}
  # T[i - 1] = T[i] - QQ[i, i] * (U[i] + x[i])^2
  @inbounds t = U[i] + x[i]
  t = t * t
  @inbounds t = t * Qd[i]
  @inbounds T[i - 1] = T[i] - t
  #@assert Rational(T[i - 1]) == Rational(T[i]) - Rational(QQ[i, i]) * (Rational(U[i]) + Rational(x[i]))^2
end

@inline function update_U!(U, QQ, i, n, x, t = fmpq(), t2 = fmpz())
  # U[i] = sum(QQ[i, j] * x[j] for j in (i + 1):n)
  s = @inbounds U[i]
  @inbounds ccall((:fmpz_set_si, libflint), Cvoid, (Ref{fmpz}, Int), t2, x[i + 1])
  @inbounds s = mul!(s, QQ[i, i + 1], t2)
  for j in (i + 2):n
    @inbounds ccall((:fmpz_set_si, libflint), Cvoid, (Ref{fmpz}, Int), t2, x[j])
    @inbounds mul!(t, QQ[i, j], t2)
    s = add!(s, s, t)
    #addmul!(s, QQ[i, j], t2, t)
  end
  return s
end

@inline function update_U!(U, QQ::Matrix{S}, i, n, x) where S <: Union{Rational{<:Integer}, UnsafeRational}
  # U[i] = sum(QQ[i, j] * x[j] for j in (i + 1):n)
  @inbounds s = QQ[i, i + 1] * x[i + 1]
  @inbounds for j in (i + 2):n
    t = QQ[i, j] * x[j]
    s = s + t
    #addmul!(s, QQ[i, j], t2, t)
  end
  U[i] = s
  #@assert Rational(U[i]) == sum(Rational(QQ[i, j]) * Rational(x[j]) for j in (i + 1):n)
end

@inline function compute_len!(t, c, T, QQ, x, U)
#len = c - T[1] + QQ[1, 1]*(x[1] + U[1])^2
  t = @inbounds add!(t, U[1], x[1])
  t = mul!(t, t, t)
  t = @inbounds mul!(t, t, QQ[1, 1])
  t = add!(t, t, c)
  t = @inbounds sub!(t, t, T[1])
  return t
end

@inline function compute_len!(c, T::Vector{S}, QQ, x, U) where S <: Union{Rational{<:Integer}, UnsafeRational}
#len = c - T[1] + QQ[1, 1]*(x[1] + U[1])^2
  s = @inbounds begin
  t = U[1] + x[1]
  t = t * t
  t = t * QQ[1, 1]
  t = t + c
  t = t - T[1]
  end
  return s
end

function _deepcopy_cheap(x::fmpq)
  z = fmpq()
  ccall((:fmpq_set, libflint), Cvoid, (Ref{fmpq}, Ref{fmpq}), z, x)
  return z
end

function is_negative(x::fmpq)
  c = ccall((:fmpq_sgn, libflint), Cint, (Ref{fmpq}, ), x)
  return c < 0
end

function is_lessorequal(x::fmpq, y::UInt)
  c = ccall((:fmpq_cmp_ui, libflint), Cint, (Ref{fmpq}, UInt), x, y)
  return c <= 0
end

################################################################################
#
#  Enumeration functions on gram matrices
#
################################################################################

# This is the work horse
# Assumes that G is a gram matrix, finds all vectors v with length l
# lb <= v < ub. Also applies the transformation transform
#
# If transform === nothing, no transform
#
# Return value is Vector{Tuple{Vector{Int}, fmpz}}
function _short_vectors_gram_nolll_integral(G, _lb, _ub, transform)
  n = nrows(G)
  ub = floor(fmpz, _ub)
  # G is integral, so q(x) <= ub is equivalent to q(x) <= floor(ub)
  #                lb <= q(x) is equivalent to ceil(ub) <= q(x)

  if ub isa fmpz && fits(Int, ub)
    if _lb isa Nothing
      V = __enumerate_gram(G, nothing, Int(ub), fmpq)
    else
      lb = ceil(fmpz, _lb)
      if iszero(lb)
        V = __enumerate_gram(G, nothing, Int(ub), fmpq)
      else
        V = __enumerate_gram(G, Int(lb), Int(ub), fmpq)
      end
    end
  else
    if _lb isa Nothing
      V = __enumerate_gram(G, nothing, ub, fmpq)
    else
      lb = ceil(fmpz, _lb)
      if iszero(lb)
        V = __enumerate_gram(G, nothing, ub, fmpq)
      else
        V = __enumerate_gram(G, lb, ub, fmpq)
      end
    end
  end

  if ub isa fmpz
    W = Vector{Tuple{Vector{fmpz}, fmpz}}()
  else
    W = Vector{Tuple{Vector{Int}, fmpz}}()
  end

  for (v, l) in V
    m = _transform(v, transform)

    positive = false
    for k in 1:n
      if iszero(m[k])
        continue
      end
      if m[k] > 0
        positive = true
      end
      break
    end

    if positive
      push!(W, (m, FlintZZ(l)))
    else
      push!(W, (-m, FlintZZ(l)))
    end
  end
  return W
end

# No assumption on _G, algorithm applies LLL

function _short_vectors_gram(_G, lb, ub::Rational{<: Integer}; hard::Bool = false)
  return _short_vectors_gram(_G, lb, fmpq(ub); hard = hard)
end

function _short_vectors_gram(_G, lb, ub; hard::Bool = false)
  d = denominator(_G)
  G = change_base_ring(FlintZZ, d * _G)
  if hard
    Glll, T = lll_gram_with_transform(G, lll_ctx(0.99999999999999, 0.500000000001, :gram))
  else
    Glll, T = lll_gram_with_transform(G, lll_ctx(0.9999, 0.5001, :gram))
  end
  if isone(T)
    V = _short_vectors_gram_nolll_integral(Glll, d * lb, d * ub, nothing)
  else
    V = _short_vectors_gram_nolll_integral(Glll, d * lb, d * ub, T)
  end
  W = Vector{Tuple{Vector{Int}, elem_type(base_ring(_G))}}(undef, length(V))
  for i in 1:length(V)
    W[i] = (V[i][1], V[i][2]//d)
  end
  return W
end

# No assumption on _G, algorithm applies LLL
function _short_vectors_gram(_G, ub; hard::Bool = false)
  return _short_vectors_gram(_G, fmpz(0), ub, hard = hard)
end

# No assumption on _G, algorithm applies LLL
function _shortest_vectors_gram(_G)
  d = denominator(_G)
  G = change_base_ring(FlintZZ, d * _G)
  Glll, T = lll_gram_with_transform(G)
  max = maximum([Glll[i, i] for i in 1:nrows(G)])
  @assert max > 0
  if isone(T)
    V = _short_vectors_gram_nolll_integral(Glll, 0, max, nothing)
  else
    V = _short_vectors_gram_nolll_integral(Glll, 0, max, T)
  end
  min = minimum(v[2] for v in V)
  return min//d, Vector{fmpz}[ v[1] for v in V if v[2] == min]
end

function _short_vectors_gram_integral(_G, ub; hard = false)
  if hard
    Glll, T = lll_gram_with_transform(_G, lll_ctx(0.99999999999999, 0.500000000001, :gram))
  else
    Glll, T = lll_gram_with_transform(_G)
  end
  if isone(T)
    V = _short_vectors_gram_nolll_integral(Glll, 0, ub, nothing)
  else
    V = _short_vectors_gram_nolll_integral(Glll, 0, ub, T)
  end

  return V
end

function _shortest_vectors_gram_integral(_G)
  Glll, T = lll_gram_with_transform(_G)
  max = maximum([Glll[i, i] for i in 1:nrows(Glll)])
  @assert max > 0
  if isone(T)
    V = _short_vectors_gram_nolll_integral(Glll, 0, max, nothing)
  else
    V = _short_vectors_gram_nolll_integral(Glll, 0, max, T)
  end
  min = minimum(v[2] for v in V)
  return min, [ v for v in V if v[2] == min]
end

_transform(m::fmpz_mat, T) = m * T

_transform(m, ::Nothing) = m

_transform(m::Vector{Int}, ::Nothing) = m

function _transform(m::Vector{Int}, T)
  n = matrix(FlintZZ, 1, nrows(T), m) * T
  return fmpz[n[1, i] for i in 1:nrows(T)]
end

function _transform(m::Vector{fmpz}, T)
  n = matrix(FlintZZ, 1, nrows(T), m) * T
  return fmpz[n[1, i] for i in 1:nrows(T)]
end

################################################################################
#
#  Additional inplace operations
#
################################################################################

@inline function numerator!(z::fmpz, y::fmpq)
  ccall((:fmpq_numerator, libflint), Cvoid, (Ref{fmpz}, Ref{fmpq}), z, y)
  return z
end

@inline function denominator!(z::fmpz, y::fmpq)
  ccall((:fmpq_denominator, libflint), Cvoid, (Ref{fmpz}, Ref{fmpq}), z, y)
  return z
end

@inline function floor!(z::fmpz, y::fmpq, t0::fmpz, t1::fmpz)
  numerator!(t0, y)
  denominator!(t1, y)
  ccall((:fmpz_fdiv_q, libflint), Cvoid, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, t0, t1)
  return z
end

@inline function ceil!(z::fmpz, y::fmpq, t0::fmpz, t1::fmpz)
  numerator!(t0, y)
  denominator!(t1, y)
  ccall((:fmpz_cdiv_q, libflint), Cvoid, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, t0, t1)
  return z
end

@inline function divexact!(z::fmpq, a::fmpq, b::fmpq)
  ccall((:fmpq_div, libflint), Cvoid, (Ref{fmpq}, Ref{fmpq}, Ref{fmpq}), z, a, b)
  return z
end

@inline function add_two!(z::fmpz, x::fmpz)
  ccall((:fmpz_add_ui, libflint), Cvoid, (Ref{fmpz}, Ref{fmpz}, Int), z, x, 2)
  return z
end

@inline function sub!(z::fmpq, a::fmpq, b::fmpq)
  ccall((:fmpq_sub, libflint), Cvoid, (Ref{fmpq}, Ref{fmpq}, Ref{fmpq}), z, a, b)
  return z
end

@inline function sub!(z::fmpq, a::fmpq, b::fmpz)
  ccall((:fmpq_sub_fmpz, libflint), Cvoid, (Ref{fmpq}, Ref{fmpq}, Ref{fmpz}), z, a, b)
  return z
end

@inline function neg!(z::fmpq, a::fmpq)
  ccall((:fmpq_neg, libflint), Cvoid, (Ref{fmpq}, Ref{fmpq}), z, a)
  return z
end

@inline function isqrt!(z::fmpz, a::fmpz)
  ccall((:fmpz_sqrt, libflint), Cvoid, (Ref{fmpz}, Ref{fmpz}), z, a)
  return z
end

divexact!(z::Rational{Int}, x::Rational{Int}, y::Rational{Int}) = divexact(x, y)

floor!(z::Int, x::Rational{Int}, y::Int, w::Int) = Int(floor(x))

isqrt!(z::Int, x::Int) = isqrt(x)

add_two!(z::Int, x::Int) = x + 2

sub!(z::Rational{Int}, x::Rational{Int}, y::Int) = x - y

neg!(z::Rational{Int}, x::Rational{Int}) = -x

ceil!(z::Int, x::Rational{Int}, y::Int, w::Int) = Int(ceil(x))

add!(z::Rational{Int}, x::Rational{Int}, y::Int) = x + y

mul!(z::Rational{Int}, x::Rational{Int}, y::Int) = x * y

numerator!(z::Int, x::Rational{Int}) = numerator(x)

is_negative(x::Rational) = x.num < 0

