################################################################################
#
#  Lattice enumeration for finding all vectors
#
################################################################################

# This implements the algorithm of Fincke-Pohst for enumeration with using
# a Gram matrix. So given positive definite G and b, find all v such that
# v * G * v^t <= b
#
# The main function is
# _short_vectors_gram_nolll_integral(::Type{T}, G, _lb, _ub, transform::X, d::Y) where {T, X, Y}

################################################################################
#
#  Pseudo cholesky decomposition
#
################################################################################

function _pseudo_cholesky(G::ZZMatrix)
  return _pseudo_cholesky(G, QQMatrix)
end

function _pseudo_cholesky(G::ZZMatrix, ::Type{QQMatrix})
  n = ncols(G)
  C = zero_matrix(QQ, n, n)
  return __pseudo_cholesky!(C, G)
end

function _pseudo_cholesky(G::ZZMatrix, ::Type{Matrix{QQFieldElem}})
  n = ncols(G)
  C = Matrix{QQFieldElem}(undef, n, n)
  if n == 0
    return C
  end
  return __pseudo_cholesky!(C, G)
end

function _pseudo_cholesky(G::ZZMatrix, ::Type{Matrix{S}}) where {T, S <: Union{Rational{T}, UnsafeRational{T}}}
  n = ncols(G)
  z = Matrix{S}(undef, n, n)
  C = _pseudo_cholesky(G, Matrix{QQFieldElem})
  for i in 1:n
    for j in 1:n
      z[i, j] = S(T(numerator(C[i, j])), T(denominator(C[i, j])))
    end
  end
  return z
end

function __pseudo_cholesky!(C::QQMatrix, G)
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

function __pseudo_cholesky!(C::Matrix{QQFieldElem}, G)
  n = ncols(G)
  limit = n
  t = QQFieldElem()

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

function __enumerate_gram(::Type{T}, G::ZZMatrix, l::Union{Nothing, Int}, c::Int) where {T}
  # This is the "high" level function
  Q = _pseudo_cholesky(G, Matrix{QQFieldElem})
  n = nrows(G)
  d = lcm([denominator(Q[i]) for i in 1:length(G)])
  @vprintln :Lattice 1 "Denominator of pseudo-Cholesky of bit size $(nbits(d))"
  k = nbits(d) + nbits(n) + 2
  isbig = Int == Int64
  if 2 * k < (isbig ? 32 : 64)
    @vprintln :Lattice 1 "Enumerating using Int"
    Qint = Matrix{UnsafeRational{Int}}([Int(numerator(q))//Int(denominator(q)) for q in Q])
    res = __enumerate_cholesky(T, Qint, l, c)
    @hassert :Lattice 1 length(__enumerate_gram(G, l, c, Rational{Int})) == length(res)
  elseif 2 * k < 64
    @vprintln :Lattice 1 "Enumerating using Int64"
    Qint64 = Matrix{UnsafeRational{Int64}}([Int64(numerator(q))//Int64(denominator(q)) for q in Q])
    res = __enumerate_cholesky(T, Qint64, l, c, identity, identity, ZZRingElem)
    @hassert :Lattice 1 length(__enumerate_gram(T, G, l, c, Rational{Int64}, identity, identity, ZZRingElem)) == length(res)
  elseif 2 * k < 128
    Qint128 = Matrix{UnsafeRational{Int128}}([Int128(numerator(q))//Int128(denominator(q)) for q in Q])
    @vprintln :Lattice 1 "Enumerating using Int128"
    res = __enumerate_cholesky(T, Qint128, l, c, identity, identity, ZZRingElem)
    @hassert :Lattice 1 length(__enumerate_gram(T, G, l, c, Rational{Int128}, identity, identity, ZZRingElem)) == length(res)
  else
    @vprintln :Lattice 1 "Enumerating using QQFieldElem"
    res = __enumerate_cholesky(T, Q, l, c, identity, identity, ZZRingElem)
  end
  @hassert :Lattice 1 length(__enumerate_gram(T, G, l, c, QQFieldElem, identity, identity, ZZRingElem)) == length(res)
  return res
end

function __enumerate_gram(::Type{S}, G::ZZMatrix, l::Union{Int, ZZRingElem, Nothing}, c::Union{Int, ZZRingElem}, ::Type{T}, pp_vector::X, pp_length::Y, elem_type::Type{U}) where {S, T, X, Y, U}
  Q = _pseudo_cholesky(G, Matrix{T})
  v = __enumerate_cholesky(S, Q, l, c, pp_vector, pp_length, elem_type)
  return v
end

struct LatEnumCtx{X, Y, elem_type}
  n::Int
  i::Int
  T::Vector{QQFieldElem}
  U::Vector{QQFieldElem}
  x::Vector{Int}
  L::Vector{Int}
  Qd::Vector{QQFieldElem}
  Q::Matrix{QQFieldElem}
  t1::QQFieldElem
  t2::ZZRingElem
  t3::ZZRingElem
  t4::ZZRingElem
  t5::ZZRingElem
  l::ZZRingElem
  c::ZZRingElem
  pp_vector::X
  pp_length::Y
  lowerbound::Bool
end

function __enumerate_cholesky(U::Type{LatEnumCtx}, Q::Matrix{QQFieldElem}, l::Union{Int, ZZRingElem, Nothing}, c::S, pp_vector::X, pp_length::Y, elem_type::Type{UU}) where {S <: Union{Int, ZZRingElem}, X, Y, UU}
  return ___enumerate_cholesky(U, Q, l, c, pp_vector, pp_length, elem_type)
end

function __enumerate_cholesky(U::Type{Vector}, Q::Matrix{E}, l::Union{Int, ZZRingElem, Nothing}, c::S, pp_vector::X, pp_length::Y, elem_type::Type{UU}) where {S <: Union{Int, ZZRingElem}, X, Y, UU, E}
  if E === QQFieldElem
    return ___enumerate_cholesky(U, Q, l, c, elem_type)
  else
    return ___enumerate_cholesky(U, Q, l, c)
  end
end

function ___enumerate_cholesky(::Type{LatEnumCtx}, Q::Matrix{QQFieldElem}, l::Union{Int, ZZRingElem, Nothing}, c::S, pp_vector::X, pp_length::Y, elem_type::Type{UU}) where {S <: Union{Int, ZZRingElem}, X, Y, UU}
  n = nrows(Q)
  i = n
  T = Vector{QQFieldElem}(undef, n)
  U = Vector{QQFieldElem}(undef, n)

  for j in 1:n
    T[j] = QQFieldElem()
    U[j] = QQFieldElem()
  end
  x = Vector{Int}(undef, n)
  L = Vector{Int}(undef, n)
  fill!(x, 0)
  fill!(L, 0)

  if n != 0
    T[i] = c
    U[i] = 0
  end

  t1 = QQFieldElem()
  t2 = ZZRingElem()
  t3 = ZZRingElem()
  t4 = ZZRingElem()
  t5 = ZZRingElem()

  Qd = Vector{QQFieldElem}(undef, n) # diagonal of Q
  @inbounds for i in 1:n
    Qd[i] = Q[i, i]
  end

  _c = ZZRingElem(c)

  if l == 0 || l isa Nothing
    _l = zero(ZZRingElem)
    lower = false
  else
    _l = ZZRingElem(l)
    lower = true
  end

  return LatEnumCtx{X, Y, elem_type}(n, n, T, U, x, L, Qd, Q, t1, t2, t3, t4, t5, _l, _c, pp_vector, pp_length, lower)
end

Base.eltype(::Type{LatEnumCtx{X, Y, elem_type}}) where {X, Y, elem_type} = Tuple{Vector{elem_type}, QQFieldElem}

function Base.iterate(C::LatEnumCtx{X, Y, elem_type}) where {X, Y, elem_type}
  n = C.n
  T = C.T
  U = C.U
  x = C.x
  L = C.L
  Qd = C.Qd
  Q = C.Q
  t1 = C.t1
  t2 = C.t2
  t3 = C.t3
  t4 = C.t4
  t5 = C.t5
  c = C.c
  l = C.l
  pp_vector = C.pp_vector
  pp_length = C.pp_length
  lowerbound = C.lowerbound

  i = n

  if n == 0
    return nothing
  end

  @label compute_bounds

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
    return nothing
  else
    #len = c - T[1] + Q[1, 1]*(x[1] + U[1])^2
    t1 = compute_len!(t1, c, T, Q, x, U)
    t2 = numerator!(t2, t1)
    _short_enough = t2 <= c
    if lowerbound && _short_enough
      _short_enough = t2 >= l
    end

    len = t2

    if _short_enough
      # t1 must be a UInt
      #z = QQFieldElem(t1)
      # Todo
      return (pp_vector(x), pp_length(len)), i
      #y = Vector{S}(undef, n)
      #if S === ZZRingElem
      #  for i in 1:n
      #    @inbounds y[i] = deepcopy(x[i])
      #  end
      #else
      #  for i in 1:n
      #    @inbounds y[i] = x[i]
      #  end
      #end
      #return (y, len), i
    end
    @goto main_loop
  end
end

function Base.iterate(C::LatEnumCtx{S, W, V}, it::Int) where {S, W, V}
  n = C.n
  T = C.T
  U = C.U
  x = C.x
  L = C.L
  Qd = C.Qd
  Q = C.Q
  t1 = C.t1
  t2 = C.t2
  t3 = C.t3
  t4 = C.t4
  t5 = C.t5
  c = C.c
  l = C.l
  pp_vector = C.pp_vector
  pp_length = C.pp_length
  i = it
  lowerbound = C.lowerbound

  @goto main_loop

  @label compute_bounds

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
    return nothing
  else
    #len = c - T[1] + Q[1, 1]*(x[1] + U[1])^2
    t1 = compute_len!(t1, c, T, Q, x, U)
    t2 = numerator!(t2, t1)
    _short_enough = t2 <= c
    if lowerbound && _short_enough
      _short_enough = t2 >= l
    end

    len = t2

    if _short_enough
      # t1 must be a UInt
      #z = QQFieldElem(t1)
      # Todo
      #y = __clean_and_assemble(x, transform)
      #return (y, len//scale), i
      return (pp_vector(x), pp_length(len)), i

      #y = Vector{S}(undef, n)
      #if S === ZZRingElem
      #  for i in 1:n
      #    @inbounds y[i] = deepcopy(x[i])
      #  end
      #else
      #  for i in 1:n
      #    @inbounds y[i] = x[i]
      #  end
      #end
      #return (y, len), i
    end
    @goto main_loop
  end
end

function ___enumerate_cholesky(::Type{Vector}, Q::Matrix{QQFieldElem}, l::Union{Int, ZZRingElem, Nothing}, c::S, elem_type::Type{UU}) where {S <: Union{Int, ZZRingElem}, UU}
  res = Tuple{Vector{S}, S}[]
  n = nrows(Q)
  i = n
  T = Vector{QQFieldElem}(undef, n)
  U = Vector{QQFieldElem}(undef, n)

  for i in 1:n
    T[i] = QQFieldElem()
    U[i] = QQFieldElem()
  end
  x = Vector{S}(undef, n)
  L = Vector{S}(undef, n)

  T[i] = c
  U[i] = 0

  t1 = QQFieldElem()
  t2 = ZZRingElem()
  t3 = ZZRingElem()
  t4 = ZZRingElem()
  t5 = ZZRingElem()

  Qd = Vector{QQFieldElem}(undef, n) # diagonal of Q
  @inbounds for i in 1:n
    Qd[i] = Q[i, i]
  end

  @label compute_bounds

  # For debugging purposes. This gives the tightest bounds
  #xc = -U[i]
  #while (Q[i, i] * (xc + U[i])^2 <= T[i])
  #  xc -= 1
  #end
  #x[i] = Int(ZZ(floor(xc)))

  #upperbound_can = -U[i]
  #while (Q[i, i] * (upperbound_can + U[i])^2 <= T[i])
  #  upperbound_can += 1
  #end
  #L[i] = Int(ZZ(ceil(upperbound_can)))

  # For debugging purposes: Fast, but allocating
  #
  #_t = isqrt(ZZ(floor(divexact(T[i], Q[i, i]))))
  #_new_upp = Int(ZZ(ceil(_t + 2 - U[i])))
  #_new_low = Int(ZZ(floor(-(_t + 2) - U[i]))) - 1

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
      _len = Int(t2)
      _short_enough = _len <= c
      if !(l isa Nothing)
        _short_enough = _short_enough && _len >= l
      end
      len = _len
    else
      _short_enough = t2 <= c
      if !(l isa Nothing)
        _short_enough = _short_enough && t2 >= l
      end

      len = deepcopy(t2)
    end

    if _short_enough
      # t1 must be a UInt
      #z = QQFieldElem()
      #set!(z, t1)
      # Todo
      y = Vector{elem_type}(undef, n)
      if S === elem_type
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

function ___enumerate_cholesky(::Type{Vector}, Q::Matrix{S}, l::Union{Int, Nothing}, c::Int) where {S <: Union{Rational, UnsafeRational}}
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
  #x[i] = Int(ZZ(floor(xc)))

  #upperbound_can = -U[i]
  #while (Q[i, i] * (upperbound_can + U[i])^2 <= T[i])
  #  upperbound_can += 1
  #end
  #L[i] = Int(ZZ(ceil(upperbound_can)))

  # For debugging purposes: Fast, but allocating
  #
  #_t = isqrt(ZZ(floor(divexact(T[i], Q[i, i]))))
  #_new_upp = Int(ZZ(ceil(_t + 2 - U[i])))
  #_new_low = Int(ZZ(floor(-(_t + 2) - U[i]))) - 1

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

@inline function _compute_bounds(Ti::QQFieldElem, Qi, Ui, t1 = QQFieldElem(),
                                             t2 = ZZRingElem(),
                                             t3 = ZZRingElem(),
                                             t4 = ZZRingElem(),
                                             t5 = ZZRingElem())
  t1 = divexact!(t1, Ti, Qi)
  t2 = floor!(t2, t1, t3, t4)
  t2 = isqrt!(t2, t2)
  # Now t2 = ceil(sqrt(Ti/Qi))
  t2 = add!(t2, 2)
  # Now t2 = ceil(sqrt(Ti/Qi)) + 2

  t1 = sub!(t1, Ui, t2)
  t1 = neg!(t1)
  t5 = ceil!(t5, t1, t3, t4)
  ub = Int(t5)  # will throw if t5 does not fit into an Int

  t1 = add!(t1, Ui, t2)
  t1 = neg!(t1)
  t5 = floor!(t5, t1, t3, t4)
  lb = Int(t5) - 1   # will throw if t5 does not fit into an Int

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

@inline function update_T!(T::Vector{QQFieldElem}, i, Qd, x, U, t = QQFieldElem())
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

@inline function update_U!(U, QQ::Matrix{QQFieldElem}, i, n, x, t = QQFieldElem(), t2 = ZZRingElem())
  # U[i] = sum(QQ[i, j] * x[j] for j in (i + 1):n)
  s = @inbounds U[i]
  @inbounds set!(t2, x[i + 1])
  @inbounds s = mul!(s, QQ[i, i + 1], t2)
  for j in (i + 2):n
    @inbounds set!(t2, x[j])
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

_deepcopy_cheap(x::QQFieldElem) = set!(QQFieldElem(), x)

function is_lessorequal(x::QQFieldElem, y::UInt)
  c = ccall((:fmpq_cmp_ui, libflint), Cint, (Ref{QQFieldElem}, UInt), x, y)
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
# If transform === nothing, no transform in the vector case
#
# Return value is Vector{Tuple{Vector{S}, ZZRingElem}}
function _short_vectors_gram_nolll_integral(::Type{T}, G, _lb, _ub, transform::X, d::Y, elem_type::Type{S} = ZZRingElem) where {T, X, Y, S}
  n = nrows(G)
  ub = floor(ZZRingElem, _ub)
  # G is integral, so q(x) <= ub is equivalent to q(x) <= floor(ub)
  #                lb <= q(x) is equivalent to ceil(lb) <= q(x)

  # We pass the following function through to the iterator
  # They are applied to the vector found and the length of the vector
  cleanvec = v -> __clean_and_assemble(v, transform, !isnothing(transform) && !isone(transform), S)
  cleanscalar = l -> l//d

  if ub isa ZZRingElem && fits(Int, ub)
    if _lb isa Nothing
      V = __enumerate_gram(T, G, nothing, Int(ub), QQFieldElem, cleanvec, cleanscalar, elem_type)
    else
      lb = ceil(ZZRingElem, _lb)
      if iszero(lb)
        V = __enumerate_gram(T, G, nothing, Int(ub), QQFieldElem,
                             cleanvec, cleanscalar, elem_type)
      else
        V = __enumerate_gram(T, G, Int(lb), Int(ub), QQFieldElem,
                             cleanvec, cleanscalar, elem_type)
      end
    end
  else
    if _lb isa Nothing
      V = __enumerate_gram(T, G, nothing, ub, QQFieldElem,
                             cleanvec, cleanscalar, elem_type)
    else
      lb = ceil(ZZRingElem, _lb)
      if iszero(lb)
        V = __enumerate_gram(T, G, nothing, ub, QQFieldElem,
                             cleanvec, cleanscalar, elem_type)
      else
        V = __enumerate_gram(T, G, lb, ub, QQFieldElem,
                             cleanvec, cleanscalar, elem_type)
      end
    end
  end

  # V is type-unstable, so we use a function barrier
  if V isa Vector
    W = Vector{Tuple{Vector{S}, QQFieldElem}}()
    __assemble_result!(W, V, transform, n)
    return W
  else
    return V
  end
end

Base.IteratorSize(::Type{<:LatEnumCtx}) = Base.SizeUnknown()

function __clean_and_assemble(v::V, transform::U, dotransform::Bool, elem_type::Type{S} = ZZRingElem) where {V, U, S}
  # this may or may not produce a copy
  if dotransform
    m = _transform(v, transform)
  else
    m = v
  end
  n = length(v)

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
    if S === eltype(m)
      return copy(m)
    else
      return S.(m)
    end
  else
    return S.(-m)
  end
end

function __assemble_result!(W, V::T, transform, n) where {T}
  k = 0
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
      push!(W, (m, QQ(l)))
    else
      push!(W, (-m, QQ(l)))
    end
    k += 1
  end
  return k
end

# No assumption on _G, algorithm applies LLL

function _short_vectors_gram(::Type{T}, _G, lb, ub::Rational{<: Integer}, elem_type::Type{S} = ZZRingElem; hard::Bool = false) where {T, S}
  return _short_vectors_gram(T, _G, lb, QQFieldElem(ub), S; hard = hard)
end

function _short_vectors_gram(::Type{S}, _G, lb, ub, elem_type::Type{U} = ZZRingElem; hard::Bool = false) where {S, U}
  d = denominator(_G)
  G = change_base_ring(ZZ, d * _G)
  if isempty(G)
    Glll = G
    T = G
  elseif hard
    Glll, T = lll_gram_with_transform(G, LLLContext(0.99999999999999, 0.500000000001, :gram))
  else
    Glll, T = lll_gram_with_transform(G, LLLContext(0.9999, 0.5001, :gram))
  end

  # We pass d and T to the next level, but it is actually only used for the
  # iterator version the vector version applies the things below before the
  # return.

  if !(S <: Vector)
    V = _short_vectors_gram_nolll_integral(S, Glll, d * lb, d * ub, T, d, U)
  else
    if isone(T)
      V = _short_vectors_gram_nolll_integral(S, Glll, d * lb, d * ub, nothing, d, U)
    else
      V = _short_vectors_gram_nolll_integral(S, Glll, d * lb, d * ub, T, d, U)
    end
  end

  if !(S <: Vector)
    return V
  else
    W = Vector{Tuple{Vector{elem_type}, QQFieldElem}}(undef, length(V))
    for i in 1:length(V)
      W[i] = (V[i][1], V[i][2]//d)
    end
    return W
  end
end

# No assumption on _G, algorithm applies LLL
function _short_vectors_gram(::Type{T}, _G, ub, elem_type::Type{S} = ZZRingElem; hard::Bool = false) where {T, S}
  return _short_vectors_gram(T, _G, ZZRingElem(0), ub, S, hard = hard)
end

################################################################################
#
#  Shortest vectors
#
################################################################################

# No assumption on _G, algorithm applies LLL
function _shortest_vectors_gram(::Type{S}, _G) where {S}
  d = denominator(_G)
  G = change_base_ring(ZZ, d * _G)
  Glll, T = lll_gram_with_transform(G)
  ub = minimum([Glll[i, i] for i in 1:nrows(G)])
  @assert ub > 0
  if isone(T)
    V = _short_vectors_gram_nolll_integral(S, Glll, 0, ub, nothing, one(ZZ), ZZRingElem)
  else
    V = _short_vectors_gram_nolll_integral(S, Glll, 0, ub, T, one(ZZ), ZZRingElem)
  end
  min = minimum(v[2] for v in V)
  return min//d, Vector{ZZRingElem}[ v[1] for v in V if v[2] == min]
end

function _shortest_vectors_gram(_G, elem_type::Type{S} = ZZRingElem) where {S}
  d = denominator(_G)
  G = change_base_ring(ZZ, d * _G)
  Glll, T = lll_gram_with_transform(G)
  ub = minimum([Glll[i, i] for i in 1:nrows(G)])
  V = _short_vectors_gram_nolll_integral(LatEnumCtx, Glll, 0, ub, T, ZZRingElem(1), S)

  cur_min = ub #
  cur_vec = Vector{S}[]

  for (v, l) in V
    if l < cur_min
      empty!(cur_vec)
      push!(cur_vec, v)
      cur_min = l
    elseif l == cur_min
      push!(cur_vec, v)
    end
  end

  min = cur_min//d
  return min, cur_vec
end

function _short_vectors_gram_integral(::Type{S}, _G, ub, elem_type::Type{U} = ZZRingElem; hard = false) where {S, U}
  if hard
    Glll, T = lll_gram_with_transform(_G, LLLContext(0.99999999999999, 0.500000000001, :gram))
  else
    Glll, T = lll_gram_with_transform(_G)
  end
  if S === Vector && isone(T)
    V = _short_vectors_gram_nolll_integral(S, Glll, 0, ub, nothing, one(ZZ), elem_type)
  else
    V = _short_vectors_gram_nolll_integral(S, Glll, 0, ub, T, one(ZZ), elem_type)
  end

  return V
end

function _shortest_vectors_gram_integral(::Type{S}, _G) where {S}
  Glll, T = lll_gram_with_transform(_G)
  max = maximum([Glll[i, i] for i in 1:nrows(Glll)])
  @assert max > 0
  if isone(T)
    V = _short_vectors_gram_nolll_integral(S, Glll, 0, max, nothing, one(ZZ), ZZRingElem)
  else
    V = _short_vectors_gram_nolll_integral(S, Glll, 0, max, T, one(ZZ), ZZRingElem)
  end
  min = minimum(v[2] for v in V)
  return min, [ v for v in V if v[2] == min]
end

_transform(m::ZZMatrix, T::ZZMatrix) = m * T

_transform(m::Vector, ::Nothing) = m

function _transform(m::Vector{Int}, T::ZZMatrix)
  return ZZRingElem.(m) * T
end

function _transform(m::Vector{ZZRingElem}, T::ZZMatrix)
  return m * T
end

################################################################################
#
#  Additional inplace operations
#
################################################################################

@inline function floor!(z::ZZRingElem, y::QQFieldElem, t0::ZZRingElem, t1::ZZRingElem)
  numerator!(t0, y)
  denominator!(t1, y)
  ccall((:fmpz_fdiv_q, libflint), Cvoid, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), z, t0, t1)
  return z
end

@inline function ceil!(z::ZZRingElem, y::QQFieldElem, t0::ZZRingElem, t1::ZZRingElem)
  numerator!(t0, y)
  denominator!(t1, y)
  ccall((:fmpz_cdiv_q, libflint), Cvoid, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), z, t0, t1)
  return z
end

@inline function isqrt!(z::ZZRingElem, a::ZZRingElem)
  ccall((:fmpz_sqrt, libflint), Cvoid, (Ref{ZZRingElem}, Ref{ZZRingElem}), z, a)
  return z
end

floor!(z::Int, x::Rational{Int}, y::Int, w::Int) = Int(floor(x))

isqrt!(z::Int, x::Int) = isqrt(x)

ceil!(z::Int, x::Rational{Int}, y::Int, w::Int) = Int(ceil(x))
