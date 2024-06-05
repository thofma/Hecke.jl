################################################################################
#
#  Line enumeration
#
################################################################################

# We iterate through K by adding 1 in the prime field case and by multiplying
# with a primitive element in the general case.

function LineEnumCtx(K::T, n::Int) where {T}
  a = primitive_element(K)
  v = Vector{elem_type(K)}(undef, n)
  for i in 1:n
    v[i] = zero(K)
  end
  depth = n + 1
  dim = n
  q = order(K)
  length = divexact(BigInt(q)^n - 1, q - 1)
  return LineEnumCtx{T, elem_type(T)}(K, a, dim, depth, v, length)
end

function LineEnumCtx(K::T, n::Int) where {T <: Union{fpField, FpField}}
  a = zero(K)
  v = Vector{elem_type(T)}(undef, n)
  for i in 1:n
    v[i] = zero(K)
  end
  depth = n + 1
  dim = n
  q = order(K)
  length = divexact(BigInt(q)^n - 1, q - 1)
  return LineEnumCtx{T, elem_type(T)}(K, a, dim, depth, v, length)
end

function enumerate_lines(K, n)
  return LineEnumCtx(K, n)
end

function Base.show(io::IO, ::MIME"text/plain", P::LineEnumCtx)
  io = pretty(io)
  println(io, "Iterator for vector lines in a $(dim(P))-dimensional vector space")
  print(io, Indent(), "over ", Lowercase(), P.K)
  print(io, Dedent())
end

function Base.show(io::IO, P::LineEnumCtx)
  if is_terse(io)
    print(io, "Iterator for vector lines")
  else
    io = pretty(io)
    print(io, "Iterator for Gr(1, $(dim(P))) over ")
    print(terse(io), Lowercase(), P.K)
  end
end

Base.length(P::LineEnumCtx) = P.length

Base.eltype(::Type{LineEnumCtx{T, S}}) where {T, S} = Vector{S}

base_field(P::LineEnumCtx) = P.K

depth(P::LineEnumCtx) = P.depth

dim(P::LineEnumCtx) = P.dim

primitive_element(P::LineEnumCtx) = P.a

function Base.rand(P::LineEnumCtx)
  K = base_field(P)
  n = dim(P)
  v = rand(K, n)
  while iszero(v)
    v = rand(K, n)
  end
  j = findfirst(!iszero, v)
  map!(x -> x*inv(v[j]), v, v)
  return v
end

################################################################################
#
#  Iteration
#
################################################################################

# custom iteration
function next(P::LineEnumCtx)
  if depth(P) > 0
    i = dim(P)
    while true
      #@show i, P.v, depth(P)
      if i == depth(P)
        P.v[i] = zero!(P.v[i])
        i = i - 1
      elseif i < depth(P)
        P.depth = i
        if i >= 1
          P.v[i] = one(P.K)
        end
        break
      elseif iszero(P.v[i])
        P.v[i] = one(P.K)
        break
      else
        P.v[i] = P.v[i] * primitive_element(P)
        if isone(P.v[i])
          P.v[i] = zero!(P.v[i])
          i = i - 1
        else
          break
        end
      end
    end
  end
  return P.v
end

function next(P::LineEnumCtx{T, S}) where {T <: Union{fpField, FpField}, S}
  if depth(P) > 0
    i = dim(P)
    while true
      #@show i, P.v, depth(P)
      if i == depth(P)
        P.v[i] = zero!(P.v[i])
        i = i - 1
      elseif i < depth(P)
        P.depth = i
        if i >= 1
          P.v[i] = one(P.K)
        end
        break
      elseif iszero(P.v[i])
        P.v[i] = one(P.K)
        break
      else
        P.v[i] = P.v[i] + 1
        if iszero(P.v[i])
          i = i - 1
        else
          break
        end
      end
    end
  end
  return P.v
end

################################################################################
#
#  Iterator interface
#
################################################################################

function Base.iterate(P::LineEnumCtx)
  P.v[dim(P)] = one(P.K)
  P.depth = dim(P)
  return P.v, one(BigInt)
end

# For prime fields
function Base.iterate(P::LineEnumCtx{T, S}, state) where
                                  {T <: Union{fpField, FpField}, S}
  if state >= P.length
    return nothing
  end

  onee = one(P.K)

  if depth(P) > 0
    i = dim(P)
    while true
      if i == depth(P)
        P.v[i] = zero(P.K)
        i = i - 1
      elseif i < depth(P)
        P.depth = i
        if i >= 1
          P.v[i] = onee
        end
        break
      elseif iszero(P.v[i])
        P.v[i] = onee
        break
      else
        P.v[i] = P.v[i] + 1
        if iszero(P.v[i])
          i = i - 1
        else
          break
        end
      end
    end
  end
  return P.v, inc!(state)
end

# For non-prime fields
function Base.iterate(P::LineEnumCtx, state)
  if state >= P.length
    return nothing
  end

  if depth(P) > 0
    i = dim(P)
    while true
      if i == depth(P)
        P.v[i] = zero!(P.v[i])
        i = i - 1
      elseif i < depth(P)
        P.depth = i
        if i >= 1
          P.v[i] = one(P.K)
        end
        break
      elseif iszero(P.v[i])
        P.v[i] = one(P.K)
        break
      else
        P.v[i] = P.v[i] * primitive_element(P)
        if isone(P.v[i])
          P.v[i] = zero!(P.v[i])
          i = i - 1
        else
          break
        end
      end
    end
  end
  return P.v, inc!(state)
end

################################################################################
#
#  Line orbits
#
################################################################################

line_orbits(G::Vector{fpMatrix}) = _line_orbits(G)

function line_orbits(G::Vector{T}) where {T <: MatElem{FpFieldElem}}
  F = base_ring(G[1])
  p = modulus(F)
  k = nrows(G[1])
  if fits(UInt, p)
    Fsmall = Native.GF(UInt(p), cached = false)
    GG = Vector{dense_matrix_type(Fsmall)}(undef, length(G))
    let Fsmall = Fsmall
      for i in 1:length(G)
        GG[i] = map_entries(x -> Fsmall(x.data), G[i])::dense_matrix_type(Fsmall)
      end
    end
    _res = line_orbits(GG)
    res = Vector{Tuple{Vector{elem_type(F)}, Int}}(undef, length(_res))
    for i in 1:length(_res)
      t = _res[i][1]
      y = Vector{elem_type(F)}(undef, k)
      for j in 1:k
        y[j] = F(t[j].data)
      end
      res[i] = y, _res[i][2]
    end
    return res
  else
    return _line_orbits(G)
  end
end

function line_orbits(G::Vector{fqPolyRepMatrix})
  F = base_ring(G[1])
  d = degree(F)
  k = nrows(G[1])
  if d == 1
    p = characteristic(F)
    @assert fits(UInt, p)
    GFp = Native.GF(UInt(p), cached = false)
    GG = Vector{fpMatrix}(undef, length(G))
    let GFp = GFp
      for i in 1:length(G)
        GG[i] = map_entries(x -> GFp(coeff(x, 0)), G[i])
      end
    end
    _res = line_orbits(GG)
    res = Vector{Tuple{Vector{elem_type(F)}, Int}}(undef, length(_res))
    for i in 1:length(_res)
      t = _res[i][1]
      y = Vector{elem_type(F)}(undef, k)
      for j in 1:k
        y[j] = F(t[j].data)
      end
      res[i] = y, _res[i][2]
    end
    return res
  else
    return _line_orbits(G)
  end
end

function line_orbits(G::Vector{FqPolyRepMatrix})
  F = base_ring(G[1])
  a = gen(F)
  d = degree(F)
  p = characteristic(F)
  k = nrows(G[1])
  if fits(UInt, p)
    f = defining_polynomial(F)
    GFp = Native.GF(UInt(p), cached = false)
    GFpx, x = polynomial_ring(GFp, "x", cached = false)
    local fp
    let GFp = GFp
      fp = map_coefficients(a -> GFp(a.data), f, parent = GFpx)
    end
    FF, aa = Native.finite_field(fp, "aa", cached = false)
    GG = Vector{dense_matrix_type(FF)}(undef, length(G))
    for i in 1:length(G)
      GG[i] = map_entries(b -> sum(coeff(b, i) * aa^i for i in 0:(d-1)), G[i])::dense_matrix_type(FF)
    end
    _res = line_orbits(GG)
    res = Vector{Tuple{Vector{FqPolyRepFieldElem}, Int}}(undef, length(_res))
    for i in 1:length(res)
      t = _res[i][1]
      y = Vector{elem_type(F)}(undef, k)
      for j in 1:k
        y[j] = sum(coeff(t[j], i) * a^i for i in 0:(d - 1))
      end
      res[i] = y, _res[i][2]
    end
    return res
  else
    return _line_orbits(G)
  end
end

function line_orbits(G::Vector{FqMatrix})
  return _line_orbits(G)
end

function _line_orbits(G::Vector)
  K = base_ring(G[1])
  n = nrows(G[1])
  P = enumerate_lines(K, n)
  l = length(P)
  @vprintln :GenRep 1 "Computing orbits of lines of total length $l over $K"
  lines = Vector{eltype(P)}(undef, l)
  i = 1
  for v in P
    lines[i] = deepcopy(v)
    i += 1
  end

  if !(K isa fpField && K isa FpField)
    sort!(lines, lt = _isless)
  end

  res = Tuple{eltype(P), Int}[]

  visited = trues(l)
  sofar = zero(BigInt)
  newline = zero_matrix(K, 1, n)
  newline2 = zero_matrix(K, 1, n)
  ___isless = __isless(elem_type(K)) # the comparison needs some
                                     # temporary variables in some cases
  while sofar < l
    pt = findfirst(visited)
    @assert pt !== nothing
    visited[pt] = false
    norb = 1
    cnd = 1
    orb = Int[pt]
    while cnd <= norb
      set!(newline, lines[orb[cnd]])
      for i in 1:length(G)
        newline2 = mul!(newline2, newline, G[i])
        _normalize!(newline2)
        m = searchsortedfirst(lines, newline2, lt = ___isless)
        @assert m !== nothing
        if visited[m]
          visited[m] = false
          norb += 1
          push!(orb, m)
        end
      end
      cnd += 1
    end
    push!(res, (lines[pt], norb))
    sofar = sofar + norb
  end
  return res
end

################################################################################
#
#  Cheap increment of a BigInt
#
################################################################################

function inc!(a::BigInt)
  ccall((:__gmpz_add_ui, :libgmp), Nothing,
        (Ref{BigInt}, Ref{BigInt}, UInt), a, a, UInt(1))
  return a
end

################################################################################
#
#  Helper functions for sorting and comparing finite field matrices and arrays
#
################################################################################

# gfp
function set!(a::fpMatrix, z::Vector{fpFieldElem})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    Nemo.setindex_raw!(a, z[i].data, 1, i) # no reduction necessary
  end
end

function _normalize!(x::fpMatrix)
  R = base_ring(x)
  @GC.preserve x begin
    piv = 0
    local ell
    for j in 1:ncols(x)
      el = x[1, j]
      if !iszero(el)
        piv = j
        ell = inv(el)
        break
      end
    end

    @assert piv != 0

    for j in (piv+1):ncols(x)
      el = x[j] * ell
      Nemo.setindex_raw!(x, el.data, 1, j)
    end
    Nemo.setindex_raw!(x, UInt(1), 1, piv)
  end
  return x
end

function _isless(x::Vector{fpFieldElem}, y::fpMatrix)
  d = length(x)
  for i in 1:d
    xi = x[i]
    yi = y[1, i]
    if xi.data != yi.data
      return xi.data < yi.data
    end
  end
  return false
end

function _isless(x::Vector{fpFieldElem}, y::Vector{fpFieldElem})
  d = length(x)
  for i in 1:d
    xi = x[i]
    yi = y[i]
    if xi.data != yi.data
      return xi.data < yi.data
    end
  end
  return false
end

# gfp_fmpz

function set!(a::MatElem, z::Vector{FpFieldElem})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    a[1, i] = z[i]
  end
end

function _normalize!(x::MatElem{FpFieldElem})
  R = base_ring(x)
  @GC.preserve x begin
    piv = 0
    local ell
    for j in 1:ncols(x)
      el = x[1, j]
      if !iszero(el)
        piv = j
        ell = inv(el)
        break
      end
    end

    @assert piv != 0

    for j in (piv+1):ncols(x)
      t = x[1, j]
      mul!(t, t, ell)
    end
    one!(x[1, piv].data)
  end
  return x
end

function _isless(x::Vector{FpFieldElem}, y::MatElem)
  d = length(x)
  for i in 1:d
    xi = x[i]
    yi = y[1, i]
    if xi.data != yi.data
      return xi.data < yi.data
    end
  end
  return false
end

function _isless(x::Vector{FpFieldElem}, y::Vector{FpFieldElem})
  d = length(x)
  for i in 1:d
    xi = x[i]
    yi = y[i]
    if xi.data != yi.data
      return xi.data < yi.data
    end
  end
  return false
end

# fqPolyRepMatrix
function set!(a::fqPolyRepMatrix, z::Vector{fqPolyRepFieldElem})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    ccall((:fq_nmod_mat_entry_set, libflint), Nothing,
          (Ref{fqPolyRepMatrix}, Int, Int, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}),
          a, 0, i - 1, z[i], base_ring(a))
  end
end

function _isequal(x::fqPolyRepMatrix, y::Vector{fqPolyRepFieldElem})
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:length(y)
      el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fqPolyRepFieldElem}, (Ref{fqPolyRepMatrix}, Int, Int), x, 0, i - 1)
      b = ccall((:fq_nmod_equal, libflint), Cint, (Ref{fqPolyRepFieldElem}, Ptr{fqPolyRepFieldElem}, Ref{fqPolyRepField}), y[i], el, R)
      bb = Bool(b)
      if !bb
        return false
      end
    end
  end
  return true
end

function _muleq!(x::fqPolyRepMatrix, y::fqPolyRepFieldElem)
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:nrows(x)
      for j in 1:ncols(x)
        el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fqPolyRepFieldElem}, (Ref{fqPolyRepMatrix}, Int, Int), x, i - 1, j - 1)
        ccall((:fq_nmod_mul, libflint), Cvoid, (Ptr{fqPolyRepFieldElem}, Ptr{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), el, el, y, R)
      end
    end
  end
  return x
end

function _normalize!(x::fqPolyRepMatrix)
  R = base_ring(x)
  @GC.preserve x begin
    piv = 0
    local ell
    for j in 1:ncols(x)
      el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fqPolyRepFieldElem}, (Ref{fqPolyRepMatrix}, Int, Int), x, 0, j - 1)
      b = ccall((:fq_nmod_is_zero, libflint), Cint, (Ptr{fqPolyRepFieldElem}, Ref{fqPolyRepField}), el, R)
      if !Bool(b)
        piv = j
        ccall((:fq_nmod_inv, libflint), Cvoid, (Ptr{fqPolyRepFieldElem}, Ptr{fqPolyRepFieldElem}, Ref{fqPolyRepField}), el, el, R)
        ell = el
        break
      end
    end

    @assert piv != 0

    for j in (piv+1):ncols(x)
      el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fqPolyRepFieldElem},
                 (Ref{fqPolyRepMatrix}, Int, Int), x, 0, j - 1)
      ccall((:fq_nmod_mul, libflint), Cvoid,
            (Ptr{fqPolyRepFieldElem}, Ptr{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}),
            el, el, ell, R)
    end
    ccall((:fq_nmod_one, libflint), Cvoid,
          (Ptr{fqPolyRepFieldElem}, Ref{fqPolyRepField}), ell, R)
  end
  return x
end

function _isless(x::fqPolyRepFieldElem, y::fqPolyRepFieldElem)
  d = degree(parent(x)) - 1
  for i in 0:d
    xi = coeff(x, i)
    yi = coeff(y, i)
    if xi != yi
      return xi < yi
    end
  end
  return false
end

@inline function _isless(x::fqPolyRepFieldElem, y::Ptr{fqPolyRepFieldElem})
  d = degree(parent(x)) - 1
  for i in 0:d
    xi = coeff(x, i)
    yi = ccall((:nmod_poly_get_coeff_ui, libflint), UInt,
               (Ptr{fqPolyRepFieldElem}, Int), y, i)
    if xi != yi
      return xi < yi
    end
  end
  return false
end

function _isless(x::Vector{fqPolyRepFieldElem}, y::Vector{fqPolyRepFieldElem})
  d = length(x)
  for i in 1:d
    xi = x[i]
    yi = y[i]
    if xi != yi
      return _isless(xi, yi)
    end
  end
  return false
end

function _isless(x::Vector{fqPolyRepFieldElem}, y::fqPolyRepMatrix)
  d = length(x)
  R = base_ring(y)
  @GC.preserve y begin
    for i in 1:d
      xi = x[i]
      el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fqPolyRepFieldElem},
                 (Ref{fqPolyRepMatrix}, Int, Int), y, 0, i - 1)
      b = ccall((:fq_nmod_equal, libflint), Cint,
                (Ref{fqPolyRepFieldElem}, Ptr{fqPolyRepFieldElem}, Ref{fqPolyRepField}), xi, el, R)
      if !Bool(b)
        return _isless(xi, el)
      end
    end
    return false
  end
end

# FqPolyRepFieldElem
function set!(a::FqPolyRepMatrix, z::Vector{FqPolyRepFieldElem})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    ccall((:fq_mat_entry_set, libflint), Nothing,
          (Ref{FqPolyRepMatrix}, Int, Int, Ref{FqPolyRepFieldElem}, Ref{FqPolyRepField}),
          a, 0, i - 1, z[i], base_ring(a))
  end
end

function _isequal(x::FqPolyRepMatrix, y::Vector{FqPolyRepFieldElem})
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:length(y)
      el = ccall((:fq_mat_entry, libflint), Ptr{FqPolyRepFieldElem},
                 (Ref{FqPolyRepMatrix}, Int, Int), x, 0, i - 1)
      b = ccall((:fq_equal, libflint), Cint,
                (Ref{FqPolyRepFieldElem}, Ptr{FqPolyRepFieldElem}, Ref{FqPolyRepField}), y[i], el, R)
      bb = Bool(b)
      if !bb
        return false
      end
    end
  end
  return true
end

function _muleq!(x::FqPolyRepMatrix, y::FqPolyRepFieldElem)
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:nrows(x)
      for j in 1:ncols(x)
        el = ccall((:fq_mat_entry, libflint), Ptr{FqPolyRepFieldElem},
                   (Ref{FqPolyRepMatrix}, Int, Int), x, i - 1, j - 1)
        ccall((:fq_mul, libflint), Cvoid,
              (Ptr{FqPolyRepFieldElem}, Ptr{FqPolyRepFieldElem}, Ref{FqPolyRepFieldElem}, Ref{FqPolyRepField}), el, el, y, R)
      end
    end
  end
  return x
end

function _normalize!(x::FqPolyRepMatrix)
  R = base_ring(x)
  @GC.preserve x begin
    piv = 0
    local ell
    for j in 1:ncols(x)
      el = ccall((:fq_mat_entry, libflint), Ptr{FqPolyRepFieldElem},
                 (Ref{FqPolyRepMatrix}, Int, Int), x, 0, j - 1)
      b = ccall((:fq_is_zero, libflint), Cint,
                (Ptr{FqPolyRepFieldElem}, Ref{FqPolyRepField}), el, R)
      if !Bool(b)
        piv = j
        ccall((:fq_inv, libflint), Cvoid,
              (Ptr{FqPolyRepFieldElem}, Ptr{FqPolyRepFieldElem}, Ref{FqPolyRepField}), el, el, R)
        ell = el
        break
      end
    end

    @assert piv != 0

    for j in (piv+1):ncols(x)
      el = ccall((:fq_mat_entry, libflint), Ptr{FqPolyRepFieldElem},
                 (Ref{FqPolyRepMatrix}, Int, Int), x, 0, j - 1)
      ccall((:fq_mul, libflint), Cvoid,
            (Ptr{FqPolyRepFieldElem}, Ptr{FqPolyRepFieldElem}, Ref{FqPolyRepFieldElem}, Ref{FqPolyRepField}), el, el, ell, R)
    end
    ccall((:fq_one, libflint), Cvoid, (Ptr{FqPolyRepFieldElem}, Ref{FqPolyRepField}), ell, R)
  end
  return x
end

function _isless(x::FqPolyRepFieldElem, y::FqPolyRepFieldElem, xi::ZZRingElem = ZZRingElem(), yi::ZZRingElem = ZZRingElem())
  d = degree(parent(x)) - 1
  for i in 0:d
    ccall((:fmpz_poly_get_coeff_fmpz, libflint), Cvoid,
          (Ref{ZZRingElem}, Ref{FqPolyRepFieldElem}, Int), xi, x, i)
    ccall((:fmpz_poly_get_coeff_fmpz, libflint), Cvoid,
          (Ref{ZZRingElem}, Ref{FqPolyRepFieldElem}, Int), yi, y, i)
    if xi != yi
      return xi < yi
    end
  end
  return false
end

@inline function _isless(x::FqPolyRepFieldElem, y::Ptr{FqPolyRepFieldElem}, xi::ZZRingElem = ZZRingElem(),
                                            yi::ZZRingElem = ZZRingElem())
  d = degree(parent(x)) - 1
  for i in 0:d
    ccall((:fmpz_poly_get_coeff_fmpz, libflint), Cvoid,
          (Ref{ZZRingElem}, Ref{FqPolyRepFieldElem}, Int), xi, x, i)
    ccall((:fmpz_poly_get_coeff_fmpz, libflint), Cvoid,
          (Ref{ZZRingElem}, Ptr{FqPolyRepFieldElem}, Int), yi, y, i)
    if xi != yi
      return xi < yi
    end
  end
  return false
end

function _isless(x::Vector{FqPolyRepFieldElem}, y::Vector{FqPolyRepFieldElem}, tx::ZZRingElem = ZZRingElem(),
                                               ty::ZZRingElem = ZZRingElem())
  d = length(x)
  for i in 1:d
    xi = x[i]
    yi = y[i]
    if xi != yi
      return _isless(xi, yi, tx, ty)
    end
  end
  return false
end

function _isless(x::Vector{FqPolyRepFieldElem}, y::FqPolyRepMatrix, tx::ZZRingElem = ZZRingElem(), ty::ZZRingElem = ZZRingElem())
  d = length(x)
  R = base_ring(y)
  @GC.preserve y begin
    for i in 1:d
      xi = x[i]
      el = ccall((:fq_mat_entry, libflint), Ptr{FqPolyRepFieldElem},
                 (Ref{FqPolyRepMatrix}, Int, Int), y, 0, i - 1)
      b = ccall((:fq_equal, libflint), Cint,
                (Ref{FqPolyRepFieldElem}, Ptr{FqPolyRepFieldElem}, Ref{FqPolyRepField}), xi, el, R)
      if !Bool(b)
        return _isless(xi, el, tx, ty)
      end
    end
    return false
  end
end

# In some cases the _isless needs some temporary variables

function __isless(::Type{FqPolyRepFieldElem})
  t1, t2 = ZZRingElem(), ZZRingElem()
  return (x, y) -> _isless(x, y, t1, t2)
end

# FqFieldElem
function set!(a::FqMatrix, z::Vector{FqFieldElem})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    ccall((:fq_default_mat_entry_set, libflint), Nothing,
          (Ref{FqMatrix}, Int, Int, Ref{FqFieldElem}, Ref{FqField}),
          a, 0, i - 1, z[i], base_ring(a))
  end
end

function _isequal(x::FqMatrix, y::Vector{FqFieldElem})
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:length(y)
      el = ccall((:fq_mat_entry, libflint), Ptr{FqFieldElem},
                 (Ref{FqMatrix}, Int, Int), x, 0, i - 1)
      b = ccall((:fq_default_equal, libflint), Cint,
                (Ref{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqField}), y[i], el, R)
      bb = Bool(b)
      if !bb
        return false
      end
    end
  end
  return true
end

function _muleq!(x::FqMatrix, y::FqFieldElem)
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:nrows(x)
      for j in 1:ncols(x)
        el = Nemo.fq_default_mat_entry_ptr(x, i, j)
        ccall((:fq_default_mul, libflint), Cvoid,
              (Ptr{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqFieldElem}, Ref{FqField}), el, el, y, R)
      end
    end
  end
  return x
end

function _normalize!(x::FqMatrix)
  R = base_ring(x)
  piv = 0
  local ell
  @GC.preserve x begin
    for j in 1:ncols(x)
      el = Nemo.fq_default_mat_entry_ptr(x, 1, j)
      b = ccall((:fq_default_is_zero, libflint), Cint,
                (Ptr{FqFieldElem}, Ref{FqField}), el, R)
      if !Bool(b)
        piv = j
        ccall((:fq_default_inv, libflint), Cvoid,
              (Ptr{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqField}), el, el, R)
        ell = el
        break
      end
    end

    @assert piv != 0

    for j in (piv+1):ncols(x)
      el = Nemo.fq_default_mat_entry_ptr(x, 1, j)
      ccall((:fq_default_mul, libflint), Cvoid,
            (Ptr{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqFieldElem}, Ref{FqField}), el, el, ell, R)
    end
    ccall((:fq_default_one, libflint), Cvoid, (Ptr{FqFieldElem}, Ref{FqField}), ell, R)
  end
  return x
end

function _isless(x::FqFieldElem, y::FqFieldElem, xi::ZZRingElem = ZZRingElem(), yi::ZZRingElem = ZZRingElem())
  d = absolute_degree(parent(x)) - 1
  for i in 0:d
    ccall((:fq_default_get_coeff_fmpz, libflint), Cvoid,
          (Ref{ZZRingElem}, Ref{FqFieldElem}, Int, Ref{FqField}), xi, x, i, parent(x))
    ccall((:fq_default_get_coeff_fmpz, libflint), Cvoid,
          (Ref{ZZRingElem}, Ref{FqFieldElem}, Int, Ref{FqField}), yi, y, i, parent(x))
    if xi != yi
      return xi < yi
    end
  end
  return false
end

@inline function _isless(x::FqFieldElem, y::Ptr{FqFieldElem}, xi::ZZRingElem = ZZRingElem(),
                                            yi::ZZRingElem = ZZRingElem())
  R = parent(x)
  d = degree(parent(x)) - 1
  for i in 0:d
    ccall((:fq_default_get_coeff_fmpz, libflint), Cvoid,
          (Ref{ZZRingElem}, Ref{FqFieldElem}, Int, Ref{FqField}), xi, x, i, R)
    ccall((:fq_default_get_coeff_fmpz, libflint), Cvoid,
          (Ref{ZZRingElem}, Ptr{FqFieldElem}, Int, Ref{FqField}), yi, y, i, R)
    if xi != yi
      return xi < yi
    end
  end
  return false
end

function _isless(x::Vector{FqFieldElem}, y::Vector{FqFieldElem}, tx::ZZRingElem = ZZRingElem(),
                                               ty::ZZRingElem = ZZRingElem())
  d = length(x)
  for i in 1:d
    xi = x[i]
    yi = y[i]
    if xi != yi
      return _isless(xi, yi, tx, ty)
    end
  end
  return false
end

function _isless(x::Vector{FqFieldElem}, y::FqMatrix, tx::ZZRingElem = ZZRingElem(), ty::ZZRingElem = ZZRingElem())
  d = length(x)
  R = base_ring(y)
  @GC.preserve y begin
    for i in 1:d
      xi = x[i]
      el = Nemo.fq_default_mat_entry_ptr(y, 1, i)
      #el = ccall((:fq_default_mat_entry, libflint), Ptr{FqFieldElem},
      #           (Ref{FqMatrix}, Int, Int), y, 0, i - 1)
      b = ccall((:fq_default_equal, libflint), Cint,
                (Ref{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqField}), xi, el, R)
      if !Bool(b)
        return _isless(xi, el, tx, ty)
      end
    end
    return false
  end
end

# In some cases the _isless needs some temporary variables

function __isless(::Type{FqFieldElem})
  t1, t2 = ZZRingElem(), ZZRingElem()
  return (x, y) -> _isless(x, y, t1, t2)
end

__isless(::Type{T}) where {T} = _isless
