################################################################################
#
#  Line enumeration
#
################################################################################

# Iterate over the lines in K^n, that is, over the points of projective
# space P^(n-1)(K).
#
# Important: In the prime case, this must always be lexicographically ordered

mutable struct LineEnumCtx{T, S}
  K::T
  a::S # primitive element
  dim::Int
  depth::Int
  v::Vector{S}
  length::BigInt
end

# We iterate through K by adding 1 in the prime field case and by multiplying
# with a primitive element in the general case.

function LineEnumCtx(K::T, n) where {T}
  a = _primitive_element(K)
  v = Vector{elem_type(K)}(undef, n)
  for i in 1:n
    v[i] = zero(K)
  end
  depth = n + 1
  dim = n
  q = order(K)
  length = divexact(q^n - 1, q - 1)
  return LineEnumCtx{T, elem_type(T)}(K, a, dim, depth, v, length)
end

function LineEnumCtx(K::T, n::Int) where {T <: Union{GaloisField, GaloisFmpzField}}
  a = zero(K)
  v = Vector{elem_type(T)}(undef, n)
  for i in 1:n
    v[i] = zero(K)
  end
  depth = n + 1
  dim = n
  q = order(K)
  length = divexact(q^n - 1, q - 1)
  return LineEnumCtx{T, elem_type(T)}(K, a, dim, depth, v, length)
end

function enumerate_lines(K, n)
  return LineEnumCtx(K, n)
end

function Base.show(io::IO, P::LineEnumCtx)
  print(io, "Iterator for affine lines in K^n with n = ", dim(P), "\n")
  print(io, "over ", P.K)
end

Base.length(P::LineEnumCtx) = P.length

Base.eltype(::Type{LineEnumCtx{T, S}}) where {T, S} = Vector{S}

depth(P::LineEnumCtx) = P.depth

dim(P::LineEnumCtx) = P.dim

primitive_element(P::LineEnumCtx) = P.a

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
      @show i, P.v, depth(P)
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

function next(P::LineEnumCtx{T, S}) where {T <: Union{GaloisField, GaloisFmpzField}, S}
  if depth(P) > 0
    i = dim(P)
    while true
      @show i, P.v, depth(P)
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
                                  {T <: Union{GaloisField, GaloisFmpzField}, S}
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
#  Primitive elements for prime fields
#
################################################################################

function _primitive_element(R::GaloisField)
  S = ResidueRing(FlintZZ, Int(modulus(R)))
  U, mU = unit_group(S)
  return R(data(mU(U[1])))
end

function _primitive_element(R::GaloisFmpzField)
  S = ResidueRing(FlintZZ, fmpz(modulus(R)))
  U, mU = unit_group(S)
  return R(data(mU(U[1])))
end

################################################################################
#
#  Line orbits
#
################################################################################

line_orbits(G::Vector{gfp_mat}) = _line_orbits(G)

function line_orbits(G::Vector{T}) where {T <: MatElem{gfp_fmpz_elem}}
  F = base_ring(G[1])
  p = modulus(F)
  k = nrows(G[1])
  if fits(UInt, p)
    Fsmall = GF(UInt(p), cached = false)
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

function line_orbits(G::Vector{fq_nmod_mat})
  F = base_ring(G[1])
  d = degree(F)
  k = nrows(G[1])
  if d == 1
    p = characteristic(F)
    @assert fits(UInt, p)
    GFp = GF(UInt(p), cached = false)
    GG = Vector{gfp_mat}(undef, length(G))
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

function line_orbits(G::Vector{fq_mat})
  F = base_ring(G[1])
  a = gen(F)
  d = degree(F)
  p = characteristic(F)
  k = nrows(G[1])
  if fits(UInt, p)
    f = defining_polynomial(F)
    GFp = GF(UInt(p), cached = false)
    GFpx, x = PolynomialRing(GFp, "x", cached = false)
    local fp
    let GFp = GFp
      fp = map_coeffs(a -> GFp(a.data), f, parent = GFpx)
    end
    FF, aa = FlintFiniteField(fp, "aa", cached = false)
    GG = Vector{dense_matrix_type(FF)}(undef, length(G))
    for i in 1:length(G)
      GG[i] = map_entries(b -> sum(coeff(b, i) * aa^i for i in 0:(d-1)), G[i])::dense_matrix_type(FF)
    end
    _res = line_orbits(GG)
    res = Vector{Tuple{Vector{fq}, Int}}(undef, length(_res))
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

function _line_orbits(G::Vector)
  K = base_ring(G[1])
  n = nrows(G[1])
  P = enumerate_lines(K, n)
  l = length(P)
  @vprint :GenRep 1 "Computing orbits of lines of total length $l over $K\n"
  lines = Vector{eltype(P)}(undef, l)
  i = 1
  for v in P
    lines[i] = deepcopy(v)
    i += 1
  end

  if !(K isa GaloisField && K isa GaloisFmpzField)
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
function set!(a::gfp_mat, z::Vector{gfp_elem})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    Nemo.setindex_raw!(a, z[i].data, 1, i) # no reduction necessary
  end
end

function _normalize!(x::gfp_mat)
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

function _isless(x::Vector{gfp_elem}, y::gfp_mat)
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

function _isless(x::Vector{gfp_elem}, y::Vector{gfp_elem})
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

function set!(a::MatElem, z::Vector{gfp_fmpz_elem})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    a[1, i] = z[i]
  end
end

function _normalize!(x::MatElem{gfp_fmpz_elem})
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

function _isless(x::Vector{gfp_fmpz_elem}, y::MatElem)
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

function _isless(x::Vector{gfp_fmpz_elem}, y::Vector{gfp_fmpz_elem})
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

# fq_nmod_mat
function set!(a::fq_nmod_mat, z::Vector{fq_nmod})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    ccall((:fq_nmod_mat_entry_set, libflint), Nothing,
          (Ref{fq_nmod_mat}, Int, Int, Ref{fq_nmod}, Ref{FqNmodFiniteField}),
          a, 0, i - 1, z[i], base_ring(a))
  end
end

function _isequal(x::fq_nmod_mat, y::Vector{fq_nmod})
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:length(y)
      el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fq_nmod}, (Ref{fq_nmod_mat}, Int, Int), x, 0, i - 1)
      b = ccall((:fq_nmod_equal, libflint), Cint, (Ref{fq_nmod}, Ptr{fq_nmod}, Ref{FqNmodFiniteField}), y[i], el, R)
      bb = Bool(b)
      if !bb
        return false
      end
    end
  end
  return true
end

function _muleq!(x::fq_nmod_mat, y::fq_nmod)
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:nrows(x)
      for j in 1:ncols(x)
        el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fq_nmod}, (Ref{fq_nmod_mat}, Int, Int), x, i - 1, j - 1)
        ccall((:fq_nmod_mul, libflint), Cvoid, (Ptr{fq_nmod}, Ptr{fq_nmod}, Ref{fq_nmod}, Ref{FqNmodFiniteField}), el, el, y, R)
      end
    end
  end
  return x
end

function _normalize!(x::fq_nmod_mat)
  R = base_ring(x)
  @GC.preserve x begin
    piv = 0
    local ell
    for j in 1:ncols(x)
      el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fq_nmod}, (Ref{fq_nmod_mat}, Int, Int), x, 0, j - 1)
      b = ccall((:fq_nmod_is_zero, libflint), Cint, (Ptr{fq_nmod}, Ref{FqNmodFiniteField}), el, R)
      if !Bool(b)
        piv = j
        ccall((:fq_nmod_inv, libflint), Cvoid, (Ptr{fq_nmod}, Ptr{fq_nmod}, Ref{FqNmodFiniteField}), el, el, R)
        ell = el
        break
      end
    end

    @assert piv != 0
    
    for j in (piv+1):ncols(x)
      el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fq_nmod},
                 (Ref{fq_nmod_mat}, Int, Int), x, 0, j - 1)
      ccall((:fq_nmod_mul, libflint), Cvoid,
            (Ptr{fq_nmod}, Ptr{fq_nmod}, Ref{fq_nmod}, Ref{FqNmodFiniteField}),
            el, el, ell, R)
    end
    ccall((:fq_nmod_one, libflint), Cvoid,
          (Ptr{fq_nmod}, Ref{FqNmodFiniteField}), ell, R)
  end
  return x
end

function _isless(x::fq_nmod, y::fq_nmod)
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

@inline function _isless(x::fq_nmod, y::Ptr{fq_nmod})
  d = degree(parent(x)) - 1
  for i in 0:d
    xi = coeff(x, i)
    yi = ccall((:nmod_poly_get_coeff_ui, libflint), UInt,
               (Ptr{fq_nmod}, Int), y, i)
    if xi != yi
      return xi < yi
    end
  end
  return false
end

function _isless(x::Vector{fq_nmod}, y::Vector{fq_nmod})
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

function _isless(x::Vector{fq_nmod}, y::fq_nmod_mat)
  d = length(x)
  R = base_ring(y)
  @GC.preserve y begin
    for i in 1:d
      xi = x[i]
      el = ccall((:fq_nmod_mat_entry, libflint), Ptr{fq_nmod},
                 (Ref{fq_nmod_mat}, Int, Int), y, 0, i - 1)
      b = ccall((:fq_nmod_equal, libflint), Cint,
                (Ref{fq_nmod}, Ptr{fq_nmod}, Ref{FqNmodFiniteField}), xi, el, R)
      if !Bool(b)
        return _isless(xi, el)
      end
    end
    return false
  end
end


# fq
function set!(a::fq_mat, z::Vector{fq})
  @assert ncols(a) == length(z)
  for i in 1:length(z)
    ccall((:fq_mat_entry_set, libflint), Nothing,
          (Ref{fq_mat}, Int, Int, Ref{fq}, Ref{FqFiniteField}),
          a, 0, i - 1, z[i], base_ring(a))
  end
end

function _isequal(x::fq_mat, y::Vector{fq})
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:length(y)
      el = ccall((:fq_mat_entry, libflint), Ptr{fq},
                 (Ref{fq_mat}, Int, Int), x, 0, i - 1)
      b = ccall((:fq_equal, libflint), Cint,
                (Ref{fq}, Ptr{fq}, Ref{FqFiniteField}), y[i], el, R)
      bb = Bool(b)
      if !bb
        return false
      end
    end
  end
  return true
end

function _muleq!(x::fq_mat, y::fq)
  R = base_ring(x)
  @GC.preserve x begin
    for i in 1:nrows(x)
      for j in 1:ncols(x)
        el = ccall((:fq_mat_entry, libflint), Ptr{fq},
                   (Ref{fq_mat}, Int, Int), x, i - 1, j - 1)
        ccall((:fq_mul, libflint), Cvoid,
              (Ptr{fq}, Ptr{fq}, Ref{fq}, Ref{FqFiniteField}), el, el, y, R)
      end
    end
  end
  return x
end

function _normalize!(x::fq_mat)
  R = base_ring(x)
  @GC.preserve x begin
    piv = 0
    local ell
    for j in 1:ncols(x)
      el = ccall((:fq_mat_entry, libflint), Ptr{fq},
                 (Ref{fq_mat}, Int, Int), x, 0, j - 1)
      b = ccall((:fq_is_zero, libflint), Cint,
                (Ptr{fq}, Ref{FqFiniteField}), el, R)
      if !Bool(b)
        piv = j
        ccall((:fq_inv, libflint), Cvoid,
              (Ptr{fq}, Ptr{fq}, Ref{FqFiniteField}), el, el, R)
        ell = el
        break
      end
    end

    @assert piv != 0
    
    for j in (piv+1):ncols(x)
      el = ccall((:fq_mat_entry, libflint), Ptr{fq},
                 (Ref{fq_mat}, Int, Int), x, 0, j - 1)
      ccall((:fq_mul, libflint), Cvoid,
            (Ptr{fq}, Ptr{fq}, Ref{fq}, Ref{FqFiniteField}), el, el, ell, R)
    end
    ccall((:fq_one, libflint), Cvoid, (Ptr{fq}, Ref{FqFiniteField}), ell, R)
  end
  return x
end

function _isless(x::fq, y::fq, xi::fmpz = fmpz(), yi::fmpz = fmpz())
  d = degree(parent(x)) - 1
  for i in 0:d
    ccall((:fmpz_poly_get_coeff_fmpz, libflint), Cvoid,
          (Ref{fmpz}, Ref{fq}, Int), xi, x, i)
    ccall((:fmpz_poly_get_coeff_fmpz, libflint), Cvoid,
          (Ref{fmpz}, Ref{fq}, Int), yi, y, i)
    if xi != yi
      return xi < yi
    end
  end
  return false
end

@inline function _isless(x::fq, y::Ptr{fq}, xi::fmpz = fmpz(),
                                            yi::fmpz = fmpz())
  d = degree(parent(x)) - 1
  for i in 0:d
    ccall((:fmpz_poly_get_coeff_fmpz, libflint), Cvoid,
          (Ref{fmpz}, Ref{fq}, Int), xi, x, i)
    ccall((:fmpz_poly_get_coeff_fmpz, libflint), Cvoid,
          (Ref{fmpz}, Ptr{fq}, Int), yi, y, i)
    if xi != yi
      return xi < yi
    end
  end
  return false
end

function _isless(x::Vector{fq}, y::Vector{fq}, tx::fmpz = fmpz(),
                                               ty::fmpz = fmpz())
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

function _isless(x::Vector{fq}, y::fq_mat, tx::fmpz = fmpz(), ty::fmpz = fmpz())
  d = length(x)
  R = base_ring(y)
  @GC.preserve y begin
    for i in 1:d
      xi = x[i]
      el = ccall((:fq_mat_entry, libflint), Ptr{fq},
                 (Ref{fq_mat}, Int, Int), y, 0, i - 1)
      b = ccall((:fq_equal, libflint), Cint,
                (Ref{fq}, Ptr{fq}, Ref{FqFiniteField}), xi, el, R)
      if !Bool(b)
        return _isless(xi, el, tx, ty)
      end
    end
    return false
  end
end

# In some cases the _isless needs some temporary variables

function __isless(::Type{fq})
  t1, t2 = fmpz(), fmpz()
  return (x, y) -> _isless(x, y, t1, t2)
end

__isless(::Type{T}) where {T} = _isless

################################################################################
#
#  Defining polynomial for finite fields
#
################################################################################

defining_polynomial(F::FqFiniteField) = minpoly(gen(F))
