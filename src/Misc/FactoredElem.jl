################################################################################
#
#  Insert in a dictionary
#
################################################################################

function add_to_key!(D::Dict{S, T}, k::S, v; remove_zero::Bool = true) where S where T <: IntegerUnion
  add_to_key!(D, k, T(v), remove_zero = remove_zero)
  return nothing
end

if VERSION >= v"1.9.0-DEV.215"
  function add_to_key!(D::Dict{S, T}, k::S, v::T; remove_zero::Bool = true) where S where T <: IntegerUnion
    hash_k, sh = Base.ht_keyindex2_shorthash!(D, k)
    if hash_k > 0
      D.age += 1
      #The key is in the dictionary, we only need to add
      w = D.vals[hash_k]
      if remove_zero
        if w != v && iszero(cmpabs(w, v))
          Base._delete!(D, hash_k)
        else
          @inbounds D.vals[hash_k] = w + v
        end
      else
        @inbounds Base._setindex!(D, w + v, k, -hash_k, sh)
      end
    else
      @inbounds Base._setindex!(D, v, k, -hash_k, sh)
    end
    return nothing
  end
else
  function add_to_key!(D::Dict{S, T}, k::S, v::T; remove_zero::Bool = true) where S where T <: IntegerUnion
    hash_k = Base.ht_keyindex2!(D, k)
    if hash_k > 0
      #The key is in the dictionary, we only need to add
      w = D.vals[hash_k]
      if remove_zero
        if w != v && iszero(cmpabs(w, v))
          Base._delete!(D, hash_k)
        else
          @inbounds D.vals[hash_k] = w + v
        end
      else
        @inbounds D.vals[hash_k] = w + v
      end
    else
      pos = -hash_k
      @inbounds D.slots[pos] = 0x1
      @inbounds D.keys[pos] = k
      @inbounds D.vals[pos] = v
      D.count += 1
      if pos < D.idxfloor
        D.idxfloor = pos
      end
    end
    D.age += 1
    return nothing
  end
end


################################################################################
#
#  Multiplicative representation
#
################################################################################

# abstract nonsense

const FacElemMonDict = AbstractAlgebra.CacheDictType{Ring, FacElemMon}()

function (x::FacElemMon{S})() where S
  z = FacElem{elem_type(S), S}()
  z.fac = Dict{elem_type(S), ZZRingElem}()
  z.parent = x
  return z
end

@doc raw"""
    FacElem{B}(R, base::Vector{B}, exp::Vector{ZZRingElem}) -> FacElem{B}

Returns the element $\prod b_i^{e_i}$, un-expanded.
"""
function FacElem(R, base::Vector{B}, exp::Vector{ZZRingElem}; parent = FacElemMon(R)) where {B}
  if elem_type(R) !== B
    throw(ArgumentError("Parent of elements wrong."))
  end

  length(base) != length(exp) && error("not the same length")

  z = FacElem{B, typeof(R)}()

  for i in 1:length(base)
    if iszero(exp[i])
      continue
    end
    add_to_key!(z.fac, base[i], exp[i], remove_zero = true)
  end

  z.parent = parent
  return z
end

@doc raw"""
    FacElem{B}(base::Vector{B}, exp::Vector{ZZRingElem}) -> FacElem{B}

Returns the element $\prod b_i^{e_i}$, un-expanded.
"""
function FacElem(base::Vector{B}, exp::Vector{ZZRingElem}) where B

  length(base) == 0 && error("Array must not be empty")

  R = parent(base[1])

  return FacElem(R, base, exp)
end

@doc raw"""
    FacElem{B}(R, d::Dict{B, ZZRingElem}) -> FacElem{B}
    FacElem{B}(R, d::Dict{B, Integer}) -> FacElem{B}

Returns the element $\prod b^{d[p]}$, un-expanded.
"""
function FacElem(R, d::Dict{B, ZZRingElem}) where B
  if elem_type(R) !== B
    throw(ArgumentError("Parent of elements wrong."))
  end

  z = FacElem{B, typeof(R)}()
  z.fac = d
  z.parent = FacElemMon(R)
  return z
end

@doc raw"""
    FacElem{B}(d::Dict{B, ZZRingElem}) -> FacElem{B}
    FacElem{B}(d::Dict{B, Integer}) -> FacElem{B}

Returns the element $\prod b^{d[p]}$, un-expanded.
"""
function FacElem(d::Dict{B, ZZRingElem}) where B

  length(d) == 0 && error("Dictionary must not be empty")

  R = parent(first(keys(d)))

  return FacElem(R, d)
end

function FacElem(R::Ring)
  z = FacElem{elem_type(R), typeof(R)}()
  z.fac = Dict{elem_type(R), ZZRingElem}()
  z.parent = FacElemMon(R)
  return z
end

function FacElem(R, d::Dict{B, T}) where {B, T <: Integer}

  z = FacElem{B, typeof(R)}()
  z.fac = Dict{B, ZZRingElem}((k,ZZRingElem(v)) for (k,v) = d)

  z.parent = FacElemMon(R)
  return z
end

function FacElem(d::Dict{B, T}) where {B, T <: Integer}

  length(d) == 0 && error("Dictionary must not be empty")

  R = parent(first(keys(d)))

  return FacElem(R, d)
end

parent(x::FacElem) = x.parent

base_ring(x::FacElemMon) = x.base_ring

base_ring(x::FacElem) = base_ring(parent(x))

base(x::FacElem) = keys(x.fac)

function Base.deepcopy_internal(x::FacElem{B, S}, dict::IdDict) where {B, S}
  z = FacElem{B, S}()
  z.fac = Base.deepcopy_internal(x.fac, dict)
  if isdefined(x, :parent)
    z.parent = x.parent
  end
#  z.hash = x.hash # this needs to be deleted in ! operations
  return z
end

function Base.copy(x::FacElem{B, S}) where {B, S}
  z = FacElem{B, S}()
  z.fac = Base.copy(x.fac)
  if isdefined(x, :parent)
    z.parent = x.parent
  end
#  z.hash = x.hash
  return z
end

Base.iterate(a::FacElem) = Base.iterate(a.fac)

Base.iterate(a::FacElem, state) = Base.iterate(a.fac, state)

Base.length(a::FacElem) = Base.length(a.fac)

Base.eltype(a::Type{FacElem{S, T}}) where {S, T} = Pair{S, ZZRingElem}

check_parent(x::FacElem{S, T}, y::FacElem{S, T}) where { S, T } = base_ring(x) == base_ring(y)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::FacElemMon)
  print(io, "Factored elements over $(x.base_ring)")
end

function AbstractAlgebra.expressify(x::FacElem; context=nothing)
  if length(x.fac) == 0
    return Expr(:1)
  end
  prod = Expr(:call, :*)
  for (k,v) = x.fac
    push!(prod.args, Expr(:call, :^, AbstractAlgebra.expressify(k, context=context), v))
  end
  return prod
end

@enable_all_show_via_expressify FacElem

################################################################################
#
#  Inverse
#
################################################################################
function inv!(x::FacElem)
  for i = x.fac.idxfloor:length(x.fac.vals)
    if isassigned(x.fac.vals, i)
      x.fac.vals[i] = -x.fac.vals[i]
    end
  end
  return x
end

function inv(x::FacElem)
  y = copy(x)
  inv!(y)
  return y
end

################################################################################
#
#  Exponentiation
#
################################################################################

function pow!(z::FacElem, x::FacElem, y::T) where T <: IntegerUnion
  z.fac = copy(x.fac)
  for i = z.fac.idxfloor:length(z.fac.vals)
    if isassigned(z.fac.vals, i)
      z.fac.vals[i] = z.fac.vals[i]*y
    end
  end
  return nothing
end

function pow!(z::FacElem, y::T) where T <: IntegerUnion
  for i = z.fac.idxfloor:length(z.fac.vals)
    if isassigned(z.fac.vals, i)
      z.fac.vals[i] = z.fac.vals[i]*y
    end
  end
end

# ^(x::FacElem, y::IntegerUnion) is ambiguous
for T in [:Integer, ZZRingElem]
  @eval begin
    function ^(x::FacElem, y::($T))
      z = parent(x)()
      if y == 0
        return z
      end
      if y == 1
        return copy(x)
      else
        z.fac = copy(x.fac)
        for i = z.fac.idxfloor:length(z.fac.vals)
          if isassigned(z.fac.vals, i)
            z.fac.vals[i] = z.fac.vals[i]*y
          end
        end
        return z
      end
    end
  end
end

################################################################################
#
#  Multiplication
#
################################################################################

function mul!(z::FacElem{B, S}, x::FacElem{B, S}, y::FacElem{B, S}) where {B, S}
  @assert check_parent(x, y) "Elements must have the same parent"
  @assert check_parent(x, z) "Elements must have the same parent"
  z.fac = copy(x.fac)
  for (a, v) in y
    add_to_key!(z.fac, a, v, remove_zero = true)
  end
  return z
end

function *(x::FacElem{B, S}, y::FacElem{B, S}) where {B, S}
  @assert check_parent(x, y) "Elements must have the same parent"
  if length(x.fac) == 0
    return copy(y)
  end

  if length(y.fac) == 0
    return copy(x)
  end

  z = copy(x)
  for (a, v) in y
    add_to_key!(z.fac, a, v, remove_zero = true)
  end

  return z
end

function *(x::FacElem{B}, y::B) where B
  @assert base_ring(x) == parent(y)
  z = copy(x)
  add_to_key!(z.fac, y, 1, remove_zero = true)
  return z
end

function *(y::B, x::FacElem{B}) where B
  @assert base_ring(x) == parent(y)
  z = copy(x)
  add_to_key!(z.fac, y, 1, remove_zero = true)
  return z
end

function div(x::FacElem{B}, y::FacElem{B}) where B
  @assert check_parent(x, y) "Elements must have the same parent"
  z = copy(x)
  for (a, v) in y
    add_to_key!(z.fac, a, -v, remove_zero = true)
  end
  return z
end

################################################################################
#
#  Apply transformation
#
################################################################################

# return (x1,...,xr)*y
function _transform(x::Vector{FacElem{T, S}}, y::ZZMatrix) where {T, S}
  length(x) != nrows(y) &&
              error("Length of array must be number of rows of matrix")

  z = Array{FacElem{T, S}}(undef, ncols(y))

  t = parent(x[1])()

  for i in 1:ncols(y)
    z[i] = x[1]^y[1,i]
    for j in 2:nrows(y)
       if iszero(y[j, i])
        continue
      end
      if isone(y[j, i])
        mul!(z[i], z[i], x[j])
      else
        pow!(t, x[j], y[j, i])
        mul!(z[i], z[i], t)
      end
    end
  end
  return z
end

function transform(x::Vector{FacElem{S, T}}, y::ZZMatrix) where {S, T}
  return _transform(x, y)
end

function transform_left!(x::Vector{FacElem{S, T}}, y::TrafoSwap{ZZRingElem}) where {S, T}
  x[y.i], x[y.j] = x[y.j], x[y.i]
  nothing
end

function transform_left!(x::Vector{FacElem{S, T}}, y::TrafoAddScaled{ZZRingElem}) where {S, T}
  x[y.j] = x[y.j] * x[y.i]^y.s
  nothing
end

function transform_left!(x::Vector{FacElem{S, T}}, y::TrafoPartialDense{R}) where {S, T, R}
  z = view(deepcopy(x), y.rows)
  xx = view(x, y.rows)
  for i in 1:nrows(y.U)
    xx[i] = z[1]^Int(y.U[i, 1])
    for j in 2:ncols(y.U)
      xx[i] *= z[j]^Int(y.U[i, j])
    end
  end
end

function transform_left!(x::Vector{T}, t::TrafoDeleteZero{S}) where {S, T}
  # move ith position to the back
  for j in t.i:length(x)-1
    r = x[j]
    x[j] = x[j + 1]
    x[j + 1] = r
  end
end

function transform_left!(x::Vector{FacElem{S, T}}, y::TrafoParaAddScaled{R}) where {S, T, R}
  # [ Ri; Rj] <- [a b; c d]* [ Ri; Rj ]
  ri = deepcopy(x[y.i])
  rj = deepcopy(x[y.j])
  x[y.i] = ri^y.a * rj^y.b
  x[y.j] = ri^y.c * rj^y.d
end

################################################################################
#
#  Evaluate
#
################################################################################

function evaluate(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}; coprime::Bool = false)
  O = order(base_ring(x))
  if !coprime
    x = simplify(x) # the other method won't work due to one()
  end
  if length(x.fac)==0
    return fractional_ideal(O, O(1))
  end
  # still doesn't work
  D = collect(x.fac)
  A = (D[1][1]//1)^Int(D[1][2])
  for i in 2:length(D)
    A = A * (D[i][1]//1)^Int(D[i][2])
  end
  return A
end

function _ev(d::Dict{AbsSimpleNumFieldElem, ZZRingElem}, oe::AbsSimpleNumFieldElem)
  z = deepcopy(oe)
  if length(d)==0
    return z
  elseif length(d)==1
    x = first(d)
    return x[1]^x[2]
  end
  b = empty(d)
  for (k, v) in d
    if iszero(v)
      continue
    end
    if v>-10 && v<10
      mul!(z, z, k^Int(v))
    else
      r = isodd(v) ? 1 : 0
      vv = div(v-r, 2)
      if vv != 0
        b[k] = vv
      end
      if r != 0
        mul!(z, z, k)
      end
    end
  end
  if isempty(b)
    return z
  end
  res = _ev(b, oe)
  mul!(res, res, res)
  mul!(z, z, res)
  return z
end

function _ev(d::Dict{fqPolyRepFieldElem, ZZRingElem}, z::fqPolyRepFieldElem)
  Fq = parent(z)
  if length(d) == 0
    return z
  elseif length(d)==1
    x = first(d)
    return x[1]^Int(x[2])
  end
  b = empty(d)
  for (k, v) in d
    if iszero(v)
      continue
    end
    if abs(v) < 10
      if v >0
        kv = Fq()
        ccall((:fq_nmod_pow, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{ZZRingElem}, Ref{fqPolyRepField}), kv, k, v, Fq)
        mul!(z, z, kv)
      else
        kv = Fq()
        ccall((:fq_nmod_inv, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), kv, k, Fq)
        ccall((:fq_nmod_pow, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{ZZRingElem}, Ref{fqPolyRepField}), kv, kv, -v, Fq)
        mul!(z, z, kv)
      end
    else
      r = isodd(v) ? 1 : 0
      vv = div(v-r, 2)
      if vv != 0
        b[k] = vv
      end
      if r != 0
        mul!(z, z, k)
      end
    end
  end
  if isempty(b)
    return z
  end
  res = _ev(b, one(Fq))
  mul!(res, res, res)
  mul!(z, z, res)
  return z
end

function _ev(d::Dict{T, ZZRingElem}, oe::T) where T
  if T <: RingElement
    z = deepcopy(oe)
  else # mainly for ideals?
    z = copy(oe)
  end
  if length(d)==0
    return z
  elseif length(d)==1
    x = first(d)
    return x[1]^x[2]
  end
  b = empty(d)
  for (k,v) in d
    if v>-10 && v<10
      z *= k^Int(v)
    else
      r = isodd(v) ? 1 : 0
      vv = div(v-r, 2)
      if vv!=0
        b[k] = vv
      end
      if r!=0
        z*= k
      end
    end
  end
  return _ev(b, oe)^2*z
end


@doc raw"""
    evaluate{T}(x::FacElem{T}) -> T

Expands or evaluates the factored element, i.e. actually computes the
value.
Does "square-and-multiply" on the exponent vectors.
"""
function evaluate(x::FacElem{T}) where T
  return _ev(x.fac, one(base_ring(x)))
end

@doc raw"""
    evaluate_naive{T}(x::FacElem{T}) -> T

Expands or evaluates the factored element, i.e. actually computes the
value. Uses the obvious naive algorithm. Faster for input in finite rings.
"""
function evaluate_naive(x::FacElem{T}) where T
  z = one(base_ring(x))
  d = x.fac
  if length(d)==0
    return z
  end
  for (k,v) in d
    z *= k^v
  end
  return z
end

#################################################################################
@doc raw"""
    max_exp(a::FacElem)

Finds the largest exponent in the factored element $a$.
"""
function max_exp(a::FacElem)
  return maximum(values(a.fac))
end

@doc raw"""
    min_exp(a::FacElem)

Finds the smallest exponent in the factored element $a$.
"""
function min_exp(a::FacElem)
  return minimum(values(a.fac))
end

@doc raw"""
    maxabs_exp(a::FacElem)

Finds the largest exponent by absolute value in the factored element $a$.
"""
function maxabs_exp(a::FacElem)
  return maximum(abs, values(a.fac))
end

function Base.hash(a::FacElem, u::UInt)
  if a.hash == UInt(0)
    h = hash(u, UInt(3127))
    for (k,v) = a.fac
      h = hash(k, hash(v, h))
    end
    a.hash = h
  end
  return a.hash
end

#################################################################################
##
##  Auxiliary deep copy functions
##
#################################################################################
#
#function _deepcopy{K, V}(x::Dict{K, V})
#  z = typeof(x)()
#  for a in keys(x)
#    z[a] = deepcopy(x[a])
#  end
#  return z
#end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (F::FacElemMon)(a::T) where T
  z = F()
  z.fac[a] = ZZRingElem(1)
  return z
end

#function order(A::FacElemMon{IdealSet})
#  return order(A.base_ring)
#end

function order(A::FacElemMon)
  return order(A.base_ring)
end

(::Type{FacElem{T}})(a::FacElem{T}) where {T} = a

(::Type{FacElem})(a::FacElem{T}) where {T} = a
