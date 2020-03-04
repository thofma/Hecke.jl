export FacElem, FacElemMon, simplify, factor_coprime

export transform

################################################################################
#
#  Insert in a dictionary
#
################################################################################

function add_to_key!(D::Dict{S, T}, k::S, v) where S where T <: Union{fmpz, Integer}
  add_to_key!(D, k, T(v))
  return nothing
end

function add_to_key!(D::Dict{S, T}, k::S, v::T) where S where T <: Union{fmpz, Integer}
  hash_k = Base.ht_keyindex2!(D, k)
  if hash_k > 0
    #The key is in the dictionary, we only need to add
    @inbounds D.vals[hash_k] += v
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

################################################################################
#
#  Multiplicative representation
#
################################################################################

# abstract nonsense

const FacElemMonDict = IdDict()

function (x::FacElemMon{S})() where S
  z = FacElem{elem_type(S), S}()
  z.fac = Dict{elem_type(S), fmpz}()
  z.parent = x
  return z
end
@doc Markdown.doc"""
    FacElem{B}(base::Array{B, 1}, exp::Array{fmpz, 1}) -> FacElem{B}
Returns the element $\prod b_i^{e_i}$, un-expanded.
"""
function FacElem(base::Array{B, 1}, exp::Array{fmpz, 1}) where B

  length(base) == 0 && error("Array must not be empty")

  length(base) != length(exp) && error("not the same length")

  z = FacElem{B, typeof(parent(base[1]))}()

  for i in 1:length(base)
    if iszero(exp[i])
      continue
    end
    add_to_key!(z.fac, base[i], exp[i])
  end

  z.parent = FacElemMon(parent(base[1]))
  return z
end

@doc Markdown.doc"""
    FacElem{B}(d::Dict{B, fmpz}) -> FacElem{B}
    FacElem{B}(d::Dict{B, Integer}) -> FacElem{B}
Returns the element $\prod b^{d[p]}$, un-expanded.
"""
function FacElem(d::Dict{B, fmpz}) where B

  length(d) == 0 && error("Dictionary must not be empty")

  z = FacElem{B, typeof(parent(first(keys(d))))}()
  z.fac = d

  z.parent = FacElemMon(parent(first(keys(d))))
  return z
end

function FacElem(R::Ring)
  z = FacElem{elem_type(R), typeof(R)}()
  z.fac = Dict{elem_type(R), fmpz}()
  z.parent = FacElemMon(R)
  return z
end

function FacElem(d::Dict{B, T}) where {B, T <: Integer}

  length(d) == 0 && error("Dictionary must not be empty")

  z = FacElem{B, typeof(parent(first(keys(d))))}()
  z.fac = Dict{B, fmpz}((k,fmpz(v)) for (k,v) = d) 

  z.parent = FacElemMon(parent(first(keys(d))))
  return z
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

check_parent(x::FacElem{S, T}, y::FacElem{S, T}) where { S, T } = base_ring(x) == base_ring(y)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::FacElemMon)
  print(io, "Factored elements over $(x.base_ring)")
end

function show(io::IO, x::FacElem)
  print(io, "Factored element with data\n$(x.fac)")
end

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

function pow!(z::FacElem, x::FacElem, y::T) where T <: Union{fmpz, Integer}
  z.fac = copy(x.fac)
  for (a, v) in x
    # this should be inplace ... not sure anymore: using copy, inplace is bad
    z.fac[a] = y*v
  end
end

function pow!(x::FacElem, y::T) where T <: Union{fmpz, Integer}
  for (a, v) in x
    # this should be inplace ... not sure anymore: using copy, inplace is bad
    x.fac[a] = y*v
  end
end

# ^(x::FacElem, y::Union{fmpz, Integer}) is ambiguous
for T in [:Integer, fmpz]
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
        for (a, v) in x
          # this should be inplac
          z.fac[a] = y*v
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
    add_to_key!(z.fac, a, v)
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
    add_to_key!(z.fac, a, v)
  end
  return z
end

function *(x::FacElem{B}, y::B) where B
  @assert base_ring(x) == parent(y)
  z = copy(x)
  add_to_key!(z.fac, y, 1)
  return z
end

function *(y::B, x::FacElem{B}) where B
  @assert base_ring(x) == parent(y)
  z = copy(x)
  add_to_key!(z.fac, y, 1)
  return z
end

function div(x::FacElem{B}, y::FacElem{B}) where B
  @assert check_parent(x, y) "Elements must have the same parent"
  z = copy(x)
  for (a, v) in y
    add_to_key!(z.fac, a, -v)
  end
  return z
end

################################################################################
#
#  Apply transformation
#
################################################################################

# return (x1,...,xr)*y
function _transform(x::Array{FacElem{T, S}, 1}, y::fmpz_mat) where {T, S}
  length(x) != nrows(y) &&
              error("Length of array must be number of rows of matrix")

  z = Array{FacElem{T, S}}(undef, ncols(y))

  t = parent(x[1])()

  for i in 1:ncols(y)
    z[i] = x[1]^y[1,i]
    for j in 2:nrows(y)
      if y[j, i] == 0
        continue
      end
      pow!(t, x[j], y[j, i])
      mul!(z[i], z[i], t)
    end
  end
  return z
end

function transform(x::Array{FacElem{S, T}, 1}, y::fmpz_mat) where {S, T}
  return _transform(x, y)
end

function transform_left!(x::Array{FacElem{S, T}, 1}, y::TrafoSwap{fmpz}) where {S, T}
  x[y.i], x[y.j] = x[y.j], x[y.i]
  nothing
end

function transform_left!(x::Array{FacElem{S, T}, 1}, y::TrafoAddScaled{fmpz}) where {S, T}
  x[y.j] = x[y.j] * x[y.i]^y.s
  nothing
end

function transform_left!(x::Array{FacElem{S, T}, 1}, y::TrafoPartialDense{R}) where {S, T, R}
  z = view(deepcopy(x), y.rows)
  xx = view(x, y.rows)
  for i in 1:nrows(y.U)
    xx[i] = z[1]^Int(y.U[i, 1])
    for j in 2:ncols(y.U)
      xx[i] *= z[j]^Int(y.U[i, j])
    end
  end
end

function transform_left!(x::Array{T, 1}, t::TrafoDeleteZero{S}) where {S, T}
  # move ith position to the back
  for j in t.i:length(x)-1
    r = x[j]
    x[j] = x[j + 1]
    x[j + 1] = r
  end
end

function transform_left!(x::Array{FacElem{S, T}, 1}, y::TrafoParaAddScaled{R}) where {S, T, R}
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

function evaluate(x::FacElem{NfOrdIdl, NfOrdIdlSet}; coprime::Bool = false)
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

function _ev(d::Dict{nf_elem, fmpz}, oe::nf_elem)
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

function _ev(d::Dict{fq_nmod, fmpz}, z::fq_nmod)
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
        ccall((:fq_nmod_pow, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{fmpz}, Ref{FqNmodFiniteField}), kv, k, v, Fq)
        mul!(z, z, kv)
      else
        kv = Fq()
        ccall((:fq_nmod_inv, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{FqNmodFiniteField}), kv, k, Fq)
        ccall((:fq_nmod_pow, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{fmpz}, Ref{FqNmodFiniteField}), kv, kv, -v, Fq)
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

function _ev(d::Dict{T, fmpz}, oe::T) where T
  z = copy(oe)
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

function one(A::NfOrdFracIdlSet)
  return ideal(order(A), 1)//1
end

function copy(A::NfOrdFracIdl)
  return deepcopy(A)
end

function ^(A::NfOrdFracIdl, d::fmpz)
  return A^Int(d)
end

@doc Markdown.doc"""
  evaluate{T}(x::FacElem{T}) -> T

Expands or evaluates the factored element, i.e. actually computes the
value. 
Does "square-and-multiply" on the exponent vectors.
"""
function evaluate(x::FacElem{T}) where T
  return _ev(x.fac, one(base_ring(x)))
end

@doc Markdown.doc"""
    evaluate(x::FacElem{fmpq}) -> fmpq
    evaluate(x::FacElem{fmpz}) -> fmpz

Expands or evaluates the factored element, i.e. actually computes the
the element. 
Works by first obtaining a simplified version of the power product
into coprime base elements.
"""
function evaluate(x::FacElem{fmpq})
  return evaluate_naive(simplify(x))
end

function evaluate(x::FacElem{fmpz})
  return evaluate_naive(simplify(x))
end
@doc Markdown.doc"""
    simplify(x::FacElem{fmpq}) -> FacElem{fmpq}
    simplify(x::FacElem{fmpz}) -> FacElem{fmpz}

Simplfies the factored element, i.e. arranges for the base to be coprime.
"""
function simplify(x::FacElem{fmpq})
  y = deepcopy(x)
  simplify!(y)
  return y
end

function simplify(x::FacElem{fmpz})
  y = deepcopy(x)
  simplify!(y)
  return y
end

function simplify!(x::FacElem{fmpq})
  if length(x.fac) <= 1
    return
  end
  cp = coprime_base(vcat([denominator(y) for y = base(x)], [numerator(y) for y=base(x)]))
  ev = Dict{fmpq, fmpz}()
  for p = cp
    if p == 1 || p == -1
      continue
    end
    v = fmpz(0)
    for (b, vb) in x
      v += valuation(b, abs(p))*vb
    end
    if v != 0
      ev[fmpq(abs(p))] = v
    end
  end
  f = b -> b < 0 && isodd(x.fac[b]) ? -1 : 1
  s = prod((f(v) for v in base(x)))
  if s == -1
    ev[fmpq(-1)] = 1
  else
    if length(ev) == 0
      ev[fmpq(1)] = 0
    end
  end
  x.fac = ev
  return nothing
end

function simplify!(x::FacElem{fmpz})
  if length(x.fac) == 0
    x.fac[fmpz(1)] = 0
    return
  end
  if length(x.fac) <= 1
    k,v = first(x.fac)
    if isone(k)
      x.fac[k] = 0
    elseif k == -1
      if isodd(v)
        x.fac[k] = 1
      else
        delete!(x.fac, k)
        x.fac[fmpz(1)] = 0
      end
    end
    return
  end
  cp = coprime_base(collect(base(x)))
  ev = Dict{fmpz, fmpz}()
  for p = cp
    if p == 1 || p == -1
      continue
    end
    v = fmpz(0)
    for (b, vb) in x
      v += valuation(b, abs(p))*vb
    end
    if v < 0 
      throw(DomainError(v, "Negative valuation in simplify!"))
    end
    if v != 0
      ev[abs(p)] = v
    end
  end
  f = b -> b < 0 && isodd(x.fac[b]) ? -1 : 1
  s = prod(f(v) for v in base(x))
  if s == -1
    ev[-1] = 1
  else
    if length(ev) == 0
      ev[fmpz(1)] = 0
    end
  end
  x.fac = ev
  nothing
end

@doc Markdown.doc"""
    isone(x::FacElem{fmpq}) -> Bool
    isone(x::FacElem{fmpz}) -> Bool
Tests if $x$ represents $1$ without an evaluation.
"""
function isone(x::FacElem{fmpq})
  y = simplify(x)
  return all(iszero, values(y.fac)) || all(isone, keys(y.fac))
end

function isone(x::FacElem{fmpz})
  y = simplify(x)
  return all(iszero, values(y.fac)) || all(isone, keys(y.fac))
end


#TODO: expand the coprime stuff to automatically also get the exponents
@doc Markdown.doc"""
    simplify(x::FacElem{NfOrdIdl, NfOrdIdlSet}) -> FacElem
    simplify(x::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> FacElem

Uses ```coprime_base``` to obtain a simplified version of $x$, ie.
in the simplified version all base ideals will be pariwise coprime
but not neccessarily prime!.
"""
function simplify(x::FacElem{NfOrdIdl, NfOrdIdlSet})
  z = deepcopy(x)
  simplify!(z)
  return z
end


function factor_over_coprime_base(x::FacElem{NfOrdIdl, NfOrdIdlSet}, coprime_base::Vector{NfOrdIdl})
  ev = Dict{NfOrdIdl, fmpz}()
  if isempty(coprime_base)
    return ev
  end
  OK = order(coprime_base[1])
  for p in coprime_base
    if isone(p)
      continue
    end
    P = minimum(p)
    @vprint :CompactPresentation 3 "Computing valuation at an ideal lying over $P"
    assure_2_normal(p)
    v = fmpz(0)
    for (b, e) in x
      if iszero(e)
        continue
      end
      if divisible(norm(b, copy = false), P) 
        v += valuation(b, p)*e
      end
    end
    @vprint :CompactPresentation 3 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
    if !iszero(v)
      ev[p] = v
    end
  end
  return ev
end

function simplify!(x::FacElem{NfOrdIdl, NfOrdIdlSet})
  if length(x.fac) <= 1 
    p = first(keys(x.fac))
    x.fac =  Dict(p => x.fac[p])
    return nothing
  elseif all(x -> iszero(x), values(x.fac)) 
    x.fac = Dict{NfOrdIdl, fmpz}()
    return nothing
  end
  base_x = NfOrdIdl[y for (y, v) in x if !iszero(v)]
  cp = coprime_base(base_x)
  ev = factor_over_coprime_base(x, cp)
  x.fac = ev
  return nothing
end  

function simplify(x::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  z = deepcopy(x)
  simplify!(z)
  return z
end

function simplify!(x::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  de = factor_coprime(x)
  if length(de)==0
    de = Dict(ideal(order(base_ring(parent(x))), 1) => fmpz(1))
  end
  x.fac = Dict((i//1, k) for (i,k) = de)
end

@doc Markdown.doc"""
    factor_coprime(x::FacElem{NfOrdIdl, NfOrdIdlSet}) -> Dict{NfOrdIdl, Int}
Computed a partial factorisation of $x$, ie. writes $x$ as a product
of pariwise coprime integral ideals.
"""
function factor_coprime(x::FacElem{NfOrdIdl, NfOrdIdlSet})
  z = deepcopy(x)
  simplify!(z)
  return Dict{NfOrdIdl, Int}(p=>Int(v) for (p,v) = z.fac)
end

function factor_coprime!(x::FacElem{NfOrdIdl, NfOrdIdlSet})
  simplify!(x)
  return Dict{NfOrdIdl, Int}(p => Int(v) for (p,v) = x.fac)
end

@doc Markdown.doc"""
    factor_coprime(x::FacElem{fmpz}) -> Fac{fmpz}
Computed a partial factorisation of $x$, ie. writes $x$ as a product
of pariwise coprime integers.
"""
function factor_coprime(x::FacElem{fmpz})
  x = deepcopy(x)
  simplify!(x)
  d = Dict(abs(p) => Int(v) for (p,v) = x.fac)
  if haskey(d, fmpz(-1))
    delete!(d, fmpz(-1))
    return Fac(fmpz(-1), d)
  else
    return Fac(fmpz(1), d)
  end
end

@doc Markdown.doc"""
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

function ^(a::fmpz, k::fmpz)
  if a == 0
    if k == 0
      return fmpz(1)
    end
    return fmpz(0)
  end
 
  if a == 1
    return fmpz(1)
  end
  if a == -1
    if isodd(k)
      return fmpz(-1)
    else
      return fmpz(1)
    end
  end
  return a^Int(k)
end

function ^(a::fmpq, k::fmpz)
  if a == 0
    if k == 0
      return fmpq(1)
    end
    return fmpq(0)
  end
 
  if a == 1
    return fmpq(1)
  end
  if a == -1
    if isodd(k)
      return fmpq(-1)
    else
      return fmpq(1)
    end
  end
  return a^Int(k)
end



#################################################################################
@doc Markdown.doc"""
    max_exp(a::FacElem)
Finds the largest exponent in the factored element $a$
"""
function max_exp(a::FacElem)
  return maximum(values(a.fac))
end

@doc Markdown.doc"""
    min_exp(a::FacElem)
Finds the smallest exponent in the factored element $a$
"""
function min_exp(a::FacElem)
  return minimum(values(a.fac))
end

@doc Markdown.doc"""
    maxabs_exp(a::FacElem)
Finds the largest exponent by absolute value the factored element $a$
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

#used (hopefully) only inside the class group
function FacElem(A::Array{nf_elem_or_fac_elem, 1}, v::Array{fmpz, 1})
  local B::FacElem{nf_elem, AnticNumberField}
  if typeof(A[1]) == nf_elem
    B = FacElem(A[1]::nf_elem)
  else
    B = A[1]::FacElem{nf_elem, AnticNumberField}
  end
  B = B^v[1]
  for i=2:length(A)
    if iszero(v[i])
      continue
    end
    if typeof(A[i]) == nf_elem
      local t::nf_elem = A[i]::nf_elem
      add_to_key!(B.fac, t, v[i])
    else
      local s::FacElem{nf_elem, AnticNumberField} = A[i]::FacElem{nf_elem, AnticNumberField}
      for (k, v1) in s
        if iszero(v1)
          continue
        end
        add_to_key!(B.fac, k, v1*v[i])
      end
    end
  end
  return B::FacElem{nf_elem, AnticNumberField}
end

#################################################################################
##
##  Auxillary deep copy functions
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
  z.fac[a] = fmpz(1)
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
