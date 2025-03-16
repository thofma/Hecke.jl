module ZZRingElem_Array_Mod

using Nemo
using Nemo: set!

mutable struct ZZRingElem_Array <: AbstractVector{ZZRingElem}
  ar::Vector{Int}
  l::Int
  function ZZRingElem_Array(l::Int = 0)
    ar = new(zeros(Int, l), l)
    return finalizer(ar) do x
      empty!!(x)
    end
  end
end

function get_ptr(a::ZZRingElem_Array, i::Int)
  return Ptr{ZZRingElem}(pointer(a.ar, i))
end

function Base.getindex(a::ZZRingElem_Array, i::Integer)
  n = ZZRingElem()
  return set!(n, get_ptr(a, i))
end

function Nemo.getindex!(n::ZZRingElem, a::ZZRingElem_Array, i::Integer)
  set!(n, get_ptr(a, i))
  return n
end

function Base.setindex!(a::ZZRingElem_Array, v::ZZRingElem, i::Integer)
  @assert i <= length(a)
  set!(get_ptr(a, i), v)
  return v
end

function Base.setindex!(a::ZZRingElem_Array, v::Int, i::Integer)
  @assert i <= length(a)
  if Nemo.__fmpz_is_small(a.ar[i]) && Nemo.__fmpz_is_small(v)
    a.ar[i] = v
  else
    set!(get_ptr(a, i), v)
  end
  return v
end


@inline function Base.setindex!(a::ZZRingElem_Array, v::Ptr{ZZRingElem}, i::Int)
  @assert i <= length(a)
  @inbounds if (unsigned(a.ar[i]) >> (Sys.WORD_SIZE - 2) != 1)
    uu = unsafe_load(Ptr{Int}(v))
    if (unsigned(uu) >> (Sys.WORD_SIZE - 2) != 1)
      @inbounds a.ar[i] = uu
      return
    end
  end
  ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, Ptr{ZZRingElem}), get_ptr(a, i), v)
  return v
end

function Base.length(a::ZZRingElem_Array)
  return a.l
end

function Base.size(a::ZZRingElem_Array, i::Int)
  if i == 1
    return a.l
  else
    return 1
  end
end

function Base.size(a::ZZRingElem_Array)
  return (length(a), )
end

function Base.eltype(a::ZZRingElem_Array)
  return ZZRingElem
end

function Base.iterate(a::ZZRingElem_Array, state::Int = 1)
  if state > length(a)
    return nothing
  end
  return a[state], state+1
end

function Base.sizehint!(a::ZZRingElem_Array, i::Int)
  return sizehint!(a.ar, i)

  l = length(a.ar)
  if i > l
    resize!(a.ar, i)
    for j=l+1:i
      a.ar[j] = 0
    end
  else
    for j=i+1:l
      a.ar[j] = 0
    end
  end
  return a
end

function empty!!(a::ZZRingElem_Array)
  p = get_ptr(a, 1)
  for i=1:length(a)
    @inbounds if !Nemo.__fmpz_is_small(a.ar[i])
      ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, ), p)
    end
    unsafe_store!(Ptr{Int}(p), 0)
    p += sizeof(Int)
  end
  a.l = 0
  empty!(a.ar)
end

function Base.empty!(a::ZZRingElem_Array)
  a.l = 0
  return a
end

function Base.push!(a::ZZRingElem_Array, b::ZZRingElem)
  if length(a.ar) > a.l
    a.l += 1
  else
    push!(a.ar, 0)
#    @assert length(a.ar) > a.l
    a.l += 1
  end
  set!(get_ptr(a, length(a)), b)
  return a
end

function Base.push!(a::ZZRingElem_Array, b::Ptr{ZZRingElem})
  if length(a.ar) > a.l
    a.l += 1
  else
    push!(a.ar, 0)
#    @assert length(a.ar) > a.l
    a.l += 1
  end
  set!(get_ptr(a, length(a)), b)
  return a
end

function Base.push!(a::ZZRingElem_Array, b::Ref{ZZRingElem})
  if length(a.ar) > a.l
    a.l += 1
  else
    push!(a.ar, 0)
#    @assert length(a.ar) > a.l
    a.l += 1
  end
  set!(get_ptr(a, length(a)), b)
  return a
end


function Base.push!(a::ZZRingElem_Array, b::Int)
  if length(a.ar) > a.l
    a.l += 1
  else
    push!(a.ar, 0)
#    @assert length(a.ar) > a.l
    a.l += 1
  end
  if Nemo.__fmpz_is_small(b) && Nemo.__fmpz_is_small(a.ar[a.l])
    a.ar[a.l] = b
  else
    set!(get_ptr(a, length(a)), b)
  end
  return a
end

function Base.hash(a::ZZRingElem_Array, b::UInt)
  if length(a) == 0
    return hash(0, b)
  end
  for i=1:length(a)
    b = Nemo._hash_integer(a.ar[i], b)
  end
  return b
end

function Base.resize!(a::ZZRingElem_Array, n::Int)
  la = length(a)
  if n > la
    resize!(a.ar, n)
    a.l = n
    for i=la+1:n
      @inbounds a.ar[i] = 0
    end
  elseif n < la
    ap = get_ptr(a, n+1)
    for i=n+1:la
      ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, ), ap)
      unsafe_store!(Ptr{Int}(ap), 0)
      ap += sizeof(Int)
    end
    resize!(a.ar, n)
    a.l = n
  end
  return a
end

function Base.deleteat!(a::ZZRingElem_Array, b::Int64)
  ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, ), get_ptr(a, b))
  a.ar[b] = 0
  deleteat!(a.ar, b)
  a.l -= 1
end

function Base.pop!(a::ZZRingElem_Array)
  length(a) < 1 && throw(ArgumentError("array must not be empty"))
  l = length(a)
  r = ZZ()
  r.d, a.ar[l] = a.ar[l], r.d
  resize!(a, l-1)
  return r
end

function Base.insert!(a::ZZRingElem_Array, b::Int64, c::ZZRingElem)
  insert!(a.ar, b, 0)
  a.l += 1
  a[b] = c
end

function Base.deepcopy_internal(a::ZZRingElem_Array, dict::IdDict)
  b = ZZRingElem_Array()
  sizehint!(b, length(a))
  Base.GC.@preserve a begin
    ap = get_ptr(a, 1)
    for i=1:length(a)
      push!(b, ap)
      ap += sizeof(Int)
    end
  end
  return b
end

function Base.maximum(::typeof(nbits), a::ZZRingElem_Array)
  length(a) == 0 && return 0
  mx = 0
  Base.GC.@preserve a begin
    ap = get_ptr(a, 1)
    for i=1:length(a)
      mx = max(mx, nbits(ap))
      ap += sizeof(Int)
    end
  end
  return mx
end

function Base.maximum!(m::ZZRingElem, ::typeof(abs), a::ZZRingElem_Array)
  length(a) == 0 && return zero!(m)
  Base.GC.@preserve a begin
    mx = get_ptr(a, 1)
    ap = get_ptr(a, 1)
    for i=1:length(a)
      mx = cmpabs(mx, ap) < 0 ? ap : mx
      ap += sizeof(Int)
    end
    Nemo.set!(m, mx)
    if is_negative(m)
      return neg!(m)
    else
      return m
    end
  end
end
function Base.maximum(::typeof(abs), a::ZZRingElem_Array)
  return maximum!(ZZ(), abs, a)
end

function Base.maximum!(m::ZZRingElem, a::ZZRingElem_Array)
  length(a) == 0 && return zero!(m)
  Base.GC.@preserve a begin
    mx = get_ptr(a, 1)
    ap = get_ptr(a, 1)
    for i=1:length(a)
      mx = cmp(mx, ap) > 0 ? mx : ap
      ap += sizeof(Int)
    end
    Nemo.set!(m, mx)
  end
  return m
end

function Base.maximum(a::ZZRingElem_Array)
  return maximum!(ZZ(), a)
end

function Base.minimum!(m::ZZRingElem, a::ZZRingElem_Array)
  length(a) == 0 && return zero!(m)
  Base.GC.@preserve a begin
    mx = get_ptr(a, 1)
    ap = get_ptr(a, 1)
    for i=1:length(a)
      mx = cmp(mx, ap) < 0 ? mx : ap
      ap += sizeof(Int)
    end
    Nemo.set!(m, mx)
  end
  return m
end

function Base.minimum(a::ZZRingElem_Array)
  return minimum!(ZZ(), a)
end


end # module

using ..ZZRingElem_Array_Mod: ZZRingElem_Array, get_ptr

sparse_inner_type(::Type{ZZRingElem}) = ZZRingElem_Array

function sparse_row(R::ZZRing)
  return SRow(R, Int[], ZZRingElem_Array())
end

import Base: ==

import AbstractAlgebra.Generic: heapparent, heapleft, heapright

function _perc_up!(a::SRow) #the last item
  i = length(a)
  xi = a.pos[i]
  xv = a.values.ar[i]
  while (j = heapparent(i)) >= 1
    if xi < a.pos[j]
      a.pos[i] = a.pos[j]
      a.values.ar[i] = a.values.ar[j]
      i = j
    else
      break
    end
  end
  a.values.ar[i] = xv
  a.pos[i] = xi
end

function _perc_down!(a::SRow, i::Int, len::Int = length(a)) #elem in pos i is wrong, possibly
  xi = a.pos[i]
  xv = a.values.ar[i]
  while (l = heapleft(i)) <= len
    r = heapright(i)
    j = r > len || a.pos[l] < a.pos[r] ? l : r
    if a.pos[j] >= xi
      break
    end
    a.pos[i] = a.pos[j]
    a.values.ar[i] = a.values.ar[j]
    i = j
  end
  a.pos[i] = xi
  a.values.ar[i] = xv
end

function Nemo.add!(a::SRow{ZZRingElem, ZZRingElem_Array}, p::Pair{Int, ZZRingElem})
  k = p[1]
  v = p[2]
  if iszero(v)
    return
  end
  if length(a) == 0
    push!(a.pos, k)
    push!(a.values, v)
    return
  end
  if a.pos[1] == k
    a.values[1] = add!(a.values[1], a.values[1], v)
    while iszero(a.values.ar[1])
      pop_first!(a)
      if length(a) == 0
        return
      end
    end
    @assert a.values.ar[1] != 0
    return
  end
  push!(a.values, v)
  push!(a.pos, k)
  _perc_up!(a)
end

function pop_first!(a::SRow{ZZRingElem, ZZRingElem_Array}, len::Int = length(a))
  len == 0 && throw(ArgumentError("row must be non-empty"))
  len == 1 && return pop!(a.pos)=>pop!(a.values)
  xi = a.pos[1]
  xv = a.values[1]
  a.pos[1] = a.pos[len]
  a.values.ar[1] = a.values.ar[len]
  deleteat!(a.pos, len)
  deleteat!(a.values, len)
  len -= 1
  _perc_down!(a, 1, len)
  while (len > 1 && a.pos[1] == a.pos[2]) || (len > 2 && a.pos[1] == a.pos[3])
    if a.pos[1] == a.pos[2]
      a.values[2] += a.values[1]
    else
      a.values[3] += a.values[1]
    end
    a.pos[1] = a.pos[len]
    a.values.ar[1] = a.values.ar[len]
    deleteat!(a.pos, len)
    deleteat!(a.values, len)
    len -= 1
    _perc_down!(a, 1, len)
  end
    
  return xi=>xv, len
end

#=
function Base.sort!(a::SRow) end

function Base.sort!(a::SRow{ZZRingElem, ZZRingElem_Array})
  length(a) == 0 && return
  i = 1
  pos = length(a)
  while pos > 1
    a.pos[1], a.pos[pos] = a.pos[pos], a.pos[1]
    a.values.ar[1], a.values.ar[pos] = a.values.ar[pos], a.values.ar[1]
    pos -= 1
    _perc_down!(a, 1, pos)
  end

  reverse!(a.pos)
#  @assert a.pos == sort(a.pos)
  reverse!(a.values.ar)
  i = 1
  s = 0
  x = a.pos[1]

  v = ZZRingElem(Val(:raw))
  while i <= length(a)
    j = i+1
    set!(v, get_ptr(a.values, i))
    while j <= length(a) && a.pos[j] == a.pos[i]
      add!(v, v, get_ptr(a.values, j))
#      v += a.values[j]
      j += 1
    end
    if !is_zero(v)
      s += 1
      a.values.ar[s], v.d = v.d, a.values.ar[s]
      a.pos[s] = a.pos[i]
    end
    i = j
  end
  Nemo._fmpz_clear_fn(v)
  resize!(a.pos, s)
  resize!(a.values, s)

  return nothing
end

=#


function ==(a::SRow{ZZRingElem, ZZRingElem_Array}, b::SRow{ZZRingElem, ZZRingElem_Array})
  if length(a) != length(b)
    return false
  end
  if a.pos != b.pos
    return false
  end
  if a.values.ar == b.values.ar
    return true
  end
  Base.GC.@preserve a b begin
    pa = get_ptr(a.values, 1)
    pb = get_ptr(b.values, 1)
    for i=1:length(a)
#      if ccall((:fmpz_cmp, Nemo.libflint), Cint, (Ptr{ZZRingElem}, Ptr{ZZRingElem}), pa, pb) != 0
      if cmp(pa, pb) != 0
        return false
      end
      pa += sizeof(Int)
      pb += sizeof(Int)
    end
  end
  return true
end

function sparse_row(R::ZZRing, A::Vector{Tuple{Int64, Int64}}; sort::Bool = true)
  if sort && length(A) > 1
    A = Base.sort(A, lt=(a,b)->isless(a[1], b[1]))
  end
  a = ZZRingElem_Array()
  sizehint!(a, length(A))
  l = Int[]
  for (p, v) = A
    if !is_zero(v)
      push!(a, v)
      push!(l, p)
    end
  end
  return SRow(R, l, a)
end

function sparse_row(R::ZZRing, A::Vector{Tuple{Int64, ZZRingElem}}; sort::Bool = true)
  if sort && length(A) > 1
    A = Base.sort(A, lt=(a,b)->isless(a[1], b[1]))
  end
  a = ZZRingElem_Array()
  sizehint!(a, length(A))
  l = Int[]
  for (p, v) = A
    if !is_zero(v)
      push!(a, v)
      push!(l, p)
    end
  end
  return SRow(R, l, a)
end

function sparse_row(R::ZZRing, pos::Vector{Int64}, val::AbstractVector{T}; sort::Bool = true) where T
  if sort && length(pos) > 1
    p = sortperm(pos)
    pos = pos[p]
    val = val[p]
  end
  @assert length(pos) == length(val)

  a = ZZRingElem_Array()
  sizehint!(a, length(val))
  l = Int[]
  for i=1:length(pos)
    @inbounds if !is_zero(val[i])
      @inbounds push!(a, val[i])
      @inbounds push!(l, pos[i])
    else
      error("zero passed in")
    end
  end
  return SRow(R, l, a)
end

function scale_row!(a::SRow{ZZRingElem}, b::Union{ZZRingElem, Int}) 
  if iszero(b)
    return empty!(a)
  elseif isone(b)
    return a
  end
  i = 1
  ap = get_ptr(a.values, i)
  while i <= length(a)
    mul!(ap, b, ap)
    ap += sizeof(Int)
    i += 1
  end
  return a
end

function _add_scaled_row(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, c::ZZRingElem, sr::SRow{ZZRingElem} = sparse_row(ZZ))
  empty!(sr)
  n = ZZRingElem()#Val(:raw))
  pi = 1
  pj = 1
  li = length(Ai)
  lj = length(Aj)
  sizehint!(sr.pos, li+lj)
  sizehint!(sr.values, li+lj)
  @assert !iszero(c)
  wr = 1
  @inbounds while pi <= li && pj <= lj
    pos_i = Ai.pos[pi]
    pos_j = Aj.pos[pj]
    if pos_i < pos_j
      mul!(n, c, get_ptr(Ai.values, pi))
      push!(sr.values, n)
      push!(sr.pos, pos_i)
      pi += 1
    elseif pos_i > pos_j
      push!(sr.pos, pos_j)
      push!(sr.values, get_ptr(Aj.values, pj))
      pj += 1
    else
      mul!(n, c, get_ptr(Ai.values, pi))
      add!(n, n, get_ptr(Aj.values, pj))
      if !iszero(n)
        push!(sr.pos, pos_i)
        push!(sr.values, n)
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= li
    push!(sr.pos, Ai.pos[pi])
    mul!(n, c, get_ptr(Ai.values, pi))
    push!(sr.values, n)
    pi += 1
  end
  while pj <= lj
    push!(sr.pos, Aj.pos[pj])
    push!(sr.values, get_ptr(Aj.values, pj))
    pj += 1
  end
#  Nemo._fmpz_clear_fn(n) 
  return sr
end

const val = ZZRingElem_Array_Mod.ZZRingElem_Array(100)
const pos = zeros(Int, 100)

function Base.maximum(::typeof(nbits), a::SRow)
  return length(a) == 0 ? 0 : maximum(nbits, a.values)
end

function add_scaled_row(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, c::ZZRingElem, sr::SRow{ZZRingElem} = sparse_row(ZZ))
#  _x = _add_scaled_row(Ai, Aj, c)

  li = length(Ai)
  lj = length(Aj)
  if li+lj < 10
    return _add_scaled_row(Ai, Aj, c, sr)
  end
  pi = 1
  pj = 1
  n = ZZRingElem()
  global pos
  global val
  @assert length(pos) == length(val.ar)
  if li+lj > length(pos)
    resize!(pos, 2*(li+lj))
    resize!(val, 2*(li+lj))
  end
  @assert !iszero(c)
  wr = 1
  @inbounds while pi <= li && pj <= lj
    pos_i = Ai.pos[pi]
    pos_j = Aj.pos[pj]
    if pos_i < pos_j
      pos[wr] = pos_i
      mul!(n, c, get_ptr(Ai.values, pi))
      val[wr] = n
      wr += 1
      pi += 1
    elseif pos_i > pos_j
      pos[wr] = pos_j
      val[wr] = get_ptr(Aj.values, pj)
      wr += 1
      pj += 1
    else
      mul!(n, c, get_ptr(Ai.values, pi))
      add!(n, n, get_ptr(Aj.values, pj))
      if !iszero(n)
        pos[wr] = pos_i
        val[wr] = n
        wr += 1
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= li
    pos[wr] = Ai.pos[pi]
    mul!(n, c, get_ptr(Ai.values, pi))
    val[wr] = n
    wr += 1
    pi += 1
  end
  while pj <= lj
    pos[wr] = Aj.pos[pj]
    val[wr] = get_ptr(Aj.values, pj)
    wr += 1
    pj += 1
  end
  resize!(sr.pos, wr-1)
  resize!(sr.values, wr-1)
  view(sr.pos, 1:wr-1) .= view(pos, 1:wr-1)
  for i=1:wr-1
    sr.values.ar[i], val.ar[i] = val.ar[i], sr.values.ar[i]
  end
  sr.values.l = wr-1
  return sr
end

function add_scaled_row!(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, c::ZZRingElem, sr::SRow{ZZRingElem} = sparse_row(ZZ))
  if iszero(c)
    return Aj
  end
#  _t = sr
  sr = add_scaled_row(Ai, Aj, c, sr)
#  @assert _t === sr
  swap!(Aj, sr)
  return Aj
end

#=
#Heap-based and too slow
function add_scaled_row!(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, c::ZZRingElem, sr::SRow{ZZRingElem} = sparse_row(ZZ))
  if iszero(c)
    return Aj
  end
#  s = add_scaled_row(Ai, Aj, c)

  v = ZZRingElem(Val(:raw))
  for k = 1:length(Ai)
    mul!(v, c, get_ptr(Ai.values, k))
    add!(Aj, Ai.pos[k]=>v)
  end
  Nemo._fmpz_clear_fn(v)
#  sort!(Aj)
#  s == Aj || (@show s; @show Aj)
#  @assert s == Aj
  return Aj
end
=#


function sparse_row(M::ZZMatrix)
  pos = Int[]
  vals = ZZRingElem_Array()
  @req nrows(M) == 1 "matrix must have only 1 row"
  GC.@preserve M begin
    for i = 1:ncols(M)
      if is_zero_entry(M, 1, i)
        continue
      end
      push!(pos, i)
      push!(vals, Nemo.mat_entry_ptr(M, 1, i))
    end
  end
  return SRow(ZZ, pos, vals)
end

function get_tmp(A::SMat{ZZRingElem})
  if isdefined(A, :tmp) && length(A.tmp) > 0
    return pop!(A.tmp)
  end
  return SRow(ZZ, Int[], ZZRingElem_Array())
end


function transform_row(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, a::ZZRingElem, b::ZZRingElem, c::ZZRingElem, d::ZZRingElem, sr::SRow{ZZRingElem}, tr::SRow{ZZRingElem})
  empty!(sr)
  empty!(tr)
  pi = 1
  pj = 1
  li = length(Ai)
  lj = length(Aj)
  s = ZZRingElem()
  t = ZZRingElem()
#  sizehint!(sr, length(Ai) + length(Aj))
#  sizehint!(tr, length(Ai) + length(Aj))

  GC.@preserve Ai Aj begin
    while pi <= li && pj <= lj
      pos_i = Ai.pos[pi]
      pos_j = Aj.pos[pj]
      if pos_i < pos_j
        val_i = get_ptr(Ai.values, pi)
        if a != 0
          push!(sr.pos, pos_i)
          mul!(s, a, val_i)
          push!(sr.values, s)
        end
        if c != 0
          push!(tr.pos, pos_i)
          mul!(s, c, val_i)
          push!(tr.values, s)
        end
        pi += 1
      elseif pos_i > pos_j
        val_j = get_ptr(Aj.values, pj)
        if b != 0
          push!(sr.pos, pos_j)
          mul!(s, b, val_j)
          push!(sr.values, s)
        end
        if d != 0
          push!(tr.pos, pos_j)
          mul!(s, d, val_j)
          push!(tr.values, s)
        end
        pj += 1
      else
        val_i = get_ptr(Ai.values, pi)
        val_j = get_ptr(Aj.values, pj)
        mul!(s, a, val_i)
        mul!(t, b, val_j)
        add!(s, s, t)
        if !is_zero(s)
          push!(sr.pos, pos_i)
          push!(sr.values, s)
        end
        mul!(s, c, val_i)
        mul!(t, d, val_j)
        add!(s, s, t)
        if !is_zero(s)
          push!(tr.pos, pos_i)
          push!(tr.values, s)
        end
        pi += 1
        pj += 1
      end
    end
    while pi <= li
      pos_i = Ai.pos[pi]
      val_i = get_ptr(Ai.values, pi)
      if a != 0
        push!(sr.pos, pos_i)
        mul!(s, a, val_i)
        push!(sr.values, s)
      end
      if c != 0
        push!(tr.pos, pos_i)
        mul!(s, c, val_i)
        push!(tr.values, s)
      end
      pi += 1
    end
    while pj <= lj
      pos_j = Aj.pos[pj]
      val_j = get_ptr(Aj.values, pj)
      if b != 0
        push!(sr.pos, pos_j)
        mul!(s, b, val_j)
        push!(sr.values, s)
      end
      if d != 0
        push!(tr.pos, pos_j)
        mul!(s, d, val_j)
        push!(tr.values, s)
      end
      pj += 1
    end
  end

  return sr, tr
end


function transform_row!(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, a::ZZRingElem, b::ZZRingElem, c::ZZRingElem, d::ZZRingElem, sr::SRow{ZZRingElem}, tr::SRow{ZZRingElem})
  q, w = transform_row(Ai, Aj, a, b, c, d, sr, tr)
  @assert q === sr
  @assert w === tr
  swap!(q, Ai)
  swap!(w, Aj)
end
