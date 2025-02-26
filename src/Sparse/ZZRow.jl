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
  set!(n, get_ptr(a, i))
  return n
end

function Base.setindex!(a::ZZRingElem_Array, v::ZZRingElem, i::Integer)
  @assert i <= length(a)
  set!(get_ptr(a, i), v)
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
  sizehint!(a.ar, i)
  return a
end

function empty!!(a::ZZRingElem_Array)
  p = get_ptr(a, 1)
  for i=1:length(a)
    if !Nemo.__fmpz_is_small(a.ar[i])
      ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, ), p)
    end
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
      a.ar[i] = 0
    end
  elseif n < la
    for i=n+1:la
      ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, ), get_ptr(a, i))
    end
    resize!(a.ar, n)
    a.l = n
  end
  return a
end

function Base.deleteat!(a::ZZRingElem_Array, b::Int64)
  ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, ), get_ptr(a, b))
  deleteat!(a.ar, b)
  a.l -= 1
end

function Base.insert!(a::ZZRingElem_Array, b::Int64, c::ZZRingElem)
  insert!(a.ar, b, 0)
  a.l += 1
  a[b] = c
end



function Base.deepcopy_internal(a::ZZRingElem_Array, dict::IdDict)
  b = ZZRingElem_Array()
  sizehint!(b, length(a))
  ap = get_ptr(a, 1)
  for i=1:length(a)
    push!(b, ap)
    ap += sizeof(Int)
  end
  return b
end

end # module

using ..ZZRingElem_Array_Mod: ZZRingElem_Array, get_ptr

sparse_inner_type(::Type{ZZRingElem}) = ZZRingElem_Array

function sparse_row(R::ZZRing)
  return SRow(R, Int[], ZZRingElem_Array())
end

import Base: ==

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
  pa = get_ptr(a.values, 1)
  pb = get_ptr(b.values, 1)
  for i=1:length(a)
    if ccall((:fmpz_cmp, Nemo.libflint), Cint, (Ptr{ZZRingElem}, Ptr{ZZRingElem}), pa, pb) != 0
      return false
    end
    pa += sizeof(Int)
    pb += sizeof(Int)
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
    if !is_zero(val[i])
      push!(a, val[i])
      push!(l, pos[i])
    else
      error("zero passed in")
    end
  end
  return SRow(R, l, a)
end


function add_scaled_row(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, c::ZZRingElem, sr::SRow{ZZRingElem} = sparse_row(ZZ))
  empty!(sr)
  n = ZZRingElem()
  pi = 1
  pj = 1
  li = length(Ai)
  lj = length(Aj)
  sizehint!(sr.pos, li+lj)
  sizehint!(sr.values, li+lj)
  while pi <= li && pj <= lj
    pos_i = Ai.pos[pi]
    pos_j = Aj.pos[pj]
    if pos_i < pos_j
      push!(sr.pos, pos_i)
      mul!(n, c, get_ptr(Ai.values, pi))
      push!(sr.values, n)
      pi += 1
    elseif pos_i > pos_j
      push!(sr.pos, pos_j)
      push!(sr.values, get_ptr(Aj.values, pj))
      pj += 1
    else
      mul!(n, c, get_ptr(Ai.values, pi))
      add!(n, n, get_ptr(Aj.values, pj))
#      n = c*Ai.values[pi] + Aj.values[pj]
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
  return sr
end

function add_scaled_row!(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, c::ZZRingElem, sr::SRow{ZZRingElem} = sparse_row(ZZ))
  if iszero(c)
    return Aj
  end
  _t = sr
  sr = add_scaled_row(Ai, Aj, c, sr)
  @assert _t === sr
  swap!(Aj, sr)
  return Aj
end

function sparse_row(M::ZZMatrix)
  pos = Int[]
  vals = ZZRingElem_Array()
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
