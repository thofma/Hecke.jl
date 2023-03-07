module ZZRingElem_Array_Mod
using Nemo

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
  return pointer(a.ar, i)
end

function Base.getindex(a::ZZRingElem_Array, i::Integer)
  n = ZZRingElem()
  ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ref{ZZRingElem}, Ptr{Int}), n, get_ptr(a, i))
  return n
end

function Base.length(a::ZZRingElem_Array)
  return a.l
end

function Base.size(a::ZZRingElem_Array, i::Int = 1)
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
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{Int}, ), p)
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
    @assert length(a.ar) > a.l
    a.l += 1
  end
  ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ptr{Int}, Ref{ZZRingElem}), get_ptr(a, length(a)), b)
  return a
end

end # module
