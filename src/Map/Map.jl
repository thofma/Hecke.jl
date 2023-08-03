
#function image_func(M::Map)
#  return M.header.image
#end
#
#function preim_func(M::Map)
#  return M.header.preim
#end


function show(io::IO, M::InverseMap)
  @show_name(io, M)
  println(io, "inverse of")
  print(io, " ", M.origin)
end

function pseudo_inv(a::Map)
  return InverseMap(a)
end

#function show(io::IO, M::CoerceMap)
#  println(io, "Coerce: $(domain(M)) -> $(codomain(M))")
#end

function change(D::Dict{K, V}, k::K, def::V, new::Function) where {K, V}
  i = Base.ht_keyindex2!(D, k)
  if i>0
    D.vals[i] = new(D.vals[i])
  else
    pos = -i
    D.keys[pos] = k
    D.vals[pos] = def
    D.count += 1
    if pos < D.idxfloor
      D.idxfloor = pos
    end
    D.slots[pos] = 0x1
  end
  return nothing
end

function inc(D::Dict{K, Int}, k::K, def::Int = 0) where K
  i = Base.ht_keyindex2!(D, k)
  if i>0
    D.vals[i] += 1
  else
    pos = -i
    D.keys[pos] = k
    D.vals[pos] = def
    D.count += 1
    if pos < D.idxfloor
      D.idxfloor = pos
    end
    D.slots[pos] = 0x1
  end
  return nothing
end


function _allow_cache!(M::Map, lim::Int, ::Type{D}, ::Type{C}, ::Type{De}, ::Type{Ce}) where {D, C, De, Ce}
  if isdefined(M.header, :cache)
#    println("Cache already installed")
  else
    M.header.cache = MapCache(domain(M), codomain(M), De, Ce, lim)
    M.header.cache.old_pr = M.header.preimage
    M.header.cache.old_im = M.header.image
  end

  if length(methods(M.header.image)) > 1
    println("Cannot do image cache, too many types")
  else
    function im(a::De)
      if haskey(M.header.cache.im, a)
        inc(M.header.cache.imStat, a)
        return M.header.cache.im[a]::Ce
      else
        b = M.header.cache.old_im(a)::Ce
        M.header.cache.im[a] = b
        M.header.cache.imStat[a] = 0
        return b
      end
    end
    M.header.image = im
  end

  if length(methods(M.header.preimage)) > 1
    println("Cannot do preimage cache, too many types")
  else
    function pr(a::Ce)
      i = Base.ht_keyindex(M.header.cache.pr, a)
      if i >= 0
        inc(M.header.cache.prStat, a)
        return M.header.cache.pr.vals[i]::De
      else
        b = M.header.cache.old_pr(a)::De
        M.header.cache.pr[a] = b
        M.header.cache.prStat[a] = 0
        return b
      end
    end
    M.header.preimage = pr
  end
  nothing
end

function allow_cache!(M::T, lim::Int = 100) where T <: Map
  return _allow_cache!(M, lim, typeof(domain(M)), typeof(codomain(M)), elem_type(domain(M)), elem_type(codomain(M)))
end

function stop_cache!(M::T) where T <: Map
  if isdefined(M.header, :cache)
    M.header.image = M.header.cache.old_im
    M.header.preimage = M.header.cache.old_pr
  end
  nothing
end

