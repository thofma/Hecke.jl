
#function image_func(M::Map)
#  return M.header.image
#end
#
#function preim_func(M::Map)
#  return M.header.preim
#end

function show(io::IO, M::Map)
  print(io, "Map with following data\n")
  print(io, "Domain:\n")
  print(io, "=======\n")
  print(io, "$(domain(M))\n\n")
  print(io, "Codomain:\n")
  print(io, "=========\n")
  print(io, "$(codomain(M))\n")
end

function preimage(M::Map, a)
  if isdefined(M.header, :preimage)
    p = M.header.preimage(a)#::elem_type(D)
    @assert parent(p) == domain(M)
    return p
  end
  error("No preimage function known")
end

function image{D, C}(M::Map{D, C}, a)
  if isdefined(M.header, :image)
    return M.header.image(a)::elem_type(C)
  else
    error("No image function known")
  end
end

function show(io::IO, M::InverseMap)
  println(io, "inverse of")
  println(io, " ", M.origin)
end

function inv(a::Map)
  return InverseMap(a)
end

function show(io::IO, M::CoerceMap)
  println(io, "Coerce: $(domain(M)) -> $(codomain(M))")
end

\(f::Map, x) = preimage(f, x)


function change{K, V}(D::Dict{K, V}, k::K, def::V, new::Function)
  i = Base.ht_keyindex(D, k)
  if i>0
    D.vals[i] = new(D.vals[i])
  else
    D[k] = def
  end
end

function inc{K}(D::Dict{K, Int}, k::K, def::Int = 0)
  i = Base.ht_keyindex(D, k)
  if i>0
    D.vals[i] += 1
  else
    D[k] = def
  end
end


function _allow_cache!{D, C, De, Ce}(M::Map, lim::Int, ::Type{D}, ::Type{C}, ::Type{De}, ::Type{Ce})
  if isdefined(M.header, :cache)
    println("Cache already installed")
    return
  end
  M.header.cache = MapCache{D, C, De, Ce}(domain(M), codomain(M), lim)
  old_pr = M.header.preimage
  old_im = M.header.image
  
  if length(methods(M.header.image)) > 1
    println("Cannot do image cache, too many types")
  else
    function im(a::De)
      if haskey(M.header.cache.im, a)
        inc(M.header.cache.imStat, a)
        return M.header.cache.im[a]::Ce
      else
        b = old_im(a)::Ce
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
        b = old_pr(a)::De
        M.header.cache.pr[a] = b
        M.header.cache.prStat[a] = 0
        return b
      end
    end
    M.header.preimage = pr
  end
  nothing
end

function allow_cache!(M::Map, lim::Int = 100)
  return _allow_cache!(M, lim, typeof(domain(M)), typeof(codomain(M)), elem_type(domain(M)), elem_type(codomain(M)))
end

