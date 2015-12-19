function domain(M::Map)
  return M.header.domain
end

function codomain(M::Map)
  return M.header.codomain
end

function image_func(M::Map)
  return M.header.image
end

function preim_func(M::Map)
  return M.header.preim
end

function show(io::IO, M::Map)
  println(io, "Map $(domain(M)) -> $(codomain(M))")
  if isdefined(M.header, :image)
    println(io, " with image")
  end
  if isdefined(M.header, :preim)
    println(io, " with preim")
  end
end

function preimage(M::Map, a::Any)
  if isdefined(M.header, :preim)
    p = M.header.preim(M, a)
    @assert parent(p) == domain(M)
    return p
  end
  throw("no pre-image function known")
end

function image(M::Map, a::Any)
  if isdefined(M.header, :image)
    return M.header.image(M, a)
  end
  throw("no image function known")
end

function Base.call(M::Map, a::Any)
  return image(M, a)
end

function show(io::IO, M::InverseMap)
  println(io, "inverse of")
  println(io, " ", M.a)
end

function inv(a::Map)
  return InverseMap(a)
end

function show(io::IO, M::CoerceMap)
  println(io, "Coerce: $(domain(M)) -> $(codomain(M))")
end
#######################################################
