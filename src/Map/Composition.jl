type CompositeMap <: Map
  header::MapHeader
  a::Map
  b::Map
  function CompositeMap(a::Map, b::Map)
    codomain(a) == domain(b) || throw("maps not compatible")
    r = new()
    r.a = a
    r.b = b
    image = function(M::Map, a::Any)
      return M.a(M.b(a))
    end
    preim = function(M::Map, a::Any)
      return preimage(M.b, preimage(M.a, a))
    end
    r.header = MapHeader(a.header.domain, b.header.codomain, image, preim)
    return r
  end
end

function show(io::IO, M::CompositeMap)
  println(io, "composite of")
  println(io, " ", M.a)
  println(io, "*")
  println(io, " ", M.b)
end

function *(a::Map, b::Map)
  return CompositeMap(a,b)
end

