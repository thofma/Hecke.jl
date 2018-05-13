export extend

mutable struct NfToNfMor <: Map{AnticNumberField, AnticNumberField, HeckeMap, NfToNfMor}
  header::MapHeader{AnticNumberField, AnticNumberField}
  prim_img::nf_elem

  function NfToNfMor()
    z = new()
    z.header = MapHeader()
    return r
  end

  function NfToNfMor(K::AnticNumberField, L::AnticNumberField, y::nf_elem)
    z = new()
    z.prim_img = y

    function image(x::nf_elem)
      g = parent(K.pol)(x)
      return evaluate(g, y)
    end

    z.header = MapHeader(K, L, image)
    return z
  end
end

function Base.:(==)(f::NfToNfMor, g::NfToNfMor)
  if (domain(f) != domain(g)) || (codomain(f) != codomain(g))
    return false
  end

  return f.prim_img == g.prim_img
end

function *(f::NfToNfMor, g::NfToNfMor)
  domain(f) == codomain(g) || throw("Maps not compatible")

  a = gen(domain(g))
  y = f(g(a))

  return NfToNfMor(domain(g), codomain(f), y)
end

function show(io::IO, h::NfToNfMor)
  if domain(h) == codomain(h)
    println(io, "Automorphism of ", domain(h))
  else
    println(io, "Injection of ", domain(h), " into ", codomain(h))
  end
  println(io, "defined by ", gen(domain(h)), " -> ", h.prim_img)
end


function automorphisms(K::AnticNumberField)
  f = K.pol
  lr = roots(f, K)
  Aut = Hecke.NfToNfMor[]
  for r in lr
    push!(Aut, Hecke.NfToNfMor(K, K, r))
  end
  return Aut
end

hom(K::AnticNumberField, L::AnticNumberField, a::nf_elem) = NfToNfMor(K, L, a)
