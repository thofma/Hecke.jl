export extend, NfToNfMor, automorphisms

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

function ^(f::NfToNfMor, b::Int)
  K = domain(f)
  @assert K == codomain(f)
  d = degree(K)
  b = mod(b, d)
  if b == 0
    return NfToNfMor(K, K, gen(K))
  elseif b == 1
    return f
  else
    bit = ~((~UInt(0)) >> 1)
    while (UInt(bit) & b) == 0
      bit >>= 1
    end
    z = f
    bit >>= 1
    while bit != 0
      z = z * z
      if (UInt(bit) & b) != 0
        z = z * f
      end
      bit >>= 1
    end
    return z
  end
end

Base.copy(f::NfToNfMor) = f

function show(io::IO, h::NfToNfMor)
  if domain(h) == codomain(h)
    println(io, "Automorphism of ", domain(h))
  else
    println(io, "Injection of ", domain(h), " into ", codomain(h))
  end
  println(io, "defined by ", gen(domain(h)), " -> ", h.prim_img)
end


function automorphisms(K::AnticNumberField)
  try
    Aut = _get_automorphisms_nf(K)
    return copy(Aut)::Vector{NfToNfMor}
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
  end
  f = K.pol
  lr = roots(f, K)
  Aut = Hecke.NfToNfMor[]
  for r in lr
    push!(Aut, Hecke.NfToNfMor(K, K, r))
  end
  _set_automorphisms_nf(K, Aut)
  return copy(Aut)::Vector{NfToNfMor}

end

hom(K::AnticNumberField, L::AnticNumberField, a::nf_elem) = NfToNfMor(K, L, a)
