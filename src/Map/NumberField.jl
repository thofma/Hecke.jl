export extend, NfToNfMor, automorphisms

mutable struct NfToNfMor <: Map{AnticNumberField, AnticNumberField, HeckeMap, NfToNfMor}
  header::MapHeader{AnticNumberField, AnticNumberField}
  prim_img::nf_elem
  prim_preimg::nf_elem

  function NfToNfMor()
    z = new()
    z.header = MapHeader()
    return r
  end

  function NfToNfMor(K::AnticNumberField, L::AnticNumberField, y::nf_elem, isomorphism::Bool = false)
    z = new()
    z.prim_img = y

    function _image(x::nf_elem)
      g = parent(K.pol)(x)
      return evaluate(g, y)
    end

    if !isomorphism
      z.header = MapHeader(K, L, _image)
      return z
    end

    M = zero_matrix(FlintQQ, degree(L), degree(L))
    b = basis(K)
    for i = 1:degree(L)
      c = _image(b[i])

      for j = 1:degree(L)
        M[j, i] = coeff(c, j - 1)
      end
    end
    t = zero_matrix(FlintQQ, degree(L), 1)
    t[2, 1] = fmpq(1) # coefficient vector of gen(L)

    s = solve(M, t)
    z.prim_preimg = K(parent(K.pol)([ s[i, 1] for i = 1:degree(K) ]))

    function _preimage(x::nf_elem)
      g = parent(L.pol)(x)
      return evaluate(g, z.prim_preimg)
    end

    z.header = MapHeader(K, L, _image, _preimage)
    return z
  end
end

function _compute_preimg(m::NfToNfMor)
  # build the matrix for the basis change
  K = domain(m)
  L = codomain(m)
  M = zero_matrix(FlintQQ, degree(L), degree(L))
  b = basis(K)
  for i = 1:degree(L)
    c = m(b[i])
    for j = 1:degree(L)
      M[j, i] = coeff(c, j - 1)
    end
  end
  t = zero_matrix(FlintQQ, degree(L), 1)
  t[2, 1] = fmpq(1) # coefficient vector of gen(L)
  s = solve(M, t)
  m.prim_preimg = K(parent(K.pol)([ s[i, 1] for i = 1:degree(K) ]))
  return m.prim_preimg
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

Base.hash(f::NfToNfMor, h::UInt) = Base.hash(f.prim_img, h)

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
  Kt, t = PolynomialRing(K, "t", cached = false)
  f1 = evaluate(f, t)
  f1 = divexact(f1, t - gen(K))
  lr = roots(f1, div(degree(K), 2))
  push!(lr, gen(K))
  Aut = Array{NfToNfMor, 1}(undef, length(lr))
  for i = 1:length(lr)
    Aut[i] = NfToNfMor(K, K, lr[i])
  end
  auts = closure(Aut, degree(K))
  _set_automorphisms_nf(K, auts)
  return copy(auts)::Vector{NfToNfMor}

end

hom(K::AnticNumberField, L::AnticNumberField, a::nf_elem) = NfToNfMor(K, L, a)
