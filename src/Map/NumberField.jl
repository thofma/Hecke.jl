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
    if degree(L) == 1
      t[1, 1] = coeff(gen(L), 0)
    else
      t[2, 1] = fmpq(1) # coefficient vector of gen(L)
    end

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

#_D = Dict()

function *(f::NfToNfMor, g::NfToNfMor)
#  global _D
#  _s = Base.stacktrace()[2:3]
#  if !(_s in keys(_D))
#    _D[_s] = true
#    println("Called ...")
#    Base.show_backtrace(stdout, Base.stacktrace()[2:3])
#  end
  codomain(f) == domain(g) || throw("Maps not compatible")

  a = gen(domain(f))
  y = g(f(a))

  return NfToNfMor(domain(f), codomain(g), y)
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


function automorphisms(K::AnticNumberField, copyval::Type{Val{T}} = Val{true}) where {T}
  try
    Aut = _get_automorphisms_nf(K)::Vector{NfToNfMor}
    if copyval == Val{true}
      return copy(Aut)
    else 
      return Aut
    end
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
  end
  f = K.pol
  Kt, t = PolynomialRing(K, "t", cached = false)
  f1 = change_ring(f, Kt)
  divpol = Kt(nf_elem[-gen(K), K(1)])
  f1 = divexact(f1, divpol)
  lr = roots(f1, max_roots = div(degree(K), 2))
  Aut1 = Vector{NfToNfMor}(undef, length(lr)+1)
  for i = 1:length(lr)
    Aut1[i] = NfToNfMor(K, K, lr[i])
  end
  Aut1[end] = NfToNfMor(K, K, gen(K))
  auts = closure(Aut1, degree(K))
  _set_automorphisms_nf(K, auts)
  if copyval == Val{true}
    return copy(auts)
  else 
    return auts
  end
end

hom(K::AnticNumberField, L::AnticNumberField, a::nf_elem) = NfToNfMor(K, L, a)
id_hom(K::AnticNumberField) = NfToNfMor(K, K, gen(K))
