export extend, NfToNfMor, automorphisms

struct NfMorSet{T}
  field::T
end

function show(io::IO, S::NfMorSet{T}) where {T}
  print(io, "Set of automorphisms of ", S.field)
end

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
  
  function NfToNfMor(K::AnticNumberField, L::AnticNumberField, y::nf_elem, y_inv::nf_elem)
    z = new()
    z.prim_img = y
    z.prim_preimg = y_inv
    
    function _image(x::nf_elem)
      g = parent(K.pol)(x)
      return evaluate(g, y)
    end

    function _preimage(x::nf_elem)
      g = parent(L.pol)(x)
      return evaluate(g, y_inv)
    end

    z.header = MapHeader(K, L, _image, _preimage)
    return z
  end
end

parent(f::NfToNfMor) = NfMorSet(domain(f))

################################################################################
#
#  NfToNfRelMor
#
################################################################################

mutable struct NfToNfRel <: Map{AnticNumberField, NfRel{nf_elem}, HeckeMap, NfToNfRel}
  header::MapHeader{AnticNumberField, NfRel{nf_elem}}

  function NfToNfRel(L::AnticNumberField, K::NfRel{nf_elem}, a::nf_elem, b::nf_elem, c::NfRelElem{nf_elem})
    # let K/k, k absolute number field
    # k -> L, gen(k) -> a
    # K -> L, gen(K) -> b
    # L -> K, gen(L) -> c

    k = K.base_ring
    Ly, y = PolynomialRing(L, cached = false)
    R = parent(k.pol)
    S = parent(L.pol)

    function image(x::nf_elem)
      # x is an element of L
      f = S(x)
      res = evaluate(f, c)
      return res
    end

    function preimage(x::NfRelElem{nf_elem})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      r = Vector{nf_elem}(undef, degree(f) + 1)
      for  i = 0:degree(f)
        r[i+1] = evaluate(R(coeff(f, i)), a)
      end
      return evaluate(Ly(r), b)
    end

    z = new()
    z.header = MapHeader(L, K, image, preimage)
    return z
  end
end

function show(io::IO, h::NfToNfRel)
  println(io, "Morphism between ", domain(h), "\nand ", codomain(h))
end

################################################################################
#
#  Generic groups to set of homomorphisms
#
################################################################################

mutable struct GrpGenToNfMorSet{T} <: Map{GrpGen, NfMorSet{T}, HeckeMap, GrpGenToNfMorSet{T}}
  header::MapHeader{GrpGen, NfMorSet{T}}

  function GrpGenToNfMorSet(G::GrpGen, S::NfMorSet{T}) where {T}
    z = new{T}()
    z.header = MapHeader(G, S)
    return z
  end
end

function GrpGenToNfMorSet(G::GrpGen, K::AnticNumberField)
  return GrpGenToNfMorSet(G, NfMorSet(K))
end

function image(f::GrpGenToNfMorSet, g::GrpGenElem)
  K = codomain(f).field
  return automorphisms(K)[g[]]
end

function (f::GrpGenToNfMorSet)(g::GrpGenElem)
  return image(f, g)
end

function preimage(f::GrpGenToNfMorSet, a::NfToNfMor)
  K = codomain(f).field
  aut = automorphisms(K, copy = false)
  for i in 1:length(aut)
    if a == aut[i]
      return domain(f)[i]
    end
  end
  error("something wrong")
end

function inv(f::NfToNfMor)
  if degree(domain(f)) != degree(codomain(f))
    error("The map is not invertible")
  end
  if isdefined(f, :prim_preimg)
    return hom(codomain(f), domain(f), f.prim_preimg, check = false)
  end
  L = codomain(f)
  K = domain(f)
  M = zero_matrix(FlintQQ, degree(L), degree(L))
  a = f.prim_img
  el = one(L)
  M[1, 1] = 1
  for i = 2:degree(L)
    mul!(el, el, a)
    for j = 1:degree(L)
      M[j, i] = coeff(el, j - 1)
    end
  end
  t = zero_matrix(FlintQQ, degree(L), 1)
  if degree(L) == 1
    t[1, 1] = coeff(gen(L), 0)
  else
    t[2, 1] = fmpq(1) # coefficient vector of gen(L)
  end

  s = solve(M, t)
  img = K(parent(K.pol)([ s[i, 1] for i = 1:degree(K) ]))
  return hom(L, K, img, check = false)
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

function evaluate(f::fmpq_poly, a::nf_elem)
  R = parent(a)
  if iszero(f)
    return zero(R)
  end
  l = length(f) - 1
  s = R(coeff(f, l))
  for i in l-1:-1:0
    #s = s*a + R(coeff(f, i))
    mul!(s, s, a)
    # TODO (easy): Once fmpq_poly_add_fmpq is improved in flint, remove the R(..)
    add!(s, s, R(coeff(f, i)))
  end
  return s
end

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

  return hom(domain(f), codomain(g), y, check = false)
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

function _automorphisms(K::AnticNumberField)
  if degree(K) == 1
    auts = NfToNfMor[hom(K, K, one(K))]
  else
    f = K.pol
    Kt, t = PolynomialRing(K, "t", cached = false)
    f1 = change_ring(f, Kt)
    divpol = Kt(nf_elem[-gen(K), K(1)])
    f1 = divexact(f1, divpol)
    lr = roots(f1, max_roots = div(degree(K), 2))
    Aut1 = Vector{NfToNfMor}(undef, length(lr)+1)
    for i = 1:length(lr)
      Aut1[i] = hom(K, K, lr[i], check = false)
    end
    Aut1[end] = id_hom(K)
    auts = closure(Aut1, degree(K))
  end
end

function automorphisms(K::AnticNumberField; copy::Bool = true)
  try
    Aut = _get_automorphisms_nf(K)::Vector{NfToNfMor}
    if copy 
      return Base.copy(Aut)
    else 
      return Aut
    end
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
  end
  auts = _automorphisms(K)
  _set_automorphisms_nf(K, auts)
  if copy
    return Base.copy(auts)
  else 
    return auts
  end
end

function automorphism_group(K::AnticNumberField)
  aut = automorphisms(K)
  n = degree(K)
  #First, find a good prime
  p = 11
  d = numerator(discriminant(K.pol))
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)
  pols = gfp_poly[Rx(g.prim_img) for g in aut]
  #if g in aut
  #  push!(pols, Rx(g.prim_img))
  #end
  Dcreation = Vector{Tuple{gfp_poly, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end
  D = Dict{gfp_poly, Int}(Dcreation)
  @assert length(D) == n
  mult_table = Array{Int, 2}(undef, n, n)
  #permutations = Array{Array{Int, 1},1}(undef, n)
  for s = 1:n
    #perm = Array{Int, 1}(undef, length(aut))
    for i = 1:length(aut)
      mult_table[s, i] = D[Hecke.compose_mod(pols[s], pols[i], fmod)]
    end
  end
  G = GrpGen(mult_table)
  return G, GrpGenToNfMorSet(G, K)
  #return _perm_to_gap_grp(permutations)
end

function hom(K::AnticNumberField, L::AnticNumberField, a::nf_elem; check::Bool = true, compute_inverse::Bool = false)
 if check
   if !iszero(evaluate(K.pol, a))
     error("The data does not define a homomorphism")
   end
 end
 return NfToNfMor(K, L, a, compute_inverse)
end

function hom(K::AnticNumberField, L::AnticNumberField, a::nf_elem, a_inv::nf_elem; check::Bool = true)
 if check
   if !iszero(evaluate(K.pol, a))
     error("The data does not define a homomorphism")
   end
   if !iszero(evaluate(L.pol, a_inv))
     error("The data does not define a homomorphism")
   end
 end
 return NfToNfMor(K, L, a, a_inv)
end


id_hom(K::AnticNumberField) = hom(K, K, gen(K), check = false)

morphism_type(::Type{AnticNumberField}) = NfToNfMor

isinjective(m::NfToNfMor) = true

issurjective(m::NfToNfMor) = (degree(domain(m)) == degree(codomain(m)))

isbijective(m::NfToNfMor) = issurjective(m)

###############################################################################
#
#  NfToNfMor closure
#
###############################################################################

function closure(S::Vector{NfToNfMor}, final_order::Int = -1)

  K = domain(S[1])
  d = numerator(discriminant(K.pol))
  p = 11
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)

  t = length(S)
  order = 1
  elements = [id_hom(K)]
  pols = gfp_poly[x]
  gpol = Rx(S[1].prim_img)
  if gpol != x
    push!(pols, gpol)
    push!(elements, S[1])
    order += 1

    gpol = compose_mod(gpol, pols[2], fmod)

    while gpol != x
      order = order +1
      push!(elements, S[1]*elements[end])
      push!(pols, gpol)
      gpol = compose_mod(gpol, pols[2], fmod)
    end
  end
  if order == final_order
    return elements
  end

  for i in 2:t
    if !(S[i] in elements)
      pi = Rx(S[i].prim_img)
      previous_order = order
      order = order + 1
      push!(elements, S[i])
      push!(pols, Rx(S[i].prim_img))
      for j in 2:previous_order
        order = order + 1
        push!(pols, compose_mod(pols[j], pi, fmod))
        push!(elements, elements[j]*S[i])
      end
      if order == final_order
        return elements
      end
      rep_pos = previous_order + 1
      while rep_pos <= order
        for k in 1:i
          s = S[k]
          po = Rx(s.prim_img)
          att = compose_mod(pols[rep_pos], po, fmod)
          if !(att in pols)
            elt = elements[rep_pos]*s
            order = order + 1
            push!(elements, elt)
            push!(pols, att)
            for j in 2:previous_order
              order = order + 1
              push!(pols, compose_mod(pols[j], att, fmod))
              push!(elements, elements[j] *elt)
            end
            if order == final_order
              return elements
            end
          end
        end
        rep_pos = rep_pos + previous_order
      end
    end
  end
  return elements
end

function small_generating_set(Aut::Array{NfToNfMor, 1})
  K = domain(Aut[1])
  a = gen(K)
  Identity = Aut[1]
  for i in 1:length(Aut)
    Au = Aut[i]
    if Au.prim_img == a
      Identity = Aut[i]
      break
    end
  end
  return small_generating_set(Aut, *, Identity)
end
