################################################################################
#
#  Type declaration
#
################################################################################

mutable struct NfRelToNfRelNSMor{T} <: Map{NfRel{T}, NfRelNS{T}, HeckeMap, NfRelToNfRelNSMor}
  header::MapHeader{NfRel{T}, NfRelNS{T}}
  prim_img::NfRelNSElem{T}
  emb::Array{NfRelElem{T}, 1}
  coeff_aut::NfToNfMor

  function NfRelToNfRelNSMor{T}(K::NfRel{T}, L::NfRelNS{T}, a::NfRelNSElem{T}, emb::Array{NfRelElem{T}, 1}) where {T}
    function image(x::NfRelElem{T})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return f(a)
    end

    function preimage(x::NfRelNSElem{T})
      return msubst(x.data, emb)
    end

    z = new{T}()
    z.prim_img = a
    z.coeff_aut = id_hom(base_field(K))
    z.emb = emb
    z.header = MapHeader(K, L, image, preimage)
    return z
  end  

  function NfRelToNfRelNSMor{T}(K::NfRel{T}, L::NfRelNS{T}, a::NfRelNSElem{T}) where T
    function image(x::NfRelElem{T})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return f(a)
    end

    z = new{T}()
    z.prim_img = a
    z.header = MapHeader(K, L, image)
    return z
  end  

  function NfRelToNfRelNSMor{T}(K::NfRel{T}, L::NfRelNS{T}, aut::Map, a::NfRelNSElem{T}) where {T}
    aut = NfToNfMor(domain(aut), codomain(aut), aut(gen(domain(aut))))
    function image(x::NfRelElem{T})
      # x is an element of K
      f = deepcopy(data(x))
      for i=0:degree(f)
        setcoeff!(f, i, aut(coeff(f, i)))
      end
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return f(a)
    end

    z = new{T}()
    z.prim_img = a
    z.coeff_aut = aut
    z.header = MapHeader(K, L, image)
    return z
  end  
end

mutable struct NfToNfRelNSMor <: Map{AnticNumberField, NfRelNS{nf_elem}, HeckeMap, NfToNfRelNSMor}
  header::MapHeader{AnticNumberField, NfRelNS{nf_elem}}
  img_gen::NfRelNSElem{nf_elem}
  preimg_base_field::nf_elem
  preimgs::Vector{nf_elem}
  
  function NfToNfRelNSMor(K::AnticNumberField, L::NfRelNS{nf_elem}, img_gen::NfRelNSElem{nf_elem})
    z = new()
    z.header = MapHeader(K, L)
    z.img_gen = img_gen
    return z
  end
end

mutable struct NfRelNSToNfRelNSMor{T} <: Map{NfRelNS{T}, NfRelNS{T}, HeckeMap, NfRelNSToNfRelNSMor}
  header::MapHeader{NfRelNS{T}, NfRelNS{T}}
  emb::Array{NfRelNSElem{T}, 1}
  coeff_aut::NfToNfMor

  inv_emb::Array{NfRelNSElem{T}, 1}
  inv_coeff_aut::NfToNfMor

  function NfRelNSToNfRelNSMor{T}(K::NfRelNS{T}, L::NfRelNS{T}, emb::Array{NfRelNSElem{T}, 1}) where {T}
    function image(x::NfRelNSElem{T})
      # x is an element of K
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return msubst(x.data, emb)
    end

    z = new{T}()
    z.emb = emb
    z.header = MapHeader(K, L, image)
    return z
  end  

  function NfRelNSToNfRelNSMor{T}(K::NfRelNS{T}, L::NfRelNS{T}, aut::NfToNfMor, emb::Array{NfRelNSElem{T}, 1}) where {T}
    function image(x::NfRelNSElem{T})
      # x is an element of K
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      f = x.data
      Kbxyz = parent(f)
      k = nvars(Kbxyz)
      Lbxyz = PolynomialRing(base_field(L), k, cached = false)[1]
      coeffs = Vector{T}(undef, length(f.coeffs))
      for i = 1:length(coeffs)
        coeffs[i] = aut(f.coeffs[i])
      end
      g = Lbxyz(coeffs, f.exps)
      return msubst(g, emb)
    end

    z = new{T}()
    z.emb = emb
    z.coeff_aut = aut
    z.header = MapHeader(K, L, image)
    return z
  end  
end

################################################################################
#
#  Morphism type
#
################################################################################

morphism_type(K::NfRel{T}, L::NfRelNS{T}) where T = NfRelToNfRelNSMor{T}
morphism_type(K::NfRelNS{T}, L::NfRelNS{T}) where T = NfRelNSToNfRelNSMor{T}

################################################################################
#
#  Constructors
#
################################################################################

function hom(K::NfRel{T}, L::NfRelNS{T}, a::NfRelNSElem{T}) where {T}
  return NfRelToNfRelNSMor{T}(K, L, a)
end

function hom(K::NfRel{T}, L::NfRelNS{T}, a::NfRelNSElem{T}, emb::Array{NfRelElem{T}, 1}) where {T}
  return NfRelToNfRelNSMor{T}(K, L, a, emb)
end

function hom(K::NfRel{nf_elem}, L::NfRelNS{nf_elem}, aut_base::NfToNfMor, a::NfRelNSElem{nf_elem}) 
  return NfRelToNfRelNSMor{nf_elem}(K, L, aut_base, a)
end

function hom(K::NfRelNS{T}, L::NfRelNS{T}, emb::Array{NfRelNSElem{T}, 1}; check = true) where {T}
  f = NfRelNSToNfRelNSMor{T}(K, L, emb)
  if check && T == nf_elem
    @assert isconsistent(f)
  end
  return f
end

function hom(K::NfRelNS{nf_elem}, L::NfRelNS{nf_elem}, emb::Array{NfRelNSElem{nf_elem}, 1}; check = true)
  @assert base_field(K) == base_field(L)
  return hom(K, L, id_hom(base_field(K)), emb, check = check)
end

function hom(K::NfRelNS{nf_elem}, L::NfRelNS{nf_elem}, coeff_aut::NfToNfMor, emb::Array{NfRelNSElem{nf_elem}, 1}; check = true)
  f = NfRelNSToNfRelNSMor{nf_elem}(K, L, coeff_aut, emb)
  if check 
    @assert isconsistent(f)
  end
  return f
end

id_hom(K::NfRelNS{T}) where T = NfRelNSToNfRelNSMor{T}(K, K, id_hom(base_field(K)), gens(K))

################################################################################
#
#  Hash function
#
################################################################################

function Base.hash(f::NfRelNSToNfRelNSMor{T}, u::UInt64) where T
  #I combine the hash functions for the automorphism of the base field and the hash function for the images of the generators.
  a = hash(f.coeff_aut, u)
  for i = 1:length(f.emb)
    a = hash(f.emb[i], a)
  end
  return a
end

function Base.hash(f::NfRelToNfRelMor{T}, u::UInt64) where T
  #I combine the hash functions for the automorphism of the base field and the hash function for the images of the generators.
  a = hash(f.prim_img, u)
  if isdefined(f, :coeff_aut)
    a = hash(f.coeff_aut, a)
  end
  return a
end

################################################################################
#
#  Some consistency check
#
################################################################################

function isconsistent(f::NfRelToNfRelMor{T}) where T
  K = domain(f)
  p = K.pol
  p1 = map_coeffs(f.coeff_aut, p, cached = false)
  if !iszero(p1(f.prim_img))
    error("Wrong")
  end
  return true
end

function isconsistent(f::NfRelNSToNfRelNSMor{T}) where T  
  K = domain(f)
  for i = 1:length(K.pol)
    p = map_coeffs(f.coeff_aut, K.pol[i])
    if !iszero(evaluate(p, f.emb))
      error("wrong!")
    end
  end
  return true
end

################################################################################
#
#  Composition
#
################################################################################

function Base.:(*)(f::NfRelNSToNfRelNSMor{T}, g::NfRelNSToNfRelNSMor{T}) where {T}
  codomain(f) == domain(g) || throw("Maps not compatible")

  a = gens(domain(f))
  return hom(domain(f), codomain(g),  NfRelNSElem{T}[ g(f(x)) for x in a])
end

function Base.:(*)(f::NfRelNSToNfRelNSMor{nf_elem}, g::NfRelNSToNfRelNSMor{nf_elem})
  codomain(f) == domain(g) || throw("Maps not compatible")

  a = gens(domain(f))
  return hom(domain(f), codomain(g), f.coeff_aut * g.coeff_aut, NfRelNSElem{nf_elem}[ g(f(x)) for x in a], check = false)
end

function Base.:(*)(f::NfRelToNfRelMor{nf_elem}, g::NfRelToNfRelNSMor{nf_elem})
  codomain(f) == domain(g) || throw("Maps not compatible")

  a = gen(domain(f))
  return hom(domain(f), codomain(g), f.coeff_aut * g.coeff_aut, g(f(a)))
end

################################################################################
#
#  IsEqual
#
################################################################################

function Base.:(==)(f::NfRelNSToNfRelNSMor{T}, g::NfRelNSToNfRelNSMor{T}) where {T}
  if domain(f) != domain(g) || codomain(f) != codomain(g)
    return false
  end

  L = domain(f)
  K = base_field(L)

  if f.coeff_aut.prim_img != g.coeff_aut.prim_img
    return false
  end

  for i = 1:ngens(L)
    if f.emb[i] != g.emb[i]
      return false
    end
  end

  return true
end

function _compute_preimg(f::NfRelNSToNfRelNSMor{nf_elem})
  inv_base_field = inv(f.coeff_aut)
  L = domain(f)
  K = codomain(f)
  k = base_field(K)
  @assert k == base_field(L)
  B = basis(L)
  M = sparse_matrix(k)
  for i = 1:length(B)
    push!(M, SRow(f(B[i])))
  end
  gK = gens(K)
  imgs = Vector{NfRelNSElem{nf_elem}}(undef, length(gK))
  for i = 1:length(imgs)
    N = SRow(gK[i])
    S = solve(M, N)
    imgs[i] = sum(l*B[j] for (j, l) in S)
  end
  f.inv_coeff_aut = inv_base_field
  f.inv_emb = imgs
  local preimg 
  let f = f
    function preimg(x::NfRelNSElem{nf_elem})
      b = x.data
      b1 = map_coeffs(f.inv_emb, b)
      return msubst(b1, f.inv_emb)
    end
  end
  f.header.preimage = preimg
  return nothing
end

function inv(f::NfRelNSToNfRelNSMor{nf_elem})
  _compute_preimg(f)
  return hom(codomain(f), domain(f), f.inv_coeff_aut, f.inv_emb)
end

@inline ngens(R::Nemo.Generic.MPolyRing) = R.num_vars

function _prod(A, b)
  for a in A
    b = b * a
  end
  return b
end

#aparently, should be called evaluate, talk to Bill...
#definitely non-optimal, in particular for automorphisms
function msubst(f::Generic.MPoly{T}, v::Array{NfRelElem{T}, 1}) where T
  k = base_ring(parent(f))
  n = length(v)
  @assert n == ngens(parent(f))
  r = zero(parent(v[1]))
  L = parent(v[1])
  for i=1:length(f)
    #@show prod(v[j]^f.exps[j, i] for j=1:n)
    s = _prod((v[j]^f.exps[n - j + 1, i] for j=1:n), one(L))
    r += f.coeffs[i]* s
  end
  return r
end
function msubst(f::Generic.MPoly{T}, v::Array{NfRelNSElem{T}, 1}) where T
  k = base_ring(parent(f))
  n = length(v)
  @assert n == ngens(parent(f))
  r = zero(k)
  for i=1:length(f)
    r += f.coeffs[i]*prod(v[j]^f.exps[n - j + 1, i] for j=1:n)
  end
  return r
end

################################################################################
#
#  Permutation group from NfRelNSToNfRelNSMor
#
################################################################################

function _get_poly_from_elem(a::NfRelNSElem{nf_elem}, Qxy)
  K = base_field(parent(a))
  Qx = parent(K.pol)
  p = change_base_ring(a.data, x -> evaluate(Qx(x), gen(Qxy, nvars(Qxy))))
  p1 = evaluate(p, [i for i in 1:ngens(parent(a))], gens(Qxy)[1:end-1])
  res = coeff(p1, [0 for i = 1:nvars(parent(p1))])
  return res
end

function multivariate_from_tower(f::Generic.MPoly{nf_elem}, Qxy)
  M = MPolyBuildCtx(Qxy)
  K = base_ring(f)
  Qx = parent(K.pol)
  cvzip = zip(coeffs(f), exponent_vectors(f))
  for (c, v) in cvzip
    pc = Qx(c)
    for i = degree(pc):-1:0
      cpc = coeff(pc, i)
      if iszero(cpc)
        continue
      end
      vn = vcat(v, i)
      push_term!(M, cpc, vn)
    end
  end
  return finish(M)::fmpq_mpoly
end

function (Rxy::NmodMPolyRing)(f::fmpq_mpoly)
  R = base_ring(Rxy)
  res = change_base_ring(f, x -> divexact(R(numerator(x)), R(denominator(x))), Rxy)
  return res
end

function _get_polys_from_auto(f::NfRelNSToNfRelNSMor{nf_elem}, Qxy)
  res = Vector{elem_type(Qxy)}(undef, nvars(Qxy))
  fK = f.coeff_aut
  ap = fK.prim_img
  K = parent(ap)
  res[nvars(Qxy)] = evaluate(parent(K.pol)(ap), gen(Qxy, nvars(Qxy)))
  for i = 1:nvars(Qxy)-1
    res[i] = multivariate_from_tower(f.emb[i].data, Qxy)
  end
  return res
end

function Base.hash(f::nmod_mpoly, h::UInt)
  return UInt(1)
end

function permutation_group1(G::Vector{NfRelNSToNfRelNSMor{nf_elem}})
  L = domain(G[1])
  K = base_field(L)
  dK = absolute_degree(L)
  d1 = numerator(discriminant(L, FlintQQ))
  p = 2
  while divisible(d1, p)
    p = next_prime(p)
  end
  R = ResidueRing(FlintZZ, p, cached = false)
  Rm, gRm = PolynomialRing(R, ngens(L)+1, cached = false)
  fmod = Vector{nmod_mpoly}(undef, ngens(L)+1)
  RQm, gRQm = PolynomialRing(FlintQQ, ngens(L)+1, cached = false)
  p1 = K.pol
  p1Q = evaluate(p1, gRQm[end])
  fmod[1] = Rm(p1Q)
  for i = 1:ngens(L)
    pp = L.pol[i]
    pp1 = multivariate_from_tower(pp, RQm)
    fmod[i+1] = Rm(pp1)
  end
  permutations = Array{Array{Int, 1},1}(undef, length(G))
  for i = 1:length(G)
    permutations[i] = Vector{Int}(undef, dK)
  end
  pols = Vector{Vector{nmod_mpoly}}(undef, dK)
  pols[1] = gRm
  ind = 2
  gpols = nmod_mpoly[Rm(elel) for elel in _get_polys_from_auto(G[1], RQm)]
  if gpols != gRm
    pols[ind] = gpols
    ind += 1
    gpol = nmod_mpoly[compose_mod(gpols[i], [j for j = 1:nvars(Rm)], pols[2], fmod) for i = 1:length(gpols)]
    while gRm != gpol
      pols[ind] = gpol
      ind += 1
      gpol = nmod_mpoly[compose_mod(gpol[i], [j for j in 1:nvars(Rm)], pols[2], fmod) for i = 1:length(gpols)]
    end
  end
  for i in 2:length(G)
    pi = nmod_mpoly[Rm(x) for x in _get_polys_from_auto(G[i], RQm)]
    if !(pi in pols[1:ind-1])
      previous_order = ind - 1
      pols[ind] = pi
      ind += 1
      for j in 2:previous_order
        pols[ind] = nmod_mpoly[compose_mod(pols[j][s], Int[z for z in 1:nvars(Rm)], pi, fmod) for s = 1:length(pi)]
        ind += 1
      end
      if ind - 1 == dK
        break
      end
      rep_pos = previous_order + 1
      while rep_pos <= ind - 1
        for k in 1:i
          po = nmod_mpoly[Rm(elel) for elel in _get_polys_from_auto(G[k], RQm)]
          att = nmod_mpoly[compose_mod(pols[rep_pos][s], Int[i for i in 1:nvars(Rm)], po, fmod) for s = 1:length(pols[rep_pos])]
          if !(att in pols[1:ind-1])
            pols[ind] = att
            ind += 1
            for j in 2:previous_order
              pols[ind] = nmod_mpoly[compose_mod(pols[j][s], Int[z for z in 1:nvars(Rm)], att, fmod) for s = 1:length(pols[j])]
              ind += 1
            end
            if ind - 1 == dK
              break
            end
          end
        end
        rep_pos = rep_pos + previous_order
      end
    end
  end
  #Now, I have the images mod p
  Dcreation = Vector{Tuple{Vector{nmod_mpoly}, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end

  gen_pols = Vector{nmod_mpoly}[nmod_mpoly[Rm(y) for y in _get_polys_from_auto(x, RQm)] for x in G]
  D = Dict(Dcreation)
  for s = 1:length(G)
    permutations[s][1] = D[gen_pols[s]]
    for i = 2:length(pols)
      permutations[s][i] = D[nmod_mpoly[compose_mod(gen_pols[s][t], Int[i for i in 1:nvars(Rm)], pols[i], fmod) for t = 1:length(gen_pols[s])]]
    end
  end
  return permutations
end


@doc Markdown.doc"""
    compose_mod(a::AbstractAlgebra.MPolyElem{T}, vars::Vector{Int}, vals::Vector{MPolyElem{T}}, mod::Vector{MPolyElem{T}}) where T <: FieldElement
Evaluate the polynomial by substituting in the supplied values in the array `vals` for
the corresponding variables with indices given by the array `vars`. The evaluation will
succeed if multiplication is defined between elements of the coefficient ring of $a$ and
elements of `vals`. The result will be reduced modulo "mod". If "mod" is a Groebner basis for the ideal 
the elements generate. 
"""
function compose_mod(a::S, vars::Vector{Int}, vals::Vector{S}, mod::Vector{S}) where S <:MPolyElem{T} where T <: RingElem
  unique(vars) != vars && error("Variables not unique")
  length(vars) != length(vals) && error("Number of variables does not match number of values")
  for i = 1:length(vars)
    if vars[i] < 1 || vars[i] > nvars(parent(a))
      error("Variable index not in range")
    end
  end
  if length(vars) == 0
    return a
  end
  powers = Dict{Int, S}[Dict{Int, S}() for i in 1:length(vals)]
  return _compose_mod(a, vars, vals, powers, mod)::S
end

function powmod(a::S, i::Union{Int, fmpz}, modu::Vector{S}) where S <:MPolyElem{T} where T <: RingElem
  if i == 0
    return one(parent(a))
  end
  if i == 1
    b = divrem(a, modu)[2]
    return b
  end
  if mod(i, 2) == 0
    j = div(i, 2)
    b = powmod(a, j, modu)
    b = b*b
    b = divrem(b, modu)[2]
    return b
  end
  b = divrem(a * powmod(a, i - 1, modu), modu)[2]
  return b
end

function mulmod(a::S, b::S, mod::Vector{S}) where S <:MPolyElem{T} where T <: RingElem
  return divrem(a*b, mod)[2]
end


function _compose_mod(a, vars, vals, powers, modu)
  S = parent(a)
  r = AbstractAlgebra.Generic.geobucket(S)
  cvzip = zip(coeffs(a), exponent_vectors(a))
  for (c, v) in cvzip
    t = one(S)
    for j = 1:length(vars)
      varnum = vars[j]
      exp = v[varnum]
      if !haskey(powers[j], exp)
        powers[j][exp] = powmod(vals[j], exp, modu)
      end
      t = mulmod(t, powers[j][exp], modu)
      v[varnum] = 0
    end
    M = MPolyBuildCtx(S)
    push_term!(M, c, v)
    push!(r, mulmod(t, finish(M), modu))
  end
  return finish(r)
end


function change_base_ring(p::MPolyElem{T}, g, new_polynomial_ring) where {T <: RingElement}
  cvzip = zip(coeffs(p), exponent_vectors(p))
  M = MPolyBuildCtx(new_polynomial_ring)
  for (c, v) in cvzip
    res = g(c)
    if !iszero(res)
      push_term!(M, g(c), v)
    end
  end
  return finish(M)::elem_type(new_polynomial_ring)
end


function Base.:(*)(f::NfAbsToNfAbsNS, g::NfAbsNSToNfAbsNS)
  @assert codomain(f) == domain(g)
  return hom(domain(f), codomain(g), g(f.prim_img))
end


function Base.:(*)(f::Hecke.NfRelToNfRelNSMor, g::Hecke.NfRelNSToNfRelNSMor)
  return hom(domain(f), codomain(g), g(f(gen(domain(f)))))
end


function Base.:(*)(f::Hecke.NfToNfRel, g::Hecke.NfRelToNfRelNSMor)
  @assert codomain(f) === domain(g)
  return hom(domain(f), codomain(g), g(f(gen(domain(f)))))
end

function hom(K::AnticNumberField, L::NfRelNS{nf_elem}, img_gen::NfRelNSElem{nf_elem})
  return Hecke.NfToNfRelNSMor(K, L, img_gen)
end

function image(f::Hecke.NfToNfRelNSMor, a::nf_elem)
  K = parent(a)
  Qx = parent(K.pol)
  return evaluate(Qx(a), f.img_gen)
end

function preimage(phi::Hecke.NfToNfRelNSMor, a::NfRelNSElem{nf_elem})
  if !isdefined(phi, :preimg_base_field) || !isdefined(phi, :preimgs)
    _compute_preimage(phi)
  end
  f = data(a)
  K = codomain(phi)
  k = base_field(K)
  R = parent(k.pol)
  g = map_coeffs(x -> evaluate(R(x), phi.preimg_base_field), f)
  return evaluate(g, phi.preimgs)
end


function _compute_preimage(f::NfToNfRelNSMor)
  K = domain(f)
  L = codomain(f)
  el = one(L)
  M = zero_matrix(FlintQQ, degree(K), degree(K))
  M[1, 1] = 1
  a = f.img_gen
  for i = 2:degree(K)
    el *= a
    v = absolute_coordinates(el)
    for j = 1:degree(K)
      M[i, j] = v[j]
    end
  end
  N = zero_matrix(FlintQQ, ngens(L)+1, degree(K))
  gk = L(gen(base_field(L)))
  v = absolute_coordinates(gk)
  for j = 1:degree(K)
    N[1, j] = v[j]
  end
  gL = gens(L)
  for i = 1:length(gL)
    v = absolute_coordinates(gL[i])
    for j = 1:degree(K)
      N[i+1, j] = v[j]
    end
  end
  fl, x = can_solve(M, N, side = :left)
  x1, den = _fmpq_mat_to_fmpz_mat_den(x)
  f.preimg_base_field = Nemo.elem_from_mat_row(K, x1, 1, den)
  f.preimgs = Vector{nf_elem}(undef, length(gL))
  for i = 1:length(gL)
    f.preimgs[i] = Nemo.elem_from_mat_row(K, x1, i+1, den)
  end
  return nothing
end


function degrees(L::NfRelNS)
  return Int[total_degree(x) for x in L.pol]
end

function automorphisms(L::NfRelNS{T}) where T
  c = get_special(L, :automorphisms)
  if c !== nothing
    return c
  end
  auts = _automorphisms(L)
  Hecke.set_special(L, :automorphisms => auts)
  return auts
end

function _automorphisms(L::NfRelNS{T}) where T
  roots = Vector{elem_type(L)}[roots(isunivariate(x)[2], L) for x in L.pol]
  auts = Vector{NfRelNSToNfRelNSMor{T}}(undef, prod(length(x) for x in roots))
  ind = 1
  for i in CartesianIndices(Tuple(1:length(roots[i]) for i in 1:length(roots)))
    embs = NfRelNSElem{T}[roots[j][i[j]] for j = 1:length(roots)]
    auts[ind] = hom(L, L, embs)
    ind += 1
  end
  return auts
end
