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
  cvzip = zip(coefficients(f), exponent_vectors(f))
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

function _get_polys_from_auto(f::NfRelNSToNfRelNSMor_nf_elem, Qxy)
  res = Vector{elem_type(Qxy)}(undef, nvars(Qxy))
  if isdefined(f.image_data.base_field_map_data, :prim_image)
    # ap is a constant, but there is no easy way to coerce to the base field
    ap = f.image_data.base_field_map_data.prim_image.data.coeffs[1]
  else
    ap = gen(base_field(codomain(f)))
  end
  K = base_field(codomain(f))
  res[nvars(Qxy)] = evaluate(parent(K.pol)(ap), gen(Qxy, nvars(Qxy)))
  for i = 1:nvars(Qxy)-1
    res[i] = multivariate_from_tower(image_generators(f)[i].data, Qxy)
  end
  return res
end

function Base.hash(f::nmod_mpoly, h::UInt)
  return UInt(1)
end

function permutation_group1(G::Vector{NfRelNSToNfRelNSMor_nf_elem})
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

function powermod(a::S, i::Union{Int, fmpz}, modu::Vector{S}) where S <:MPolyElem{T} where T <: RingElem
  if i == 0
    return one(parent(a))
  end
  if i == 1
    b = divrem(a, modu)[2]
    return b
  end
  if mod(i, 2) == 0
    j = div(i, 2)
    b = powermod(a, j, modu)
    b = b*b
    b = divrem(b, modu)[2]
    return b
  end
  b = divrem(a * powermod(a, i - 1, modu), modu)[2]
  return b
end

function mulmod(a::S, b::S, mod::Vector{S}) where S <:MPolyElem{T} where T <: RingElem
  return divrem(a*b, mod)[2]
end


function _compose_mod(a, vars, vals, powers, modu)
  S = parent(a)
  r = AbstractAlgebra.Generic.geobucket(S)
  cvzip = zip(coefficients(a), exponent_vectors(a))
  for (c, v) in cvzip
    t = one(S)
    for j = 1:length(vars)
      varnum = vars[j]
      exp = v[varnum]
      if !haskey(powers[j], exp)
        powers[j][exp] = powermod(vals[j], exp, modu)
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
  cvzip = zip(coefficients(p), exponent_vectors(p))
  M = MPolyBuildCtx(new_polynomial_ring)
  for (c, v) in cvzip
    res = g(c)
    if !iszero(res)
      push_term!(M, g(c), v)
    end
  end
  return finish(M)::elem_type(new_polynomial_ring)
end


function Base.:(*)(f::Hecke.NfToNfRel, g::Hecke.NfRelToNfRelNSMor_nf_elem)
  @assert codomain(f) === domain(g)
  return hom(domain(f), codomain(g), g(f(gen(domain(f)))))
end
#
#function hom(K::AnticNumberField, L::NfRelNS{nf_elem}, img_gen::NfRelNSElem{nf_elem})
#  return Hecke.NfToNfRelNSMor(K, L, img_gen)
#end
#
#function image(f::Hecke.NfToNfRelNSMor, a::nf_elem)
#  K = parent(a)
#  Qx = parent(K.pol)
#  return evaluate(Qx(a), f.img_gen)
#end
#
#function preimage(phi::Hecke.NfToNfRelNSMor, a::NfRelNSElem{nf_elem})
#  @assert isdefined(phi, :preimg_base_field) && isdefined(phi, :preimgs)
#  f = data(a)
#  K = codomain(phi)
#  k = base_field(K)
#  R = parent(k.pol)
#  g = map_coefficients(x -> evaluate(R(x), phi.preimg_base_field), f)
#  return evaluate(g, phi.preimgs)
#end
#
#
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
  rts = Vector{elem_type(L)}[roots(isunivariate(x)[2], L) for x in L.pol]
  auts = Vector{morphism_type(L)}(undef, prod(length(x) for x in rts))
  ind = 1
  it = cartesian_product_iterator([1:length(rts[i]) for i in 1:length(rts)], inplace = true)
  for i in it
    embs = NfRelNSElem{T}[rts[j][i[j]] for j = 1:length(rts)]
    auts[ind] = hom(L, L, embs)
    ind += 1
  end
  return auts
end
