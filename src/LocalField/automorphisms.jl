################################################################################
#
#   Roots
#
################################################################################

function roots(f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  K = base_ring(f)
  e = absolute_ramification_index(K)
  k, mk = residue_field(K)
  fk = map_coefficients(mk, f, cached = false)
  #TODO: We don't need a full Hensel factorization.
  lH = Hensel_factorization(f)
  rt = elem_type(K)[]
  Kx = parent(f)
  for (phi, g) in lH
    if isone(degree(phi))
      if isone(degree(g))
        push!(rt, -constant_coefficient(g)//leading_coefficient(g))
      else
        #TODO: We don't need a full slope factorization.
        lS = slope_factorization(g)
        for (h, mh) in lS
          @assert degree(h) > 0
          if isone(degree(h))
            r = -constant_coefficient(h)//leading_coefficient(h)
            for j = 1:mh
              push!(rt, r)
            end
          elseif iszero(constant_coefficient(h)) || divides(numerator(e*valuation(constant_coefficient(h))), degree(h))[1]
            rth = _roots(h)
            for j = 1:mh
              append!(rt, rth)
            end
          end
        end
      end
    end
  end
  #the roots need to be refined.
  #rt = refine_roots(f, rt)
  return rt
end

function refine_roots(f::Generic.Poly{T}, rt::Vector{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  Rx = parent(f)
  x = gen(Rx)
  factors = typeof(f)[x-y for y in rt]
  push!(factors, divexact(f, prod(factors)))
  factors = lift_factorization(f, factors)
  res = Vector{T}(undef, length(rt))
  for i = 1:length(rt)
    res[i] = -constant_coefficient(factors[i])
  end
  return res
end


function refine_roots1(f::Generic.Poly{T}, rt::Vector{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  K = base_ring(f)
  target_prec = precision(f)
  starting = minimum(Int[precision(x) for x in rt])
  chain = [target_prec]
  i = target_prec
  while i > starting
    i = div(i+1, 2)
    pushfirst!(chain, i)
  end
  der = derivative(f)
  @assert precision(der) >= target_prec
  rtnew = [setprecision(x, target_prec) for x = rt]
  wvect = [(der(rtnew[i])) for i = 1:length(rt)]
  prec_loss = Int(absolute_ramification_index(parent(rt[1]))*maximum(valuation, wvect))
  wvect = map(inv, wvect)
  for i in 1:length(chain)
    for j = 1:length(rtnew)
      rtnew[j] = rtnew[j] - wvect[j]*f(rtnew[j])
      if i < length(chain)
        wvect[j] = wvect[j]*(2-wvect[j]*der(rtnew[j]))
      end
    end
  end
  return [setprecision(x, target_prec - prec_loss) for x= rtnew]
  return rtnew
end

function _roots(f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  @assert degree(f) > 1
  K = base_ring(f)
  k, mk = residue_field(K)
  fk = map_coefficients(mk, f, cached = false)
  rts = roots(fk)
  if length(rts) == 0
    return elem_type(K)[]
  end
  @assert length(rts) == 1
  x = gen(parent(f))
  #TODO: Is this setprecision call ok?
  r = setprecision(lift(rts[1], K), precision(f))
  pi = uniformizer(K)
  g = f(pi*x+r)
  g = divexact(g, _content(g))
  rtg = roots(g)
  rts = elem_type(K)[setprecision(r, precision(y)+1) + pi*y for y in rtg]
  return rts
end

function automorphism_list(K::T) where T <: Union{LocalField, QadicField}
  f = map_coefficients(K, defining_polynomial(K), cached = false)
  rt = roots(f)
  rt = refine_roots1(f, rt)

  return morphism_type(K)[hom(K, K, x) for x in rt]
end

function automorphism_list(K::LocalField, L::T) where T <: Union{LocalField, QadicField, PadicField}
  return _automorphisms(K, K, L)
end

function absolute_automorphism_list(K::LocalField{QadicFieldElem, S}) where S
  autsk = small_generating_set(automorphism_list(base_field(K)))
  auts = morphism_type(K)[]
  for f in autsk
    fnew = map_coefficients(f, defining_polynomial(K), cached = false)
    rt = roots(K, fnew)
    for x in rt
      push!(auts, hom(K, K, f, x))
    end
  end
  return closure(auts, *)
end

function absolute_automorphism_list(K::LocalField)
  return _automorphisms(K, K, absolute_base_field(K))
end

function absolute_automorphism_list(K::QadicField)
  return automorphisms(K)
end


function hom(K::PadicField, F::T; check::Bool = true) where  {T <: Union{LocalField, QadicField, PadicField}}
  z = LocalFieldMor{typeof(K), typeof(F), map_data_type(K, F), map_data_type(K, F)}()
  z.header = MapHeader(K, F)
  z.image_data = map_data(K, F, true)
  return z
end

function _automorphisms(K::PadicField, F::T, L::PadicField) where {T <: Union{LocalField, QadicField, PadicField}}
  z = LocalFieldMor{typeof(K), typeof(F), map_data_type(K, F), map_data_type(K, F)}()
  z.header = MapHeader(K, F)
  z.image_data = map_data(K, F, true)
  return [z]
end

#L-embeddings from K -> F
function _automorphisms(K::S, F::T, L::U) where {S <: Union{LocalField, QadicField}, T <: Union{LocalField, QadicField, PadicField}, U <: Union{LocalField, QadicField, PadicField}}
  if absolute_degree(K) < absolute_degree(L)
    error("The base field is not naturally a subfield!")
  end
  if K == L
    if isa(K, PadicField)
      return morphism_type(K, F)[hom(K, F)]
    else
      return morphism_type(K, F)[hom(K, F, F(gen(K)))]
    end
  end
  autsk = _automorphisms(base_field(K), F, L)
  auts = morphism_type(K, F)[]
  for f in autsk
    fK = map_coefficients(f, defining_polynomial(K), cached = false)
    rt = roots(fK)
    rt = refine_roots1(fK, rt)
    for x in rt
      push!(auts, hom(K, F, f, x))
    end
  end
  return auts
end


function small_generating_set(auts::Vector{T}) where T <: LocalFieldMor
  @assert length(auts) >= 1
  @assert domain(auts[1]) == codomain(auts[1])
  for i = 1:length(auts)
    @assert domain(auts[i]) == codomain(auts[i])
    @assert domain(auts[1]) == domain(auts[i])
  end
  if length(auts) == 1
    return eltype(auts)[x for x in auts]
  end
  return small_generating_set(auts, *, id_hom(domain(auts[1])))
end

################################################################################
#
#   Automorphism group
#
################################################################################


function automorphism_group(K::QadicField)
  aut = automorphism_list(K)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = findfirst(isequal(aut[s]*aut[i]), aut)
    end
  end
  G = MultTableGroup(mult_table)
  return G, GrpGenToNfMorSet(G, aut, K)
end

function gens(L::QadicField, K::PadicField)
  return [gen(L)]
end

function gens(L::LocalField, K::Union{LocalField, PadicField, QadicField} = base_field(L))
  if absolute_degree(K) > absolute_degree(L)
    error("not a subfield")
  end
  g = [gen(L)]
  l = base_field(L)
  if l != K
    append!(g, map(L, gens(l, K)))
  end
  return g
end

@doc raw"""
    automorphism_group(L::LocalField, K::LocalField) -> GenGrp, GrpGenToNfMorSet

Given the extension $L$ and $K$, this function returns a group $G$
and a map from $G$ to the automorphisms of $L$ that fix $K$.
"""
function automorphism_group(L::LocalField, K::Union{LocalField, PadicField, QadicField} = base_field(L))
  aut = automorphism_list(L, K)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  g = gens(L, K)
  rt = [map(x, g) for x = aut]
  for s = 1:length(aut)
    for i = 1:length(aut)
      r = map(aut[i], rt[s])
      p = findfirst(isequal(r), rt)
      if p === nothing
        p = argmax([sum(valuation(x[i]-r[i]) for i=1:length(g)) for x = rt])
      end
      mult_table[s, i] = p
    end
  end
  G = MultTableGroup(mult_table)
  return G, GrpGenToNfMorSet(G, aut, L)
end

@doc raw"""
    absolute_automorphism_group(L::LocalField) -> GenGrp, GrpGenToNfMorSet

Given the local field $L$, this function returns a group $G$
and a map from $G$ to the automorphisms of $L$ over the padics.
"""
function absolute_automorphism_group(L::LocalField)
  aut = absolute_automorphism_list(L)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = findfirst(isequal(aut[s]*aut[i]), aut)
    end
  end
  G = MultTableGroup(mult_table)
  return G, GrpGenToNfMorSet(G, aut, L)
end

################################################################################
#
#  Isomorphism (partially)
#
################################################################################

function is_isomorphic(K::PadicField, L::PadicField)
  if prime(K) != prime(L)
    return false, hom(K, L)
  end
  return true, hom(K, L)
end

function is_isomorphic(K::QadicField, L::QadicField)
  fl, h = is_isomorphic(base_field(K), base_field(L))
  if !fl
    return false, hom(K, L, h, zero(L); check = false)
  end
  foverL = map_coefficients(h, defining_polynomial(K), parent = parent(defining_polynomial(L)))
  r = roots(L, foverL)
  if isempty(r)
    return false, hom(K, L, zero(L); check = false)
  else
    return true, hom(K, L, r[1])
  end
end

function is_isomorphic(K::LocalField, L::LocalField)
  fl, h = is_isomorphic(base_field(K), base_field(L))
  if !fl
    return false, hom(K, L, h, zero(L); check = false)
  end
  foverL = map_coefficients(h, defining_polynomial(K), parent = parent(defining_polynomial(L)))
  r = roots(L, foverL)
  if isempty(r)
    return false, hom(K, L, h, zero(L); check = false)
  else
    return true, hom(K, L, h, r[1])
  end
end
