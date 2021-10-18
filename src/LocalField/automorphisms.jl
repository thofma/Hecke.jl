################################################################################
#
#   Roots
#
################################################################################

function roots(f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(f)
  e = absolute_ramification_index(K)
  k, mk = ResidueField(K)
  fk = map_coefficients(mk, f)
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

function refine_roots(f::Generic.Poly{T}, rt::Vector{T}) where T <: Union{padic, qadic, LocalFieldElem}
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


function refine_roots1(f::Generic.Poly{T}, rt::Vector{T}) where T <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(f)
  v = numerator(absolute_ramification_index(K)*valuation(reduced_discriminant(f)))
  target_prec = precision(f)
  starting = minimum(Int[precision(x) for x in rt])  
  chain = [target_prec]
  i = target_prec
  while i > starting
    i = div(i+1, 2)
    pushfirst!(chain, i)
  end
  der = derivative(f)
  wvect = [inv(der(rt[i])) for i = 1:length(rt)]
  rtnew = copy(rt)
  for i in 1:length(chain)
    for j = 1:length(rtnew)
      wvect[j]*f(rtnew[j])
      rtnew[j] = rtnew[j] - wvect[j]*f(rtnew[j])
      wvect[j] = wvect[j]*(2-wvect[j]*der(rtnew[j]))
    end
  end
  return rtnew
end


function _roots(f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(f)
  k, mk = ResidueField(K)
  fk = map_coefficients(mk, f)
  rts = roots(fk)
  x = gen(parent(f))
  #TODO: Is this setprecision call ok?
  r = setprecision(lift(rts[1], K), precision(f))
  pi = uniformizer(K)
  g = f(pi*x+r)
  g = divexact(g, _content(g))
  rtg = roots(g)
  rts = elem_type(K)[setprecision(r, precision(y)) + pi*y for y in rtg]
  return rts
end


function automorphisms(K::T) where T <: Union{LocalField, FlintQadicField}
  rt = roots(defining_polynomial(K), K)
  return morphism_type(K)[hom(K, K, x) for x in rt]
end

function automorphisms(K::LocalField, L::T) where T <: Union{LocalField, FlintQadicField, FlintPadicField}
  return _automorphisms(K, K, L)
end

function absolute_automorphisms(K::LocalField{qadic, S}) where S
  autsk = small_generating_set(automorphisms(base_field(K)))
  auts = morphism_type(K)[]
  for f in autsk
    fnew = map_coefficients(f, defining_polynomial(K))
    rt = roots(fnew, K)
    for x in rt
      push!(auts, hom(K, K, f, x))
    end
  end
  return closure(auts, *)
end

function absolute_automorphisms(K::LocalField)
  return _automorphisms(K, K, absolute_base_field(K))
end

function absolute_automorphisms(K::FlintQadicField)
  return automorphisms(K)
end

function _automorphisms(K::S, F::T, L::U) where {S <: Union{LocalField, FlintQadicField, FlintPadicField}, T <: Union{LocalField, FlintQadicField, FlintPadicField}, U <: Union{LocalField, FlintQadicField, FlintPadicField}}
  if absolute_degree(K) < absolute_degree(L)
    error("The base field is not naturally a subfield!")
  end
  if K == L
    return morphism_type(K, F)[hom(K, F, F(gen(K)))]
  end
  autsk = _automorphisms(base_field(K), F, L)
  auts = morphism_type(K, F)[]
  for f in autsk
    rt = roots(map_coefficients(f, defining_polynomial(K)))
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


function automorphism_group(K::Union{FlintQadicField, LocalField})
  aut = automorphisms(K)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = findfirst(isequal(aut[s]*aut[i]), aut)
    end
  end
  G = GrpGen(mult_table)
  return G, GrpGenToNfMorSet(G, aut, K)
end

@doc Markdown.doc"""
    automorphism_group(L::NumField, K::NumField) -> GenGrp, GrpGenToNfMorSet

Given the number field extension $L$ and $K$, this function returns a group $G$
and a map from $G$ to the automorphisms of $L$ that fix $K$.
"""
function automorphism_group(L::LocalField, K::LocalField)
  aut = automorphisms(L, K)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = findfirst(isequal(aut[s]*aut[i]), aut)
    end
  end
  G = GrpGen(mult_table)
  return G, GrpGenToNfMorSet(G, aut, L)
end

@doc Markdown.doc"""
    absolute_automorphism_group(L::LocalField) -> GenGrp, GrpGenToNfMorSet

Given the local field $L$, this function returns a group $G$
and a map from $G$ to the automorphisms of $L$ over the padics.
"""
function absolute_automorphism_group(L::LocalField)
  aut = absolute_automorphisms(L)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = findfirst(isequal(aut[s]*aut[i]), aut)
    end
  end
  G = GrpGen(mult_table)
  return G, GrpGenToNfMorSet(G, aut, L)
end
