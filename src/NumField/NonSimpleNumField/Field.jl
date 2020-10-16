export component, non_simple_extension

################################################################################
#
#  Constructor
#
################################################################################

@doc Markdown.doc"""
    NumberField(f::Vector{PolyElem{<:NumFieldElem}}, s::String="_\$", check = true)
                                              -> NumField, Vector{NumFieldElem}

Given a list $f_1, \ldots, f_n$ of univariate polynomials in $K[x]$ over
some number field $K$, constructs the extension $K[x_1, \ldots, x_n]/(f_1(x_1),
\ldots, f_n(x_n))$.
"""
NumberField(::Vector{PolyElem{<:Union{NumFieldElem, fmpq}}}, ::String, check::Bool = true)

################################################################################
#
#  Basis
#
################################################################################

@doc Markdown.doc"""
    basis(L::NonSimpleNumField) -> Vector{NumFieldElem}

Returns the canonical basis of a non-simple extension $L/K$. If
$L = K(a_1,\dotsc,a_n)$ where each $a_i$ has degree $d_i$, then the basis will
be $a_1^{i_1}\dotsm a_d^{i_d}$ with $0 \leq i_j d_j - 1$ for $1 \leq j \leq n$.
"""
basis(::NonSimpleNumField)

################################################################################
#
#  Conversion to simple extension
#
################################################################################

@doc Markdown.doc"""
    simple_extension(L::NonSimpleNumField) -> SimpleNumField, Map

Given a non-simple extension $L/K$, this function computes a simple extension
$M/K$ and a $K$-linear isomorphism $M \to L$.
"""
simple_extension(::NonSimpleNumField)

################################################################################
#
#  Check consistency
#
################################################################################

# This is used for the check in the constructor
function _check_consistency(K::NonSimpleNumField)
  QQz, z = PolynomialRing(base_field(K), "z")
  for i = 1:length(K.pol)
    v = [zero(QQz) for i in 1:length(K.pol)]
    v[i] = z
    p = evaluate(K.pol[i], v)
    if !isirreducible(p)
      return false
    end
  end
  lg = gens(K)
  el = lg[1]
  f = minpoly(el)
  d = degree(f)
  for i = 2:length(lg)
    el += lg[i]
    f = minpoly(el)
    while !issquarefree(f)
      el += lg[i]
      f = minpoly(el)
    end
    if degree(f) != prod(degree(K.pol[j], j) for j = 1:i)
      return false
    end
    if !isirreducible(f)
      return false
    end 
  end
  return true
end

################################################################################
#
#  Component
#
################################################################################

@doc Markdown.doc"""
    component(L::NonSimpleNumField, i::Int) -> SimpleNumField, Map

Given a non-simple extension $L/K$, this function returns the simple number field 
corresponding to the $i$-th component of $L$ together with its embedding.
"""
function component(K::NonSimpleNumField, i::Int)
  fl, g = isunivariate(K.pol[i])
  gK = gens(K)
  @assert fl
  Ki, a = number_field(g, cached = false, check = false)
  mp = hom(Ki, K, gK[i])
  return Ki, mp
end

################################################################################
#
#  Non-simplify
#
################################################################################

function non_simple_extension(K::SimpleNumField)
  @assert base_field(K) isa FlintRationalField
  @assert isnormal(K)
  G, mG = automorphism_group(K)
  _subs = _subgroups_for_non_simple_extension(G)
  if length(_subs) == 0
    return [defining_polynomial(K)]
  end
  subf = Dict()
  for (subgrps, indice) in _subs
    for H in subgrps
      if !haskey(subf, H)
        subf[H] = defining_polynomial(fixed_field(K, [mG(H[2](h)) for h in H[1]])[1])
      end
    end
  end

  Qx = Globals.Qx

  l = Inf

  res = nothing

  for (subgrps, indice) in _subs
    v = [ subf[H] for H in subgrps ]
    if length(string(v)) < l
      res = v
    end
    L, = number_field(v)
    @assert isisomorphic(simple_extension(L)[1], K)[1]
  end

  return res
end

function _subgroups_for_non_simple_extension(G, maxorder = div(order(G), 2), maxnum = 5)
  sub = subgroups(G)
  n = order(G)
  res = []
  curmin = 0
  for i in 2:maxnum
    facs = _factorizations(n, i)
    for f in facs
      if curmin < sum(f) && !isempty(res)
        continue
      end

      newmin = sum(map(x -> divexact(n, x), f))

      possible_comb = [ [h for h in sub if order(h[1]) == f[i]] for i in 1:length(f) ]

      for it in Iterators.product(possible_comb...)
        maps = map(x -> x[2], collect(it))
        k = foldl((x, y) -> intersect(x, y)[2], maps)
        if order(domain(k)) != 1
          continue
        end

        if isempty(res)
          push!(res, (collect(it), collect(order.(first.(it)))))
          curmin = newmin
        else
          if newmin < curmin
            empty!(res)
            push!(res, (collect(it), collect(order.(first.(it)))))
            curmin = newmin
          elseif newmin == curmin
            push!(res, (collect(it), collect(order.(first.(it)))))
          end
        end
      end
    end
  end
  if length(res) == 0
    return res
  end
  maxlength = maximum(Int[length(x[2]) for x in res])
  res = [x for x in res if length(x[2]) == maxlength]
  return res
end

function _factorizations(n, parts)
  if parts == 1
    return Vector{Int}[Int[n]]
  end

  res = Vector{Vector{Int}}()
  for k in 2:isqrt(n)
    if mod(n, k) == 0
      nk = divexact(n, k)
      _f = _factorizations(nk, parts - 1)::Vector{Vector{Int}}
      for i in 1:length(_f)
        push!(_f[i], k)
      end
      append!(res, _f)
    end
  end
  res = map(sort!, res)
  return unique!(res)
end

################################################################################
#
#  Simplified simple extension
#
################################################################################


function _simplified_composite(L::NonSimpleNumField; isabelian::Bool = false)
  S, mS = simple_extension(L)
  K, mK = simplify(S)
  return K, mK*mS
end

function _simplified_composite(L::NfRelNS{nf_elem})
  S, mS = simple_extension(L)
  OL = maximal_order(L)
  B = pseudo_basis(OL)
  B1 = Tuple{NfRelElem{nf_elem}, NfOrdFracIdl}[(mS\x, y) for (x, y) in B]
  OS = Order(S, B1)
  OS.disc = OL.disc
  OS.ismaximal = 1
  Hecke._set_maximal_order_of_nf(S, OS)
  K, mK = simplify(S)
  return K, mK*mS
end



function _simplified_composite(L::NfAbsNS; isabelian::Bool = false)
  S, mS = simple_extension(L)
  if isabelian && !istotally_real(S)
    OS = maximal_order(S)
    OS1 = _lll_CM(OS)
    OS.lllO = OS1
  end
  K, mK = simplify(S)
  return K, mK*mS
end


function simplify_components(L::NonSimpleNumField, cp::Vector{Int}; isabelian::Bool = false)
  F, mF = _subfield_of_components(L, cp)
  K, mK = _simplified_composite(F, isabelian = isabelian)
  pols = [K.pol]
  imgs = [mF(mK(gen(K)))]
  for i = 1:ngens(L)
    if i in cp
      continue
    end
    push!(pols, isunivariate(L.pol[i])[2])
    push!(imgs, L[i])
  end
  Lnew, gnew = number_field(pols, check = false)
  mp = hom(Lnew, L, imgs, check = false)
  return Lnew, mp
end

function _subfield_of_components(L::NonSimpleNumField, cp::Vector{Int})
  gL = gens(L)
  pols = [isunivariate(L.pol[i])[2] for i in cp]
  F, gF = number_field(pols, check = false)
  mF = hom(F, L, [gL[i] for i in cp])
  return F, mF
end


@doc Markdown.doc"""
    simplified_simple_extension(L::NonSimpleNumField) -> SimpleNumField, Map

Given a non-simple extension $L/K$, this function returns an isomorphic simple number field 
with a "small" defining equation together with the isomorphism.
"""
function simplified_simple_extension(L::NonSimpleNumField; isabelian::Bool = false)
  L1 = L
  mp = id_hom(L)
  for i = 1:ngens(L1)
    @vprint :Simplify 1 "Simplifying component $i \n"
    L1, mp1 = simplify_components(L1, [i], isabelian = isabelian)
    mp = mp1*mp
  end
  while ngens(L1) > 1
    maxdegs = [0, 0]
    ind = [0, 0]
    for i = 1:ngens(L1)
      td = total_degree(L1.pol[i])
      if td > maxdegs[1]
        if td > maxdegs[2]
          maxdegs[1] = maxdegs[2]
          ind[1] = ind[2]
          maxdegs[2] = td
          ind[2] = i
        else
          maxdegs[1] = td
          ind[1] = i
        end
      end
    end
    @vprint :Simplify 1 "Simplifying components $ind \n"
    if ngens(L1) == 2
      @vprint :Simplify 1 "$L1 \n"
    end
    @vtime :Simplify 1 L1, mp1 = simplify_components(L1, ind, isabelian = isabelian)
    mp = mp1*mp
  end
  L2, mL2 = component(L1, 1)
  mp2 = mL2*mp
  return L2, mp2
end