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
corresponding to the $i$-th component of $L$ togheter with its embedding.
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
  maxlength = maximum(x -> length(x[2]), res)
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
