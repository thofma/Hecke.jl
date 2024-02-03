################################################################################
#
#  Constructor
#
################################################################################

@doc raw"""
    number_field(f::Vector{PolyRingElem{<:NumFieldElem}}, s::String="_\$", check = true)
                                              -> NumField, Vector{NumFieldElem}

Given a list $f_1, \ldots, f_n$ of univariate polynomials in $K[x]$ over
some number field $K$, constructs the extension $K[x_1, \ldots, x_n]/(f_1(x_1),
\ldots, f_n(x_n))$.

# Examples

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = number_field([x^2 - 2, x^2 - 3], "a")
(Non-simple number field of degree 4 over QQ, AbsNonSimpleNumFieldElem[a1, a2])
```
"""
function _doc_stub_nf2 end

# To work around a bug in the built documentation.
#
abstract type DocuDummy2 end

@doc (@doc _doc_stub_nf2)
number_field(::DocuDummy2)

@doc (@doc _doc_stub_nf2)
number_field(::Vector{<:PolyRingElem{<:Union{NumFieldElem, QQFieldElem}}}, ::String, check::Bool = true)

################################################################################
#
#  Basis
#
################################################################################

@doc raw"""
    basis(L::NonSimpleNumField) -> Vector{NumFieldElem}

Returns the canonical basis of a non-simple extension $L/K$. If
$L = K(a_1,\dotsc,a_n)$ where each $a_i$ has degree $d_i$, then the basis will
be $a_1^{i_1}\dotsm a_d^{i_d}$ with $0 \leq i_j \leq d_j - 1$ for $1 \leq j \leq n$.

# Examples

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, (a1, a2) = number_field([x^2 - 2, x^2 - 3], "a");

julia> basis(K)
4-element Vector{AbsNonSimpleNumFieldElem}:
 1
 a1
 a2
 a1*a2
```
"""
basis(::NonSimpleNumField)

################################################################################
#
#  Defining polynomials
#
################################################################################

@doc raw"""
    defining_polynomials(L::NonSimpleNumField) -> Vector{PolyRingElem}

Given a non-simple number field $L/K$, constructed as $L =
K[x]/(f_1,\dotsc,f_r)$, return the vector containing the $f_i$'s.
"""
defining_polynomials(::NonSimpleNumField)

defining_polynomials(K::RelNonSimpleNumField) = K.abs_pol

defining_polynomials(K::AbsNonSimpleNumField) = K.abs_pol

################################################################################
#
#  Conversion to simple extension
#
################################################################################

@doc raw"""
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
  QQz, z = polynomial_ring(base_field(K), "z")
  for i = 1:length(K.pol)
    v = [zero(QQz) for i in 1:length(K.pol)]
    v[i] = z
    p = evaluate(K.pol[i], v)
    if !is_irreducible(p)
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
    while !is_squarefree(f)
      el += lg[i]
      f = minpoly(el)
    end
    if degree(f) != prod(degree(K.pol[j], j) for j = 1:i)
      return false
    end
    if !is_irreducible(f)
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

@doc raw"""
    component(L::NonSimpleNumField, i::Int) -> SimpleNumField, Map

Given a non-simple extension $L/K$, this function returns the simple number field
corresponding to the $i$-th component of $L$ together with its embedding.
"""
function component(K::NonSimpleNumField, i::Int)
  fl = is_univariate(K.pol[i])
  @assert fl
  kx, _ = polynomial_ring(base_field(K), "x", cached = false)
  g = to_univariate(kx, K.pol[i])
  gK = gens(K)
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
  @assert base_field(K) isa QQField
  @assert is_normal(K)
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
    @assert is_isomorphic(simple_extension(L)[1], K)
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

@doc raw"""
    simplified_simple_extension(L::NonSimpleNumField) -> SimpleNumField, Map

Given a non-simple extension $L/K$, this function returns an isomorphic simple number field
with a "small" defining equation together with the isomorphism.
"""
function simplified_simple_extension(L::NonSimpleNumField; cached::Bool = true, is_abelian::Bool = false)
  OL = maximal_order(L)
  B = lll_basis(OL)
  B1 = _sieve_primitive_elements(B)
  a = B1[1]
  I = t2(a)
  for i = 2:min(50, length(B1))
    J = t2(B1[i])
    if J < I
      a = B1[i]
      I = J
    end
  end
  f = minpoly(a)
  Ls, gLs = number_field(f, cached = cached, check = false)
  mp = hom(Ls, L, a)
  return Ls, mp
end

function simplified_simple_extension(K::AbsNonSimpleNumField; cached::Bool = true, is_abelian::Bool = false)
  OK = maximal_order(K)
  if is_abelian
    OS = _lll_CM(OK)
    OK.lllO = OS
  else
    OS = lll(OK)
  end
  el = _simplify(OS)
  f = minpoly(el)
  L, mL = number_field(f, cached = cached, check = false)
  mp = hom(L, K, el, check = false)
  return L, mp
end
