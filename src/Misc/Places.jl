################################################################################
#
#  Infinite places for number fields
#
#
#  (C) 2017 Tommy Hofmann
#
################################################################################

export iscomplex, ispositive, istotally_positive, signs, sign, real_places,
       complex_places, infinite_places, infinite_place

################################################################################
#
#  Equality and hashing
#
################################################################################

function Base.:(==)(P::InfPlc, Q::InfPlc)
  P.K != Q.K && error("Places are of different number fields")
  return P.i == Q.i
end

function Base.hash(P::InfPlc, h::UInt)
  return xor(Base.hash(P.K, h), Base.hash(P.i, h))
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, P::InfPlc)
  if P.isreal
    print(io, "Real ")
  else
    print(io, "Complex ")
  end

  print(io, "place of \n$(P.K)\n")
  print(io, "corresponding to the root $(P.r)")
end 

################################################################################
#
#  Predicates
#
################################################################################

@doc Markdown.doc"""
    isreal(P::InfPlc) -> Bool

Returns whether the embedding into $\mathbf{C}$ defined by P is real or not.
"""
function Base.isreal(P::InfPlc)
  return P.isreal
end

@doc Markdown.doc"""
    iscomplex(P::InfPlc) -> Bool

Returns whether the embedding into $\mathbf{C}$ defined by P is complex or not.
"""
function iscomplex(P::InfPlc)
  return !isreal(P)
end

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
    infinite_place(K::AnticNumberField, i::Int) -> InfPlc

This function returns the infinite place of $K$ corresponding to the root
`conjugates_arb(a)[i]`, where `a` is the primitive element of $K$.
"""
function infinite_place(K::AnticNumberField, i::Int)
  !(1 <= i <= degree(K)) && error("Index must be between 1 and $(degree(K))")
  return InfPlc(K, i)
end

@doc Markdown.doc"""
    infinite_places(K::AnticNumberField) -> Vector{InfPlc}

This function returns all infinite places of $K$.
"""
function infinite_places(K::AnticNumberField)
  r1, r2 = signature(K)
  return [ InfPlc(K, i) for i in 1:(r1 + r2)]
end

@doc Markdown.doc"""
    real_places(K::AnticNumberField) -> Vector{InfPlc}

This function returns all infinite real places of $K$.
"""
function real_places(K::AnticNumberField)
  r1, r2 = signature(K)
  return [ InfPlc(K, i) for i in 1:r1]
end

@doc Markdown.doc"""
    complex_places(K::AnticNumberField) -> Vector{InfPlc}

This function returns all infinite complex places of $K$.
"""
function complex_places(K::AnticNumberField)
  r1, r2 = signature(K)
  return [ InfPlc(K, i) for i in (r1 + 1):r1 + r2]
end

################################################################################
#
#  Signs at places
#
################################################################################

@doc Markdown.doc"""
    signs(a::nf_elem)          -> Dict{InfPlc, Int}
    signs(a::FacElem{nf_elem}) -> Dict{InfPlc, Int}

This function returns a dictionary of the signs of $a$ at all infinite places
of the ambient number field. The keys are infinite places of the ambient
number field. The value is $1$ if the sign is positive and $-1$ if the sign
is negative.
"""
function signs(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}})
  K = _base_ring(a)
  r1, r2 = signature(K)
  D = Dict{InfPlc, Int}()
  s = _signs(a)
  for i in 1:r1
    P = InfPlc(K, i)
    D[P] = s[i]
  end
  return D
end

@doc Markdown.doc"""
    sign(a::nf_elem, P::InfPlc)          -> Int
    sign(a::FacElem{nf_elem}, P::InfPlc) -> Int

This function returns the sign of $a$ at the place $P$. The value is $1$ if
the sign is positive and $-1$ if the sign is negative.

"""
function sign(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, P::InfPlc)
  !isreal(P) && error("Place must be real")
  return signs(a, [P])[P]
end

@doc Markdown.doc"""
    signs(a::nf_elem, l::Vector{InfPlc})          -> Dict{InfPlc, Int}
    signs(a::FacElem{nf_elem}, l::Vector{InfPlc}) -> Dict{InfPlc, Int}

This function returns a dictionary of the signs of $a$ at places in $l$. The
keys are the elements of $l$. The value is $1$ if the sign is positive and
$-1$ if the sign is negative. The result will contain as many signs as there
are real places contained in $l$.
"""
function signs(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, l::Array{InfPlc, 1})
  K = _base_ring(a)
  r1, r2 = signature(K)
  D = Dict{InfPlc, Int}()
  s = _signs(a)
  for i in 1:r1
    P = InfPlc(K, i)
    if P in l
      D[P] = s[i]
    end
  end
  return D
end

# extend functionality to elements of orders

function signs(a::NfOrdElem, args...)
  return signs(a.elem_in_nf, args...)
end

function sign(a::NfOrdElem, args...)
  return sign(a.elem_in_nf, args...)
end

################################################################################
#
#  Positivity
#
################################################################################

@doc Markdown.doc"""
    ispositive(a::nf_elem, P::InfPlc)          -> Bool
    ispositive(a::FacElem{nf_elem}, P::InfPlc) -> Bool

Returns whether the element $a$ is positive at the embedding corresponding to
$P$. The place $P$ must be real.
"""
function ispositive(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, P::InfPlc)
  !isreal(P) && error("Place must be real")
  return sign(a, P) > 0
end

@doc Markdown.doc"""
    isnegative(a::nf_elem, P::InfPlc)          -> Bool
    isnegative(a::FacElem{nf_elem}, P::InfPlc) -> Bool

Returns whether the element $a$ is negative at the embedding corresponding to
$P$. The place $P$ must be real.
"""
function isnegative(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, P::InfPlc)
  !isreal(P) && error("Place must be real")
  return sign(a, P) < 0
end

@doc Markdown.doc"""
    ispositive(a::nf_elem, l::Vector{InfPlc})          -> Bool
    ispositive(a::FacElem{nf_elem}, l::Vector{InfPlc}) -> Bool

Returns whether the element $a$ is positive at the embeddings corresponding to
the real places of $l$.
"""
function ispositive(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, l::Array{InfPlc, 1})
  return all(x -> ispositive(a, x), (y for y in l if isreal(y)))
end

@doc Markdown.doc"""
    istotally_positive(a::nf_elem)          -> Bool
    istotally_positive(a::FacElem{nf_elem}) -> Bool

Returns whether the element $a$ is totally positive, that is, whether it is
positive at all places of the ambient number field.
"""
function istotally_positive(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}})
  K = _base_ring(a)
  return ispositive(a, real_places(K))
end

# extend functionality to elements of orders

function ispositive(a::NfOrdElem, args...)
  return ispositive(a.elem_in_nf, args...)
end

function istotally_positive(a::NfOrdElem, args...)
  return istotally_positive(a.elem_in_nf, args...)
end

################################################################################
#
#  Action of a morphism on a infinite place
#
################################################################################

#The action of f on P is defined as f(P) = P\circ f^{-1} and not P\circ f
#In this way, (f\circ g)(P)= f(g(P)), otherwise it would fail.

@doc Markdown.doc"""
    induce_image(m::NfToNfMor, P::InfPlc) -> InfPlc
Find a place in the image of $P$ under $m$. If $m$ is an automorphism,
this is unique.
"""
function induce_image(m::NfToNfMor, P::InfPlc)
  k = number_field(P)
  @assert k == domain(m)
  Qx = parent(k.pol)
  if isdefined(m, :prim_preimg)
    h = Qx(m.prim_preimg)
  else
    # I need to invert the map.
    inv_img = _compute_preimg(m)
    h = Qx(inv_img)
  end
  im = h(P.r)
  lp = infinite_places(codomain(m))
  return lp[findfirst(x -> overlaps(lp[x].r, im), 1:length(lp))]
end

function number_field(P::InfPlc)
  return P.K
end

################################################################################
#
#  Uniformizers
#
################################################################################
@doc Markdown.doc"""
    uniformizer(P::InfPlc) -> nf_elem

Returns an element of the field which is positive at $P$ and negative at all the other real places. 
Works only if P is a real place.
"""
function uniformizer(P::InfPlc)
  if iscomplex(P)
    error("The place is complex")
  end
  D = infinite_places_uniformizers(number_field(P))
  return deepcopy(D[P])
end

@doc Markdown.doc"""
    infinite_places_uniformizers(K::AnticNumberField)

Returns a dictionary having as keys the real places of $K$ and the values 
are uniformizers for the corresponding real place.
A uniformizer of a real place P is an element of the field which is negative
at $P$ and positive at all the other real places. 
"""
function infinite_places_uniformizers(K::AnticNumberField; redo::Bool = false)
  if !redo
    try 
      c = _get_places_uniformizers(K)::Dict{InfPlc, nf_elem}
      return c
    catch e
      if !isa(e, AccessorNotSetError)
        rethrow(e)
      end
    end
  end
  p = real_places(K) #Important: I assume these are ordered as the roots of the defining polynomial!
  S = DiagonalGroup([2 for i = 1:length(p)])
  
  let S = S
    function logS(x::Array{Int, 1})
      return S([x[i] > 0 ? 0 : 1 for i=1:length(x)])
    end
  end

  s = Vector{GrpAbFinGenElem}(undef, length(p))
  g = Vector{nf_elem}(undef, length(p))
  ind = 1
  q, mq = quo(S, GrpAbFinGenElem[], false)
  b = 10
  cnt = 0
  while b > 0
    a = rand(K, collect(-b:b))
    if iszero(a)
      continue
    end
    pr = 16
    lc = conjugates(a, pr)
    pr = 16
    done = true
    while true
      for i = 1:length(p)
        if contains(reim(lc[i])[1], 0)
          pr *= 2
          done = false
          break
        end
      end
      if !done
        lc = conjugates(a, pr)
        done = true
      else
        break
      end
    end
    ar = zeros(Int, length(p))
    for i = 1:length(p)
      if ispositive(reim(lc[i])[1])
        ar[i] = 0
      else
        ar[i] = 1
      end
    end
    t = S(ar)
    if !iszero(mq(t))
      s[ind] = t
      g[ind] = a
      ind += 1
      q, mq = quo(S, s[1:ind-1], false)
      if ind > length(p)
        break
      end
    end
    cnt += 1
    if cnt > 1000 
      b *= 2
      cnt = 0
    end
    for i = 1:length(p)
      good = true
      rep = reim(lc[i])[1]
      if ispositive(rep)
        y = -ceil(Int, BigFloat(rep))
      else
        y = -floor(Int, BigFloat(rep))
      end
      ar = zeros(Int, length(p))
      for j = 1:length(p)
        el = reim(lc[j])[1]+y
        if !ispositive(el) && !isnegative(el)
          good = false
          break
        end
        if ispositive(reim(lc[j])[1]+y)
          ar[j] = 0
        else
          ar[j] = 1
        end
      end
      if !good
        continue
      end
      t = S(ar)
      if !iszero(mq(t))
        s[ind] = t
        g[ind] = a + y
        ind += 1
        q, mq = quo(S, s[1:ind-1], false)
        if ind > length(p)
          break
        end
      end
    end
    if ind > length(p)
      break
    end
  end
  if b <= 0
    b = 10
    cnt = 0
    E = EquationOrder(K)
    lllE = lll(E)
    bas = basis(E, K)
    while true
      @assert b>0
      a = rand(bas, 1:b)
      if iszero(a)
        continue
      end
      emb = signs(a, p)
      ar = [0 for i = 1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          ar[i] = 1
        end
      end
      t = S(ar)
      if !iszero(mq(t))
        s[ind] = t
        g[ind] = a
        ind += 1
        q, mq = quo(S, s[1:ind-1], false)
        if ind > length(p)
          break
        end
      else
        cnt += 1
        if cnt > 1000 
          b *= 2
          cnt = 0
        end
      end
    end
  end
  hS = hom(S, S, s)   # Change of coordinates so that the canonical basis elements are mapped to the elements found above
  r = Vector{nf_elem}(undef, length(p))
  hS1 = inv(hS)
  for i = 1:length(p)
    y = hS1(S[i])
    r[i] = prod(g[w]^Int(y[w]) for w = 1:length(p) if !iszero(y[w]))
  end
  D = Dict{InfPlc, nf_elem}()
  for i = 1:length(p)
    D[p[i]] = r[i]
    @hassert :NfOrd 1 sign(r[i], p[i]) == -1
    @hassert :NfOrd 1 all(x -> isone(x), values(signs(r[i], [P for P in p if P != p[i]])))
  end
  _set_places_uniformizers(K, D)
  return D
end

function infinite_primes_map(O::NfOrd, p::Vector{InfPlc}, lying_in::NfOrdIdl)
  K = nf(O)
  D = infinite_places_uniformizers(K)
  
  S = DiagonalGroup([2 for i = 1:length(p)])

  local exp
  let S = S, D = D, p = p, O = O, lying_in = lying_in, K = K
    function exp(A::GrpAbFinGenElem)
      s = one(K)
      if iszero(A)
        return minimum(lying_in)*O(s)
      end  
      for i = 1:length(p)
        if isone(A[i])
          mul!(s, s, D[p[i]])
        end 
      end
      return minimum(lying_in)*O(s)
    end 
  end

  local log
  let S = S, D = D, p = p
    function log(B::T) where T <: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}
      emb = Hecke.signs(B, p)
      res = zeros(Int, length(p))
      for i=1:length(p)
        if emb[p[i]] == -1
          res[i] = 1
        end
      end
      return S(res)
    end 
  end
   
  return S, exp, log
end


