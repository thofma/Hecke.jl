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
***
    isreal(P::InfPlc) -> Bool

> Returns whether the embedding into $\mathbf{C}$ defined by P is real or not.
"""
function Base.isreal(P::InfPlc)
  return P.isreal
end

@doc Markdown.doc"""
***
    iscomplex(P::InfPlc) -> Bool

> Returns whether the embedding into $\mathbf{C}$ defined by P is complex or not.
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
***
    infinite_place(K::AnticNumberField, i::Int) -> InfPlc

> This function returns the infinite place of $K$ corresponding to the root
> `conjugates_arb(a)[i]`, where `a` is the primitive element of $K$.
"""
function infinite_place(K::AnticNumberField, i::Int)
  !(1 <= i <= degree(K)) && error("Index must be between 1 and $(degree(K))")
  return InfPlc(K, i)
end

@doc Markdown.doc"""
***
    infinite_places(K::AnticNumberField) -> Vector{InfPlc}

> This function returns all infinite places of $K$.
"""
function infinite_places(K::AnticNumberField)
  r1, r2 = signature(K)
  return [ InfPlc(K, i) for i in 1:(r1 + r2)]
end

@doc Markdown.doc"""
***
    real_places(K::AnticNumberField) -> Vector{InfPlc}

> This function returns all infinite real places of $K$.
"""
function real_places(K::AnticNumberField)
  r1, r2 = signature(K)
  return [ InfPlc(K, i) for i in 1:r1]
end

@doc Markdown.doc"""
***
    complex_places(K::AnticNumberField) -> Vector{InfPlc}

> This function returns all infinite complex places of $K$.
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
***
    signs(a::nf_elem)          -> Dict{InfPlc, Int}
    signs(a::FacElem{nf_elem}) -> Dict{InfPlc, Int}

> This function returns a dictionary of the signs of $a$ at all infinite places
> of the ambient number field. The keys are infinite places of the ambient
> number field. The value is $1$ if the sign is positive and $-1$ if the sign
> is negative.
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
***
    sign(a::nf_elem, P::InfPlc)          -> Int
    sign(a::FacElem{nf_elem}, P::InfPlc) -> Int

> This function returns the sign of $a$ at the place $P$. The value is $1$ if
> the sign is positive and $-1$ if the sign is negative.

"""
function sign(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, P::InfPlc)
  !isreal(P) && error("Place must be real")
  return signs(a, [P])[P]
end

@doc Markdown.doc"""
***
    signs(a::nf_elem, l::Vector{InfPlc})          -> Dict{InfPlc, Int}
    signs(a::FacElem{nf_elem}, l::Vector{InfPlc}) -> Dict{InfPlc, Int}

> This function returns a dictionary of the signs of $a$ at places in $l$. The
> keys are the elements of $l$. The value is $1$ if the sign is positive and
> $-1$ if the sign is negative. The result will contain as many signs as there
> are real places contained in $l$.
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
***
    ispositive(a::nf_elem, P::InfPlc)          -> Bool
    ispositive(a::FacElem{nf_elem}, P::InfPlc) -> Bool

> Returns whether the element $a$ is positive at the embedding corresponding to
> $P$. The place $P$ must be real.
"""
function ispositive(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, P::InfPlc)
  !isreal(P) && error("Place must be real")
  return sign(a, P) > 0
end

@doc Markdown.doc"""
***
    ispositive(a::nf_elem, l::Vector{InfPlc})          -> Bool
    ispositive(a::FacElem{nf_elem}, l::Vector{InfPlc}) -> Bool

> Returns whether the element $a$ is positive at the embeddings corresponding to
> the real places of $l$.
"""
function ispositive(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, l::Array{InfPlc, 1})
  return all(x -> ispositive(a, x), (y for y in l if isreal(y)))
end

@doc Markdown.doc"""
***
    istotally_positive(a::nf_elem)          -> Bool
    istotally_positive(a::FacElem{nf_elem}) -> Bool

> Returns whether the element $a$ is totally positive, that is, whether it is
> positive at all places of the ambient number field.
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
    induce_image(P::InfPlc, m::NfToNfMor) -> InfPlc
> Find a place in the image of $P$ under $m$. If $m$ is an automorphism,
> this is unique.
"""
function induce_image(P::InfPlc, m::NfToNfMor)
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


