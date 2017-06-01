################################################################################
#
#  Infinite places for number fields
#
#
#  (C) 2017 Tommy Hofmann
#
################################################################################

export iscomplex, ispositive, istotally_positive, _signs, _sign, real_places,
       complex_places, infinite_places

################################################################################
#
#  Equality and hashing
#
################################################################################

function Base.:(==)(P::Hecke.InfinitePlace, Q::Hecke.InfinitePlace)
  P.K != Q.K && error("Places are of different number fields")
  return P.i == Q.i
end

function Base.hash(P::Hecke.InfinitePlace, h::UInt)
  return Base.hash(P.K, h) $ Base.hash(P.i, h)
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, P::Hecke.InfinitePlace)
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

doc"""
***
    isreal(P::InfinitePlace) -> Bool

> Returns whether the embedding into $\mathbf{C}$ defined by P is real or not.
"""
function Base.isreal(P::Hecke.InfinitePlace)
  return P.isreal
end

doc"""
***
    iscomplex(P::InfinitePlace) -> Bool

> Returns whether the embedding into $\mathbf{C}$ defined by P is complex or not.
"""
function iscomplex(P::Hecke.InfinitePlace)
  return !isreal(P)
end

################################################################################
#
#  Construction
#
################################################################################

doc"""
***
    infinite_place(K::AnticNumberField, i::Int) -> InfinitePlace

> This function returns the infinite place of $K$ corresponding to the root
> `conjugates_arb(a)[i]`, where `a` is the primitive element of $K$.
"""
function infinite_place(K::AnticNumberField, i::Int)
  !(1 <= i <= degree(K)) && error("Index must be between 1 and $(degree(K))")
  return Hecke.InfinitePlace(K, i)
end

doc"""
***
    infinite_places(K::AnticNumberField) -> Vector{InfinitePlace}

> This function returns all infinite places of $K$.
"""
function infinite_places(K::AnticNumberField)
  r1, r2 = signature(K)
  return [ Hecke.InfinitePlace(K, i) for i in 1:(r1 + r2)]
end

doc"""
***
    real_places(K::AnticNumberField) -> Vector{InfinitePlace}

> This function returns all infinite real places of $K$.
"""
function real_places(K::AnticNumberField)
  r1, r2 = signature(K)
  return [ Hecke.InfinitePlace(K, i) for i in 1:r1]
end

doc"""
***
    real_places(K::AnticNumberField) -> Vector{InfinitePlace}

> This function returns all infinite complex places of $K$.
"""
function complex_places(K::AnticNumberField)
  r1, r2 = signature(K)
  return [ Hecke.InfinitePlace(K, i) for i in (r1 + 1):r2]
end

################################################################################
#
#  Signs at places
#
################################################################################

doc"""
***
    signs(a::nf_elem)          -> Dict{InfinitePlace, Int}
    signs(a::FacElem{nf_elem}) -> Dict{InfinitePlace, Int}

> This function returns a dictionary of the signs of $a$ at all infinite places
> of the ambient number field. The keys are infinite places of the ambient
> number field. The value is $1$ if the sign is positive and $-1$ if the sign
> is negative.
"""
function _signs(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}})
  K = Hecke.base_ring(a)
  r1, r2 = signature(K)
  D = Dict{Hecke.InfinitePlace, Int}()
  s = Hecke.signs(a)
  for i in 1:r1
    P = Hecke.InfinitePlace(K, i)
    D[P] = s[i]
  end
  return D
end

doc"""
***
    sign(a::nf_elem, P::InfinitePlace)          -> Int
    sign(a::FacElem{nf_elem}, P::InfinitePlace) -> Int

> This function returns the sign of $a$ at the place $P$. The value is $1$ if
> the sign is positive and $-1$ if the sign is negative.

"""
function _sign(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, P::Hecke.InfinitePlace)
  !isreal(P) && error("Place must be real")
  return _signs(a, [P])[P]
end

doc"""
***
    signs(a::nf_elem, l::Vector{InfinitePlace})          -> Dict{InfinitePlace, Int}
    signs(a::FacElem{nf_elem}, l::Vector{InfinitePlace}) -> Dict{InfinitePlace, Int}

> This function returns a dictionary of the signs of $a$ at places in $l$. The
> keys are the elements of $l$. The value is $1$ if the sign is positive and
> $-1$ if the sign is negative.
"""
function _signs(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, l::Array{Hecke.InfinitePlace, 1})
  K = Hecke._base_ring(a)
  r1, r2 = signature(K)
  D = Dict{Hecke.InfinitePlace, Int}()
  s = Hecke.signs(a)
  for i in 1:r1
    P = Hecke.InfinitePlace(K, i)
    if P in l
      D[P] = s[i]
    end
  end
  return D
end

# extend functionality to elements of orders

function _signs(a::NfOrdElem, args...)
  return _signs(a.elem_in_nf, args...)
end

function _sign(a::NfOrdElem, args...)
  return _sign(a.elem_in_nf, args...)
end

################################################################################
#
#  Positivity
#
################################################################################

doc"""
***
    ispositive(a::nf_elem, P::InfinitePlace)          -> Bool
    ispositive(a::FacElem{nf_elem}, P::InfinitePlace) -> Bool

> Returns whether the element $a$ is positive at the embedding corresponding to
> $P$. The place $P$ must be real.
"""
function ispositive(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, P::Hecke.InfinitePlace)
  !isreal(P) && error("Place must be real")
  return _sign(a, P) > 0
end

doc"""
***
    ispositive(a::nf_elem, l::Vector{InfinitePlace})          -> Bool
    ispositive(a::FacElem{nf_elem}, l::Vector{InfinitePlace}) -> Bool

> Returns whether the element $a$ is positive at the embeddings corresponding to
> the real places of $l$.
"""
function ispositive(a::Union{nf_elem, FacElem{nf_elem, AnticNumberField}}, l::Array{Hecke.InfinitePlace, 1})
  return all(x -> ispositive(a, x), (y for y in l if isreal(y)))
end

doc"""
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

