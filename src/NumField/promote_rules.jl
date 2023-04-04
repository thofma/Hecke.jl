################################################################################
#
#  Promote rules
#
################################################################################

AbstractAlgebra.promote_rule(::Type{S}, ::Type{ZZRingElem}) where S <: NumFieldElem = S

AbstractAlgebra.promote_rule(::Type{ZZRingElem}, ::Type{S}) where S <: NumFieldElem = S

AbstractAlgebra.promote_rule(::Type{S}, ::Type{QQFieldElem}) where S <: NumFieldElem = S

AbstractAlgebra.promote_rule(::Type{QQFieldElem}, ::Type{S}) where S <: NumFieldElem = S

AbstractAlgebra.promote_rule(::Type{T}, ::Type{S}) where {S <: NumFieldElem, T <: Integer} = S

AbstractAlgebra.promote_rule(::Type{S}, ::Type{T}) where {S <: NumFieldElem, T <: Integer} = S

AbstractAlgebra.promote_rule(::Type{NfRelElem{nf_elem}}, ::Type{nf_elem}) = NfRelElem{nf_elem}

AbstractAlgebra.promote_rule(::Type{NfRelNSElem{nf_elem}}, ::Type{nf_elem}) = NfRelNSElem{nf_elem}

AbstractAlgebra.promote_rule(::Type{NfRelElem{NfAbsNSElem}}, ::Type{NfAbsNSElem}) = NfRelElem{NfAbsNSElem}

AbstractAlgebra.promote_rule(::Type{NfRelNSElem{NfAbsNSElem}}, ::Type{NfAbsNSElem}) = NfRelNSElem{NfAbsNSElem}

AbstractAlgebra.promote_rule(::Type{nf_elem}, ::Type{NfRelElem{nf_elem}}) = NfRelElem{nf_elem}

AbstractAlgebra.promote_rule(::Type{nf_elem}, ::Type{NfRelNSElem{nf_elem}}) = NfRelNSElem{nf_elem}

AbstractAlgebra.promote_rule(::Type{NfAbsNSElem}, ::Type{NfRelElem{NfAbsNSElem}}) = NfRelElem{NfAbsNSElem}

AbstractAlgebra.promote_rule(::Type{NfAbsNSElem}, ::Type{NfRelNSElem{NfAbsNSElem}}) = NfRelNSElem{NfAbsNSElem}

function AbstractAlgebra.promote_rule(::Type{NfRelNSElem{T}}, ::Type{NfAbsNSElem}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, NfAbsNSElem)
    return NfRelNSElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfRelElem{T}}, ::Type{NfAbsNSElem}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, NfAbsNSElem)
    return NfRelElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfAbsNSElem}, ::Type{NfRelNSElem{T}}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, NfAbsNSElem)
    return NfRelNSElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfAbsNSElem}, ::Type{NfRelElem{T}}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, NfAbsNSElem)
    return NfRelElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfRelNSElem{T}}, ::Type{nf_elem}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, nf_elem)
    return NfRelNSElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfRelElem{T}}, ::Type{nf_elem}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, nf_elem)
    return NfRelElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{nf_elem}, ::Type{NfRelNSElem{T}}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, nf_elem)
    return NfRelNSElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{nf_elem}, ::Type{NfRelElem{T}}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, nf_elem)
    return NfRelElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfRelElem{S}}, ::Type{NfRelElem{S}}) where S <: NumFieldElem
  return NfRelElem{S}
end

function AbstractAlgebra.promote_rule(::Type{NfRelNSElem{S}}, ::Type{NfRelNSElem{S}}) where S <: NumFieldElem
  return NfRelNSElem{S}
end

function AbstractAlgebra.promote_rule(::Type{NfRelElem{S}}, ::Type{NfRelElem{T}}) where {S <: NumFieldElem, T <: NumFieldElem}
  if S === T
    return NfRelElem{S}
  end
  U = AbstractAlgebra.promote_rule(S, T)
  if U === T
    return NfRelElem{T}
  elseif U === S
    return NfRelElem{S}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfRelNSElem{S}}, ::Type{NfRelNSElem{T}}) where {S <: NumFieldElem, T <:NumFieldElem}
  if S === T
    return NfRelNSElem{S}
  end
  U = AbstractAlgebra.promote_rule(S, T)
  if U === T
    return NfRelNSElem{T}
  elseif U === S
    return NfRelNSElem{S}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfRelNSElem{S}}, ::Type{NfRelElem{T}}) where {T <: NumFieldElem, S <: NumFieldElem}
  if T === NfRelNSElem{S}
    return NfRelElem{T}
  elseif S === NfRelElem{T}
    return NfRelNSElem{S}
  elseif AbstractAlgebra.promote_rule(S, NfRelElem{T}) === NfRelElem{T}
    return NfRelElem{T}
  elseif AbstractAlgebra.promote_rule(T, NfRelNSElem{S}) == NfRelNSElem{S}
    return NfRelNSElem{S}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{NfRelElem{T}}, ::Type{NfRelNSElem{S}}) where {T <: NumFieldElem, S <: NumFieldElem}
  if T === NfRelNSElem{S}
    return NfRelElem{T}
  elseif S === NfRelElem{T}
    return NfRelNSElem{S}
  elseif AbstractAlgebra.promote_rule(S, NfRelElem{T}) === NfRelElem{T}
    return NfRelElem{T}
  elseif AbstractAlgebra.promote_rule(T, NfRelNSElem{S}) == NfRelNSElem{S}
    return NfRelNSElem{S}
  else
    return Union{}
  end
end

################################################################################
#
#  Coercion generic
#
################################################################################

(K::NfRel{T})(x::NfRelElem{T}) where {T <: NumFieldElem} = K(x.data)
(K::NfRelNS{T})(x::NfRelNSElem{T}) where {T <: NumFieldElem} = K(x.data)

function (K::NfRel{S})(a::T) where {S <: NumFieldElem, T <: NumFieldElem}
  if S === T && parent(a) == base_field(K)
    return K(parent(K.pol)(a))
  end
  ET = elem_type(K)
  if AbstractAlgebra.promote_rule(T, ET) !== ET
    return force_coerce_throwing(K, a)
  end
  el = base_field(K)(a)
  return K(el)
end

function (K::NfRelNS{S})(a::T) where {S <: NumFieldElem, T <: NumFieldElem}
  if S === T
    return K(parent(K.pol[1])(a))
  end
  ET = elem_type(K)
  if AbstractAlgebra.promote_rule(T, ET) !== ET
    error("Element not coercible!")
  end
  el = base_field(K)(a)
  return K(el)
end