################################################################################
#
#  Promote rules
#
################################################################################

AbstractAlgebra.promote_rule(::Type{RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}, ::Type{AbsSimpleNumFieldElem}) = RelSimpleNumFieldElem{AbsSimpleNumFieldElem}

AbstractAlgebra.promote_rule(::Type{RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}}, ::Type{AbsSimpleNumFieldElem}) = RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}

AbstractAlgebra.promote_rule(::Type{RelSimpleNumFieldElem{AbsNonSimpleNumFieldElem}}, ::Type{AbsNonSimpleNumFieldElem}) = RelSimpleNumFieldElem{AbsNonSimpleNumFieldElem}

AbstractAlgebra.promote_rule(::Type{RelNonSimpleNumFieldElem{AbsNonSimpleNumFieldElem}}, ::Type{AbsNonSimpleNumFieldElem}) = RelNonSimpleNumFieldElem{AbsNonSimpleNumFieldElem}

AbstractAlgebra.promote_rule(::Type{AbsSimpleNumFieldElem}, ::Type{RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}) = RelSimpleNumFieldElem{AbsSimpleNumFieldElem}

AbstractAlgebra.promote_rule(::Type{AbsSimpleNumFieldElem}, ::Type{RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}}) = RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}

AbstractAlgebra.promote_rule(::Type{AbsNonSimpleNumFieldElem}, ::Type{RelSimpleNumFieldElem{AbsNonSimpleNumFieldElem}}) = RelSimpleNumFieldElem{AbsNonSimpleNumFieldElem}

AbstractAlgebra.promote_rule(::Type{AbsNonSimpleNumFieldElem}, ::Type{RelNonSimpleNumFieldElem{AbsNonSimpleNumFieldElem}}) = RelNonSimpleNumFieldElem{AbsNonSimpleNumFieldElem}

function AbstractAlgebra.promote_rule(::Type{RelNonSimpleNumFieldElem{T}}, ::Type{AbsNonSimpleNumFieldElem}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, AbsNonSimpleNumFieldElem)
    return RelNonSimpleNumFieldElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{RelSimpleNumFieldElem{T}}, ::Type{AbsNonSimpleNumFieldElem}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, AbsNonSimpleNumFieldElem)
    return RelSimpleNumFieldElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{AbsNonSimpleNumFieldElem}, ::Type{RelNonSimpleNumFieldElem{T}}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, AbsNonSimpleNumFieldElem)
    return RelNonSimpleNumFieldElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{AbsNonSimpleNumFieldElem}, ::Type{RelSimpleNumFieldElem{T}}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, AbsNonSimpleNumFieldElem)
    return RelSimpleNumFieldElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{RelNonSimpleNumFieldElem{T}}, ::Type{AbsSimpleNumFieldElem}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, AbsSimpleNumFieldElem)
    return RelNonSimpleNumFieldElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{RelSimpleNumFieldElem{T}}, ::Type{AbsSimpleNumFieldElem}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, AbsSimpleNumFieldElem)
    return RelSimpleNumFieldElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{AbsSimpleNumFieldElem}, ::Type{RelNonSimpleNumFieldElem{T}}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, AbsSimpleNumFieldElem)
    return RelNonSimpleNumFieldElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{AbsSimpleNumFieldElem}, ::Type{RelSimpleNumFieldElem{T}}) where T <: NumFieldElem
  if T === AbstractAlgebra.promote_rule(T, AbsSimpleNumFieldElem)
    return RelSimpleNumFieldElem{T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{RelSimpleNumFieldElem{S}}, ::Type{RelSimpleNumFieldElem{S}}) where S <: NumFieldElem
  return RelSimpleNumFieldElem{S}
end

function AbstractAlgebra.promote_rule(::Type{RelNonSimpleNumFieldElem{S}}, ::Type{RelNonSimpleNumFieldElem{S}}) where S <: NumFieldElem
  return RelNonSimpleNumFieldElem{S}
end

function AbstractAlgebra.promote_rule(::Type{RelSimpleNumFieldElem{S}}, ::Type{RelSimpleNumFieldElem{T}}) where {S <: NumFieldElem, T <: NumFieldElem}
  if S === T
    return RelSimpleNumFieldElem{S}
  end
  U = AbstractAlgebra.promote_rule(S, T)
  if U === T
    return RelSimpleNumFieldElem{T}
  elseif U === S
    return RelSimpleNumFieldElem{S}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{RelNonSimpleNumFieldElem{S}}, ::Type{RelNonSimpleNumFieldElem{T}}) where {S <: NumFieldElem, T <:NumFieldElem}
  if S === T
    return RelNonSimpleNumFieldElem{S}
  end
  U = AbstractAlgebra.promote_rule(S, T)
  if U === T
    return RelNonSimpleNumFieldElem{T}
  elseif U === S
    return RelNonSimpleNumFieldElem{S}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{RelNonSimpleNumFieldElem{S}}, ::Type{RelSimpleNumFieldElem{T}}) where {T <: NumFieldElem, S <: NumFieldElem}
  if T === RelNonSimpleNumFieldElem{S}
    return RelSimpleNumFieldElem{T}
  elseif S === RelSimpleNumFieldElem{T}
    return RelNonSimpleNumFieldElem{S}
  elseif AbstractAlgebra.promote_rule(S, RelSimpleNumFieldElem{T}) === RelSimpleNumFieldElem{T}
    return RelSimpleNumFieldElem{T}
  elseif AbstractAlgebra.promote_rule(T, RelNonSimpleNumFieldElem{S}) == RelNonSimpleNumFieldElem{S}
    return RelNonSimpleNumFieldElem{S}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{RelSimpleNumFieldElem{T}}, ::Type{RelNonSimpleNumFieldElem{S}}) where {T <: NumFieldElem, S <: NumFieldElem}
  if T === RelNonSimpleNumFieldElem{S}
    return RelSimpleNumFieldElem{T}
  elseif S === RelSimpleNumFieldElem{T}
    return RelNonSimpleNumFieldElem{S}
  elseif AbstractAlgebra.promote_rule(S, RelSimpleNumFieldElem{T}) === RelSimpleNumFieldElem{T}
    return RelSimpleNumFieldElem{T}
  elseif AbstractAlgebra.promote_rule(T, RelNonSimpleNumFieldElem{S}) == RelNonSimpleNumFieldElem{S}
    return RelNonSimpleNumFieldElem{S}
  else
    return Union{}
  end
end

################################################################################
#
#  Coercion generic
#
################################################################################

(K::RelSimpleNumField{T})(x::RelSimpleNumFieldElem{T}) where {T <: NumFieldElem} = K(x.data)
(K::RelNonSimpleNumField{T})(x::RelNonSimpleNumFieldElem{T}) where {T <: NumFieldElem} = K(x.data)

function (K::RelSimpleNumField{S})(a::T) where {S <: NumFieldElem, T <: NumFieldElem}
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

function (K::RelNonSimpleNumField{S})(a::T) where {S <: NumFieldElem, T <: NumFieldElem}
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