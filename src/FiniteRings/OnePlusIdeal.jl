################################################################################
#
#  1 + J as a multiplicative group
#
################################################################################

ideal(OI::OnePlusIdeal) = OI.ideal

function Base.show(io::IO, OI::OnePlusIdeal)
  println(io, "Multiplicative group 1 + the ideal")
  print(io, ideal(OI))
end

function Base.show(io::IO, x::OnePlusIdealElem)
  print(io, data(x))
end

base_ring(I::OnePlusIdeal) = base_ring(ideal(I))

function (OI::OnePlusIdeal)(x)
  @assert parent(x) === base_ring(OI)
  #@assert x - one(algebra(OI)) in ideal(OI)
  return OnePlusIdealElem{typeof(OI.ideal), typeof(x)}(OI, x)
end

parent(x::OnePlusIdealElem) = x.parent

function Base.:(*)(x::OnePlusIdealElem, y::OnePlusIdealElem)
  @assert parent(x) === parent(y)
  return parent(x)(data(x) * data(y))
end

function one(OI::OnePlusIdeal)
  return OI(one(base_ring(OI)))
end

function one(x::OnePlusIdealElem)
  return one(parent(x))
end

function inv(x::OnePlusIdealElem)
  A = base_ring(parent(x))
  J = ideal(parent(x))
  yy = inv(x.elem)
  y = parent(x)(yy)
  @assert x * y == one(parent(x))
  @assert parent(y) === parent(x)
  return y
end

function Base.:(^)(x::OnePlusIdealElem, n::Int)
  return parent(x)(x.elem^n)
end

function Base.:(==)(x::OnePlusIdealElem, y::OnePlusIdealElem)
  @assert parent(x) === parent(y)
  return x.elem == y.elem
end

function Base.rand(R::OnePlusIdeal)
  return R(one(base_ring(ideal(R))) + rand(R.ideal))
end

data(x::OnePlusIdealElem) = x.elem

################################################################################
#
#  (1 + I)/(1 + J)
#
################################################################################

function Base.show(io::IO, OI::OnePlusIdealModuloOnePlusIdeal)
  println(io, "Quotient of")
  println(io, OI.I)
  println(io, "and")
  print(io, OI.J)
end

function Base.show(io::IO, x::OnePlusIdealModuloOnePlusIdealElem)
  print(io, x.elem)
end

parent(x::OnePlusIdealModuloOnePlusIdealElem) = x.parent

function Base.:(*)(x::OnePlusIdealModuloOnePlusIdealElem, y::OnePlusIdealModuloOnePlusIdealElem)
  @assert parent(x) === parent(y)
  z = OnePlusIdealModuloOnePlusIdealElem(x.parent, x.elem + y.elem)
  @assert parent(z) === parent(x)
  return z
end

function (Q::OnePlusIdealModuloOnePlusIdeal)(x::OnePlusIdealElem)
  @assert parent(x) === Q.I
  z = OnePlusIdealModuloOnePlusIdealElem(Q, Q.ItoQ(x.elem - one(base_ring(Q.I))))
  @assert parent(z) === Q
  return z
end

function quo(I::OnePlusIdeal, J::OnePlusIdeal)
  @assert issubset(ideal(I)*ideal(I), ideal(J))
  Q = OnePlusIdealModuloOnePlusIdeal(I, J)
  return Q, OnePlusIdealQuoMap(I, Q, Q.ItoQ)
end

function (f::OnePlusIdealQuoMap)(y::OnePlusIdealElem)
  #@show parent(y).ideal === f.I.ideal
  @assert parent(y) === f.I
  z = f.QQ(y)
  @assert parent(z) === f.QQ
  return z
end

function preimage(f, y::OnePlusIdealModuloOnePlusIdealElem)
  @assert y.parent === f.QQ
  z = f.I((f.ItoQ)\(y.elem) + one(base_ring(f.I)))
  @assert parent(z) === f.I
  return z
end

function Base.:(==)(x::OnePlusIdealModuloOnePlusIdealElem, y::OnePlusIdealModuloOnePlusIdealElem)
  @assert x.parent == y.parent
  return x.elem == y.elem
end

function Base.rand(R::OnePlusIdealModuloOnePlusIdeal)
  return R(rand(R.I))
end
