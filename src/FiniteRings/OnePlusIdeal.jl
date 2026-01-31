Hecke.ideal(OI::OnePlusIdeal) = OI.ideal

Hecke.algebra(OI::OnePlusIdeal) = algebra(ideal(OI))

function Base.show(io::IO, OI::OnePlusIdeal)
  println(io, "Multiplicative group 1 + the ideal")
  print(io, ideal(OI))
end

function Base.show(io::IO, x::OnePlusIdealElem)
  print(io, x.elem)
end

base_ring(I::OnePlusIdeal) = base_ring(ideal(I))

function (OI::OnePlusIdeal)(x)
  @assert parent(x) === base_ring(OI)
  #@assert x - one(algebra(OI)) in ideal(OI)
  return OnePlusIdealElem{typeof(OI.ideal), typeof(x)}(OI, x)
end

Hecke.parent(x::OnePlusIdealElem) = x.parent

function Base.:(*)(x::OnePlusIdealElem, y::OnePlusIdealElem)
  @assert parent(x) === parent(y)
  return parent(x)(x.elem * y.elem)
end

function Hecke.one(OI::OnePlusIdeal)
  return OI(one(base_ring(OI)))
end

function Hecke.one(x::OnePlusIdealElem)
  return one(parent(x))
end

function Hecke.inv(x::OnePlusIdealElem)
  A = base_ring(parent(x))
  J = ideal(parent(x))
  yy = inv(x.elem)
  y = parent(x)(yy)
  @assert x * y == one(parent(x))
  @assert parent(y) === parent(x)
  return y
end

function Base.:(==)(x::OnePlusIdealElem, y::OnePlusIdealElem)
  @assert parent(x) === parent(y)
  return x.elem == y.elem
end

function Base.show(io::IO, OI::OnePlusIdealModuloOnePlusIdeal)
  println(io, "Quotient of")
  println(io, OI.I)
  println(io, "and")
  print(io, OI.J)
end

function Base.show(io::IO, x::OnePlusIdealModuloOnePlusIdealElem)
  print(io, x.elem)
end

Hecke.parent(x::OnePlusIdealModuloOnePlusIdealElem) = x.parent

Base.:(*)(x::OnePlusIdealModuloOnePlusIdealElem, y::OnePlusIdealModuloOnePlusIdealElem) = begin
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

function Base.:(^)(x::OnePlusIdealElem, n::Int)
  return parent(x)(x.elem^n)
end

#function Base.:(*)(x::OnePlusIdealModuloOnePlusIdealElem, y::OnePlusIdealModuloOnePlusIdealElem)
#  @assert x.parent == y.parent
#  return OnePlusIdealModuloOnePlusIdealElem(x.parent, x.elem + y.elem)
#end

function EffectivePresentation(Q::OnePlusIdealModuloOnePlusIdeal)
 A, AtoQQ, QQtoA = isomorphism(FinGenAbGroup, Q.Q)
 AbsA = EffectivePresentation(A)
 AbsQ = EffectivePresentation(Q, AbsA.G,
                      x -> begin
                        @assert parent(x) === Q
                        y = QQtoA(x.elem)
                        @assert parent(y) === A
                        z = AbsA.forward(y)
                        @assert parent(z) === AbsA.G
                        return z
                      end,
                      y -> begin
                        @assert parent(y) === AbsA.G
                        zz = AtoQQ(AbsA.backward(y))
                        @assert parent(zz) === Q.Q
                        return OnePlusIdealModuloOnePlusIdealElem(Q, zz)
                      end)
 for i in 1:10
   y = rand(AbsQ.G)
   z = rand(AbsQ.G)
   @assert AbsQ.forward(AbsQ.backward(y)) == y
   @assert AbsQ.backward(y * z) == AbsQ.backward(y) * AbsQ.backward(z)
 end
 return AbsQ
end

function EffectivePresentation(OI::OnePlusIdeal, originalI = ideal(OI); chain = nothing)
  if is_zero(ideal(OI))
    G = free_group(0)
    return EffectivePresentation(OI, G,
                                x -> one(G),
                                y -> one(OI))
  end
  #A = algebra(OI)
  I = ideal(OI)
  # let's do 1 + I^2 -> 1 + I -> (1 + I)/(1 + I^2) -> 1
  if chain === nothing || chain[1] === nothing
    I2 = I * I
  else
    I2 = chain[1][chain[2]]
    #@assert I2 == I * I
  end
  #I2 = I * originalI
  #OI2 = OnePlusIdeal(I2)
  OI2 = OnePlusIdeal(I2) #originalI)
  Q, f = quo(OI, OI2)
  #@info "Structure of (1 + J)/(1 + J^2): $(elementary_divisors(Q.Q.A))"
  AbsQ = EffectivePresentation(Q)
  if is_zero(I2)
    # need to break the cursion
    # f is an isomorphism
    AbsOI = EffectivePresentation(AbsQ, OI, x -> begin @assert parent(x) === OI; z = f(x); @assert parent(z) === Q; return z end,
                                 y -> preimage(f, y))
    return AbsOI
  else
    AbsOI2 = EffectivePresentation(OI2, originalI; chain = (chain[1], chain[2] + 1))
    #@show AbsOI2.G
    #@info "extending"
    # now construct the extension
    res = extension(AbsOI2, AbsQ, OI,
                       # need to supply all the maps
                       # 1 + J^2 -> 1 + J
                       xx -> begin
                         @assert parent(xx) === OI2
                         return OI(xx.elem)
                       end,
                       # preimage under 1 + J^2 -> 1 + J,
                       x -> begin
                         @assert parent(x) === OI
                         return OI2(x.elem)
                       end,
                       # 1 + J -> (1 + J)/(1 + J^2),
                       x -> begin
                         @assert parent(x) === OI
                         return f(x)
                       end,
                       # preimage under 1 + J -> (1 + J)/(1 + J^2)
                       x -> begin
                         @assert parent(x) === Q
                         return preimage(f, x)
                       end)
    return res
  end
end

################################################################################
#
#  Random
#
################################################################################

function Base.rand(R::OnePlusIdeal)
  return R(one(R.ideal.R) + rand(R.ideal))
end

function Base.rand(R::OnePlusIdealModuloOnePlusIdeal)
  return R(rand(R.I))
end


