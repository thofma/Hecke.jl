################################################################################
#
#  NfOrder_elt.jl : Elements in orders of number fields
#
################################################################################

import Base: in

export NfOrderElem

export elem_in_order, random

################################################################################
#
#  Types and memory management
#
################################################################################

type NfOrderElem
  elem_in_nf::nf_elem
  elem_in_basis::Array{fmpz, 1}
  parent::NfOrder

  function NfOrderElem(O::NfOrder, a::nf_elem, check::Bool = true)
    z = new()
    if check
      (x,y) = _check_elem_in_order(a,O)
      !x && error("Number field element not in the order")
      #z.elem_in_basis = y
    end
    z.elem_in_nf = deepcopy(a)
    z.parent = O
    return z
  end

  function NfOrderElem(O::NfOrder, arr::Array{fmpz, 1})
    z = new()
    z.elem_in_nf = Base.dot(basis_nf(O), arr)
    z.parent = O
    return z
  end

  function NfOrderElem{T <: Integer}(O::NfOrder, arr::Array{T, 1})
    return NfOrderElem(O, map(ZZ, arr))
  end

  function NfOrderElem(O::NfOrder)
    z = new()
    z.parent = O
    #z.elem_in_nf = zero(parent(O).nf)
    #z.elem_in_basis = fill!(Array(fmpz, degree(O)), ZZ(0))
    return z
  end
end

#function NfOrderElem!(O::NfOrder, a::nf_elem)
#  z = O()
#  z.elem_in_nf = a
#end

parent(a::NfOrderElem) = a.parent

################################################################################
#
#  Field access
#
################################################################################

function elem_in_nf(a::NfOrderElem)
  if isdefined(a, :elem_in_nf)
    return a.elem_in_nf
  end
#  if isdefined(a, :elem_in_basis)
#    a.elem_in_nf = dot(_basis(O), a.elem_in_basis)
#    return a.elem_in_nf
#  end
  error("Not a valid order element")
end

function elem_in_basis(a::NfOrderElem)
  @vprint :NfOrder 2 "Computing the coordinates of $a\n"
#  if isdefined(a, :elem_in_basis)
#    @vprint :NfOrder 2 "allready definied\n"
#    return a.elem_in_basis
#  end
#  if isdefined(a, :elem_in_nf)
    (x,y) = _check_elem_in_order(a.elem_in_nf,parent(a))
    !x && error("Number field element not in the order")
    a.elem_in_basis = y
    return a.elem_in_basis
#  end
  error("Not a valid order element")
end

################################################################################
#
#  Special elements
#
################################################################################

function zero(O::NfOrder)
  z = O()
  z.elem_in_nf = zero(O.nf)
#  z.elem_in_basis = fill!(Array(fmpz, degree(O)), ZZ(0))
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfOrderElem)
  print(io, a.elem_in_nf)
end

################################################################################
#
#  Parent object overloading
#
################################################################################
 
function Base.call(O::NfOrder, a::nf_elem, check::Bool = true)
  return NfOrderElem(O, a, check)
end

function Base.call(O::NfOrder, arr::Array{fmpz, 1})
  return NfOrderElem(O,arr)
end

function Base.call{T <: Integer}(O::NfOrder, arr::Array{T, 1})
  return NfOrderElem(O,arr)
end

function Base.call(O::NfOrder)
  return NfOrderElem(O)
end

################################################################################
#
#  Binary operations
#
################################################################################

function *(x::NfOrderElem, y::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
  return z
end

function +(x::NfOrderElem, y::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  return z
end

function *(a::NfOrderElem, b::fmpz)
  z = parent(a)()
  z.elem_in_nf = a.elem_in_nf *b
  return z
end

*(a::fmpz, b::NfOrderElem) = b*a

################################################################################
#
#  Modular reduction
#
################################################################################

function mod(a::NfOrderElem, m::fmpz)
  ar = copy(elem_in_basis(a))
  for i in 1:degree(parent(a))
    ar[i] = mod(ar[i],m)
  end
  return parent(a)(ar)
end

==(x::NfOrderElem, y::NfOrderElem) = x.elem_in_nf == y.elem_in_nf
 
################################################################################
#
#  Modular exponentiation
#
################################################################################

function powermod(a::NfOrderElem, i::fmpz, p::fmpz)
  if i == 0 then
    z = parent(a)()
    z.elem_in_nf = one(nf(parent(a)))
    return z
  end
  if i == 1 then
    b = mod(a,p)
    return b
  end
  if mod(i,2) == 0 
    j = div(i,2)
    b = powermod(a, j, p)
    b = b^2
    b = mod(b,p)
    return b
  end
  b = mod(a*powermod(a,i-1,p),p)
  return b
end  

powermod(a::NfOrderElem, i::Integer, p::Integer)  = powermod(a, ZZ(i), ZZ(p))

powermod(a::NfOrderElem, i::fmpz, p::Integer)  = powermod(a, i, ZZ(p))

powermod(a::NfOrderElem, i::Integer, p::fmpz)  = powermod(a, ZZ(i), p)

################################################################################
#
#  Number field element conversion/containment
#
################################################################################

function in(a::nf_elem, O::NfOrder)
  x, = _check_elem_in_order(a::nf_elem, O::NfOrder)
  return x
end

function elem_in_order(a::nf_elem, O::NfOrder)
  (x,y) = _check_elem_in_order(a, O)
  return (x, O(y))
end

################################################################################
#
#  Representation matrices
#
################################################################################

function representation_mat(a::NfOrderElem)
  O = parent(a)
  A = representation_mat(a, parent(a).nf)
  A = basis_mat(O)*A*basis_mat_inv(O)
  !(A.den == 1) && error("Element not in order")
  return A.num
end

function representation_mat(a::NfOrderElem, K::NfNumberField)
  @assert parent(a.elem_in_nf) == K
  d = denominator(a.elem_in_nf)
  b = d*a.elem_in_nf
  A = representation_mat(b)
  z = FakeFmpqMat(A,d)
  return z
end

################################################################################
#
#  Trace
#
################################################################################

function trace(a::NfOrderElem)
  return trace(elem_in_nf(a))
end

################################################################################
#
#  Norm
#
################################################################################

function norm(a::NfOrderElem)
  return norm(elem_in_nf(a))
end

################################################################################
#
#  Random element generation
#
################################################################################

function random!{T <: Integer}(z::NfOrderElem, O::NfOrder, R::UnitRange{T})
  y = O()
  ar = rand(R, degree(O))
  B = basis(O)
  mul!(z, ar[1], B[1])
  for i in 2:degree(O)
    mul!(y, ar[i], B[i])
    add!(z, z, y)
  end
  return z
end

function random{T <: Integer}(O::NfOrder, R::UnitRange{T})
  z = zero(O)
  random!(z, O, R)
  return z
end

function random!(z::NfOrderElem, O::NfOrder, n::Integer)
  return random!(z, O, -n:n)
end

function random(O::NfOrder, n::Integer)
  return random(O, -n:n)
end

function random!(z::NfOrderElem, O::NfOrder, n::fmpz)
  return random!(z, O, BigInt(n))
end

function random(O::NfOrder, n::fmpz)
  return random(O, BigInt(n))
end
  
################################################################################
#
#  Unsafe operations
#
################################################################################

function add!(z::NfOrderElem, x::NfOrderElem, y::NfOrderElem)
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  nothing
end

function mul!(z::NfOrderElem, x::NfOrderElem, y::NfOrderElem)
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
  nothing
end

function mul!(z::NfOrderElem, x::Integer, y::NfOrderElem)
  z.elem_in_nf = ZZ(x) * y.elem_in_nf
  nothing
end

mul!(z::NfOrderElem, x::NfOrderElem, y::Integer) = mul!(z, y, x)

function mul!(z::NfOrderElem, x::fmpz, y::NfOrderElem)
  z.elem_in_nf = x * y.elem_in_nf
  nothing
end

mul!(z::NfOrderElem, x::NfOrderElem, y::fmpz) = mul!(z, y, x)

