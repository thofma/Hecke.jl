################################################################################
#
#  NfOrder_elt.jl : Elements in orders of number fields
#
################################################################################

import Base: in

export NfOrderElem

export elem_in_order, rand, rand!

################################################################################
#
#  Types and memory management
#
################################################################################

#type NfOrderElem
#  elem_in_nf::nf_elem
#  elem_in_basis::Array{fmpz, 1}
#  has_coord::Bool
#  parent::NfOrder
#
#  function NfOrderElem(O::NfOrder, a::nf_elem)
#    z = new()
#    z.elem_in_nf = deepcopy(a)
#    z.elem_in_basis = Array(fmpz, degree(O))
#    z.parent = O
#    z.has_coord = false
#    return z
#  end
#
##  function NfOrderElem(O::NfOrder, a::nf_elem, check::Bool)
##    z = new()
##    if check
##      (x,y) = _check_elem_in_order(a,O)
##      !x && error("Number field element not in the order")
##      z.has_coord = true
##      z.elem_in_basis = y
##    end
##    z.elem_in_nf = deepcopy(a)
##    z.parent = O
##    return z
##  end
##
#  function NfOrderElem(O::NfOrder, a::nf_elem, arr::Array{fmpz, 1})
#    z = new()
#    z.parent = O
#    z.elem_in_nf = deepcopy(a)
#    z.has_coord = true
#    z.elem_in_basis = deepcopy(arr)
#    return z
#  end
#
#  function NfOrderElem(O::NfOrder, arr::Array{fmpz, 1})
#    z = new()
#    z.elem_in_nf = Base.dot(basis_nf(O), arr)
#    z.has_coord = true
#    z.elem_in_basis = deepcopy(arr)
#    z.parent = O
#    return z
#  end
#
#  function NfOrderElem{T <: Integer}(O::NfOrder, arr::Array{T, 1})
#    return NfOrderElem(O, map(ZZ, arr))
#  end
#
#  function NfOrderElem(O::NfOrder)
#    z = new()
#    z.parent = O
#    z.elem_in_nf = parent(O).nf()
#    z.elem_in_basis = Array(fmpz, degree(O))
#    z.has_coord = false
#    return z
#  end
#end

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
  if a.has_coord
    return a.elem_in_basis
  else
    (x,y) = _check_elem_in_order(a.elem_in_nf,parent(a))
    !x && error("Number field element not in the order")
    a.elem_in_basis = y
    a.has_coord = true
    return a.elem_in_basis
#  end
    error("Not a valid order element")
  end
end

################################################################################
#
#  Special elements
#
################################################################################

function zero(O::GenNfOrd)
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
 
#function call(O::NfOrder, a::nf_elem, check::Bool = true)
#  if check
#    (x,y) = _check_elem_in_order(a,O)
#    !x && error("Number field element not in the order")
#    return NfOrderElem(O, a, y)
#  else
#    return NfOrderElem(O, a)
#  end
#end
#
#function call(O::NfOrder, a::nf_elem, arr::Array{fmpz, 1})
#  return NfOrderElem(O, a, arr)
#end
#
#function call(O::NfOrder, arr::Array{fmpz, 1})
#  return NfOrderElem(O, arr)
#end
#
#function call{T <: Integer}(O::NfOrder, arr::Array{T, 1})
#  return NfOrderElem(O, arr)
#end
#
#function call(O::NfOrder)
#  return NfOrderElem(O)
#end

################################################################################
#
#  Binary operations
#
################################################################################

function *(x::NfOrderElem, y::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = elem_in_nf(x)*elem_in_nf(y)
  return z
end

function *(x::NfOrderElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf * y
  return z
end

*(x::fmpz, y::NfOrderElem) = y * x

*(x::Integer, y::NfOrderElem) = fmpz(x)* y

*(x::NfOrderElem, y::Integer) = y * x

function +(x::NfOrderElem, y::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  return z
end

function -(x::NfOrderElem, y::NfOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y.elem_in_nf
  return z
end


function +(x::NfOrderElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y
  return z
end

+(x::fmpz, y::NfOrderElem) = y + x

function ^(x::NfOrderElem, y::Int)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf^y
  return z
end

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

function representation_mat(a::NfOrderElem, K::AnticNumberField)
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
  return FlintZZ(trace(elem_in_nf(a)))
end

################################################################################
#
#  Norm
#
################################################################################

function norm(a::NfOrderElem)
  return FlintZZ(norm(elem_in_nf(a)))
end

################################################################################
#
#  Random element generation
#
################################################################################

function rand!{T <: Integer}(z::NfOrderElem, O::GenNfOrd, R::UnitRange{T})
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

function rand{T <: Integer}(O::GenNfOrd, R::UnitRange{T})
  z = O()
  rand!(z, O, R)
  return z
end

function rand!(z::NfOrderElem, O::GenNfOrd, n::Integer)
  return rand!(z, O, -n:n)
end

function rand(O::GenNfOrd, n::Integer)
  return rand(O, -n:n)
end

function rand!(z::NfOrderElem, O::GenNfOrd, n::fmpz)
  return rand!(z, O, BigInt(n))
end

function rand(O::GenNfOrd, n::fmpz)
  return rand(O, BigInt(n))
end
  
################################################################################
#
#  Unsafe operations
#
################################################################################

function add!(z::NfOrderElem, x::NfOrderElem, y::NfOrderElem)
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  if x.has_coord && y.has_coord
    for i in 1:degree(parent(x))
      z.elem_in_basis[i] = x.elem_in_basis[i] + y.elem_in_basis[i]
    end
    z.has_coord = true
  else
    z.has_coord = false
  end
  nothing
end

function mul!(z::NfOrderElem, x::NfOrderElem, y::NfOrderElem)
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
  z.has_coord = false
  nothing
end

function mul!(z::NfOrderElem, x::Integer, y::NfOrderElem)
  mul!(z, ZZ(x), y)
  nothing
end

mul!(z::NfOrderElem, x::NfOrderElem, y::Integer) = mul!(z, y, x)

function mul!(z::NfOrderElem, x::fmpz, y::NfOrderElem)
  z.elem_in_nf = x * y.elem_in_nf
  if y.has_coord
    for i in 1:degree(parent(z))
      z.elem_in_basis[i] = x*y.elem_in_basis[i]
    end
  end
  z.has_coord = true
  nothing
end

function add!(z::NfOrderElem, x::fmpz, y::NfOrderElem)
  z.elem_in_nf = y.elem_in_nf + x
  nothing
end

add!(z::NfOrderElem, x::NfOrderElem, y::fmpz) = add!(z, y, x)

function add!(z::NfOrderElem, x::Integer, y::NfOrderElem)
  z.elem_in_nf = x + y.elem_in_nf
  nothing
end

add!(z::NfOrderElem, x::NfOrderElem, y::Integer) = add!(z, y, x)

mul!(z::NfOrderElem, x::NfOrderElem, y::fmpz) = mul!(z, y, x)

dot(x::fmpz, y::nf_elem) = x*y

dot(x::nf_elem, y::fmpz) = x*y

dot(x::NfOrderElem, y::Int64) = y*x

Base.call(K::AnticNumberField, x::NfOrderElem) = elem_in_nf(x)
