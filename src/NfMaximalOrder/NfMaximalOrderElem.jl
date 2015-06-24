export NfMaximalOrderElem

export is_torsion_unit

type NfMaximalOrderElem
  elem_in_nf::nf_elem
  elem_in_basis::Array{fmpz, 1}
  parent::NfMaximalOrder
 
  function NfMaximalOrderElem(O::NfMaximalOrder)
    z = new()
    z.parent = O
    return z
  end
end

################################################################################
#
#  Constructors
#
################################################################################

function NfMaximalOrderElem(O::NfMaximalOrder, x::nf_elem; check::Bool = true )
  if check
    b,v = _check_elem_in_maximal_order(x, O)
    if b
      return O(x,v)
    end
  end
  z = NfMaximalOrderElem(O)
  z.elem_in_nf = x
  return z
end

function NfMaximalOrderElem(O::NfMaximalOrder, x::nf_elem, y::Array{fmpz, 1}; check::Bool = false)
  if !check
    z = NfMaximalOrderElem(O)
    z.elem_in_nf = x
    z.elem_in_basis = y
    return z
  end
end

function NfMaximalOrderElem(O::NfMaximalOrder, x::Array{fmpz, 1})
  z = NfMaximalOrderElem(O)
  z.elem_in_basis = x
  return z
end

function NfMaximalOrderElem{T <: Integer}(O::NfMaximalOrder, x::Array{T, 1})
  return NfMaximalOrderElem(O, map(ZZ, x))
end

# Should I assume that first basis element is 1?
function NfMaximalOrderElem(O::NfMaximalOrder, x::fmpz)
  z = NfMaximalOrderElem(O)
  z.elem_in_nf = nf(O)(x)
  v = fill(ZZ(0), degree(O))
  v[1] = x
  z.elem_in_basis = v
  return z
end

function NfMaximalOrderElem{T <: Integer}(O::NfMaximalOrder, x::T)
  return NfMaximalOrderElem(O, ZZ(x))
end

function zero(O::NfMaximalOrder)
  z = NfMaximalOrderElem(O)
  z.elem_in_nf = zero(nf(O))
  v = fill(ZZ(0), degree(O))
  z.elem_in_basis = v
  return z
end

function one(O::NfMaximalOrder)
  z = NfMaximalOrderElem(O)
  z.elem_in_nf = one(nf(O))
  v = fill(ZZ(0), degree(O))
  v[1] = ZZ(1)
  z.elem_in_basis = v
  return z
end

function copy(x::NfMaximalOrderElem)
  z = parent(x)()
  z.elem_in_nf = deepcopy(x.elem_in_nf)
  return z
end

################################################################################
#
#  Field access
#
################################################################################

parent(x::NfMaximalOrderElem) = x.parent

function elem_in_nf(x::NfMaximalOrderElem)
  if isdefined(x, :elem_in_nf)
    return x.elem_in_nf
  end
  x.elem_in_nf = dot(x.elem_in_basis, basis_nf(parent(x)))
  return x.elem_in_nf
end

function elem_in_basis(x::NfMaximalOrderElem)
#  if isdefined(x, :elem_in_basis)
#    return x.elem_in_basis
#  end
  (b,v) = _check_elem_in_maximal_order(elem_in_nf(x), parent(x))
  x.elem_in_basis = v
  return v
end

################################################################################
#
#  Norm
#
################################################################################

function norm(x::NfMaximalOrderElem)
  return FlintZZ(norm(elem_in_nf(x)))
end

################################################################################
#
#  Trace
#
################################################################################

function trace(x::NfMaximalOrderElem)
  return trace(elem_in_nf(x))
end

################################################################################
#
#  Representation matrix
#
################################################################################

function representation_mat(a::NfMaximalOrderElem)
  O = parent(a)
  A = representation_mat(a, nf(O))
  A = basis_mat(O)*A*basis_mat_inv(O)
  !(A.den == 1) && error("Element not in order")
  return A.num
end

function representation_mat(a::NfMaximalOrderElem, K::NfNumberField)
  @assert nf(parent(a)) == K
  a_nf = elem_in_nf(a)
  d = denominator(a_nf)
  b = d*a_nf
  A = representation_mat(b)
  z = FakeFmpqMat(A,d)
  return z
end


################################################################################
#
#  Parent object overloading
#
################################################################################

function Base.call(O::NfMaximalOrder)
  z = NfMaximalOrderElem(O)
  return z
end

function Base.call(O::NfMaximalOrder, x::nf_elem; check::Bool = true)
  return NfMaximalOrderElem(O, x; check = check)
end

function Base.call(O::NfMaximalOrder, x::nf_elem, y::Array{fmpz, 1})
  return NfMaximalOrderElem(O, x, y)
end

function Base.call(O::NfMaximalOrder, x::Array{fmpz, 1})
  return NfMaximalOrderElem(O, x)
end

function Base.call{T <: Integer}(O::NfMaximalOrder, x::Array{T, 1})
  return NfMaximalOrderElem(O, x)
end

function Base.call(O::NfMaximalOrder, x::fmpz)
  return NfMaximalOrderElem(O, x)
end

function Base.call{T <: Integer}(O::NfMaximalOrder, x::T)
  return NfMaximalOrderElem(O, x)
end
  
################################################################################
#
#  Binary operations
#
################################################################################

function *(x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z = parent(x)()
  z.elem_in_nf = elem_in_nf(x)*elem_in_nf(y)
  return z
end

function *(x::NfMaximalOrderElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf * y
  return z
end

*(x::fmpz, y::NfMaximalOrderElem) = y * x

*(x::Integer, y::NfMaximalOrderElem) = fmpz(x)* y

*(x::NfMaximalOrderElem, y::Integer) = y * x

function +(x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  return z
end

function -(x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf - y.elem_in_nf
  return z
end


function +(x::NfMaximalOrderElem, y::fmpz)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y
  return z
end

+(x::fmpz, y::NfMaximalOrderElem) = y + x

function add!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  nothing
end

function mul!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
  nothing
end

function mul!(z::NfMaximalOrderElem, x::Int, y::NfMaximalOrderElem)
  z.elem_in_nf = x*y.elem_in_nf
  nothing
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::NfMaximalOrderElem)
#  if isdefined(x, :elem_in_basis) && isdefined(x, :elem_in_nf)
    print(io, elem_in_nf(x), " ", elem_in_basis(x))
#  elseif isdefined(x, :elem_in_basis)
#    print(io, x.elem_in_basis)
#  else
#    print(io, x.elem_in_nf)
#  end
end

################################################################################
#
#  Random elements
#
################################################################################

function rand(O::NfMaximalOrder, r::UnitRange{Int})
  ar = basis(O)
  s = zero(O)
  t = zero(O)
  for i in 1:degree(O)
    mul!(t, rand(r), ar[i])
    add!(s, s, t)
  end
  return s
end

function rand!(z::NfMaximalOrderElem, O::NfMaximalOrder, r::UnitRange{Int})
  ar = basis(O)
  t = O()
  mul!(z, rand(r), ar[1])
  for i in 2:degree(O)
    mul!(t, rand(r), ar[i])
    add!(z, z, t)
  end
end

################################################################################
#
#  Reduction
#
################################################################################

function mod(a::NfMaximalOrderElem, m::Int)
  O = parent(a)
  z = O()
  v = fill(ZZ(0), degree(O))
  ar = elem_in_basis(a)
  for i in 1:degree(O)
    v[i] = ar[i] % m
  end
  return O(v)
end


################################################################################
#
#  Random element generation
#
################################################################################

function random!{T <: Integer}(z::NfMaximalOrderElem, O::NfMaximalOrder, R::UnitRange{T})
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

function random{T <: Integer}(O::NfMaximalOrder, R::UnitRange{T})
  z = zero(O)
  random!(z, O, R)
  return z
end

function random!(z::NfMaximalOrderElem, O::NfMaximalOrder, n::Integer)
  return random!(z, O, -n:n)
end

function random(O::NfMaximalOrder, n::Integer)
  return random(O, -n:n)
end

function random!(z::NfMaximalOrderElem, O::NfMaximalOrder, n::fmpz)
  return random!(z, O, BigInt(n))
end

function random(O::NfMaximalOrder, n::fmpz)
  return random(O, BigInt(n))
end
  
################################################################################
#
#  Unsafe operations
#
################################################################################

function add!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  nothing
end

function mul!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
  nothing
end

function mul!(z::NfMaximalOrderElem, x::Integer, y::NfMaximalOrderElem)
  z.elem_in_nf = ZZ(x) * y.elem_in_nf
  nothing
end

mul!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::Integer) = mul!(z, y, x)

function mul!(z::NfMaximalOrderElem, x::fmpz, y::NfMaximalOrderElem)
  z.elem_in_nf = x * y.elem_in_nf
  nothing
end

mul!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::fmpz) = mul!(z, y, x)

################################################################################
#
#  Conversion
#
################################################################################

Base.call(K::NfNumberField, x::NfMaximalOrderElem) = elem_in_nf(x)

################################################################################
#
#  Torsion units
#
################################################################################

function is_torsion_unit(x::NfMaximalOrderElem)
  !is_unit(x) && return false
  # test for the signature etc
  O = parent(x)
  d = degree(O)
  # round down should be mode 3 (right?)
  Rarb = ArbField(32)
  Rd = Rarb(d)
  t = (log(Rd)/d^2)/24
  while !ispositive(t)
     Rarb = ArbField(2*Rarb.prec)
     Rd = Rarb(d)
     t = (log(Rd)/d^2)/24
  end
  Rarf = ArfField(Rarb.prec)
  z = Rarf()
  ccall((:arb_get_abs_lbound_arf, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, t.data, Rarb.prec)
  @hassert :NfMaximalOrder 1 sign(z) == 1
  zz = 1 + (log(Rd)/d^2)/12
  i = ccall((:arf_cmpabs_mag, :libarb), Cint, (Ptr{Void}, Ptr{Void}), z.data, radius(zz).data)
  f = nf(parent(x)).pol
  Zf = PolynomialRing(FlintZZ,"x")[1](f) 
  c = complex_roots(Zf, target_prec = Rarb.prec)
  for j in 1:length(c)
    r = parent(c[1])(0)
    for k in 1:degree(O)
      r = r + parent(c[1])(coeff(elem_in_nf(x), k))*c[j]^k
    end
    s = abs(r)
    assert(ccall((:arf_cmpabs_mag, :libarb), Cint, (Ptr{Void}, Ptr{Void}), z.data, radius(s).data) == 1)
    if compare(midpoint(s), midpoint(zz)) == 1
      return false
    end
  end
  return true
end

function mod(a::NfMaximalOrderElem, m::fmpz)
  ar = elem_in_basis(a)
  for i in 1:degree(parent(a))
    ar[i] = mod(ar[i],m)
  end
  return parent(a)(ar)
end


################################################################################
#
#  Modular exponentiation
#
################################################################################

function ^(a::NfMaximalOrderElem, i::Int)
  if i == 0 then
    z = parent(a)()
    z.elem_in_nf = one(nf(parent(a)))
    return z
  end
  if i == 1 then
    return copy(a)
  end
  if mod(i,2) == 0 
    j = div(i,2)
    b = a^j
    b = b*b
    return b
  end
  b = a*a^(i-1)
  return b
end  

function powermod(a::NfMaximalOrderElem, i::fmpz, p::fmpz)
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
    b = b*b
    b = mod(b,p)
    return b
  end
  b = mod(a*powermod(a,i-1,p),p)
  return b
end  

powermod(a::NfMaximalOrderElem, i::Integer, p::Integer)  = powermod(a, ZZ(i), ZZ(p))

powermod(a::NfMaximalOrderElem, i::fmpz, p::Integer)  = powermod(a, i, ZZ(p))

powermod(a::NfMaximalOrderElem, i::Integer, p::fmpz)  = powermod(a, ZZ(i), p)

function is_unit(x::NfMaximalOrderElem)
  return inv(elem_in_nf(x)) in parent(x)
end

dot(x::fmpz, y::nf_elem) = x*y

dot(x::NfMaximalOrderElem, y::Int64) = y*x

function add!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
  nothing
end

function add!(z::NfMaximalOrderElem, x::fmpz, y::NfMaximalOrderElem)
  z.elem_in_nf = y.elem_in_nf + x
  nothing
end

add!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::fmpz) = add!(z, y, x)

function add!(z::NfMaximalOrderElem, x::Integer, y::NfMaximalOrderElem)
  z.elem_in_nf = x + y.elem_in_nf
  nothing
end

add!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::Integer) = add!(z, y, x)

function mul!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
  nothing
end

function mul!(z::NfMaximalOrderElem, x::Integer, y::NfMaximalOrderElem)
  z.elem_in_nf = ZZ(x) * y.elem_in_nf
  nothing
end

mul!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::Integer) = mul!(z, y, x)

function mul!(z::NfMaximalOrderElem, x::fmpz, y::NfMaximalOrderElem)
  z.elem_in_nf = x * y.elem_in_nf
  nothing
end

mul!(z::NfMaximalOrderElem, x::NfMaximalOrderElem, y::fmpz) = mul!(z, y, x)

