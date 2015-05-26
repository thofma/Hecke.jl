export NfMaximalOrderElem

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
  if isdefined(x, :elem_in_basis)
    return x.elem_in_basis
  end
  (b,v) = _check_elem_in_maximal_order(x.elem_in_nf, parent(x))
  x.elem_in_basis = v
  return v
end

################################################################################
#
#  Norm
#
################################################################################

function norm(x::NfMaximalOrderElem)
  return norm(elem_in_nf(x))
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
  z.elem_in_nf = x.elem_in_nf * y.elem_in_nf
end

function +(x::NfMaximalOrderElem, y::NfMaximalOrderElem)
  z = parent(x)()
  z.elem_in_nf = x.elem_in_nf + y.elem_in_nf
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::NfMaximalOrderElem)
  if isdefined(x, :elem_in_basis) && isdefined(x, :elem_in_nf)
    print(io, elem_in_nf(x), " ", elem_in_basis(x))
  elseif isdefined(x, :elem_in_basis)
    print(io, x.elem_in_basis)
  else
    print(io, x.elem_in_nf)
  end
end

