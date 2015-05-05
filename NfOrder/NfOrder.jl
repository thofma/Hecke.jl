################################################################################
#
#  NfOrder.jl : Orders in Number fields
#
################################################################################

import Base: powermod

export NfOrder, NfOrderSet

export powermod, elem_in_basis, EquationOrder, deepcopy, Order

################################################################################
#
#  Types
#
################################################################################

NfOrderSetID = ObjectIdDict()

type NfOrderSet
  nf::NfNumberField

  function NfOrderSet(a::NfNumberField)
  try
    return NfOrderSetID[a]
  end
    NfOrderSetID[a] = new(a)
    return NfOrderSetID[a]
  end
end

type NfOrder <: Ring
  nf::NfNumberField
  basis # Array{NfOrder_elt, 1}
  _basis::Array{nf_elem, 1}
  basis_mat::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  discriminant::fmpz
  isequationorder::Bool
  index::fmpz
  parent::NfOrderSet

  function NfOrder()
    z = new()
    return z
  end

  function NfOrder(a::NfNumberField)
    z = new()
    z._basis = Array(nf_elem, degree(a))
    z._basis[1] = one(a)
    for i in 2:degree(a)
      z._basis[i] = gen(a)^(i-1)
    end
    z.nf = a
    z.parent = NfOrderSet(a)
    return z
  end

  function NfOrder(a::Array{nf_elem, 1})
    z = new()
    z.nf = parent(a[1])
    z._basis = a
    z.parent = NfOrderSet(z.nf)
    return z
  end
    
  function NfOrder(f::fmpq_poly, s::ASCIIString = "a")
    z = new()
    z.nf = NumberField(f, s)[1]
    z._basis = basis(z.nf)
    z.discriminant = discriminant(PolynomialRing(ZZ,"x")[1](f))
    z.parent = NfOrderSet(z.nf)
    return z
  end

  function NfOrder(K::NfNumberField, x::FakeFmpqMat)
    z = new()
    z.basis_mat = x
    z.nf = K
    B = Array(nf_elem, degree(K))
    for i in 1:degree(K)
      B[i] = element_from_mat_row(K, x.num, i)//K(x.den) ## this is stupid: nf_elem//fmpz not definied!
    end
    z._basis = B
    z.parent = NfOrderSet(z.nf)
    return z
  end
end

function _basis(O::NfOrder)
  (!isdefined(O, :_basis) && !isdefined(O, :basis_mat)) && error("_basis or basis_mat must be defined")
  if isdefined(O, :_basis)
    return O._basis
  end
  a = Array(nf_elem, degree(O))
  for i in 1:degree(O)
    a[i] = QQ(1)//QQ(den(basis_mat(O))) * element_from_mat_row(O.nf, num(basis_mat(O)), i)
  end
  O._basis = a
  return O._basis
end

function basis(O::NfOrder)
  if isdefined(O, :basis)
    return O.basis
  end
  z = Array(NfOrderElem, degree(O))
  for i in 1:degree(O)
    z[i] = O(O._basis[i])
  end
  O.basis = z
  return O.basis
end


function basis_mat(K::NfNumberField, b::Array{nf_elem, 1})
  d = denominator(b[1])
  n = degree(K)
  for i = 2:n
    d = Base.lcm(d, denominator(b[i]))
  end
  M = MatrixSpace(ZZ, n,n)()
  for i = 1:n
    element_to_mat_row!(M, i, b[i]*d)
  end
  return M, d
end 

function basis_mat(O::NfOrder)
  if isdefined(O, :basis_mat)
    return O.basis_mat
  end
  O.basis_mat = FakeFmpqMat(basis_mat(O.nf, O._basis))
  return O.basis_mat
end

function basis_mat_inv(O::NfOrder)
  if isdefined(O, :basis_mat_inv)
    return O.basis_mat_inv
  end
  O.basis_mat_inv = inv(basis_mat(O))
  return O.basis_mat_inv
end

degree(O::NfOrder) = degree(O.nf)

parent(O::NfOrder) = O.parent

################################################################################
#
#  Binary operations
#
################################################################################

function +(a::NfOrder, b::NfOrder)
  O = parent(a)()
  c = sub(hnf(vcat(den(basis_mat(b))*num(basis_mat(a)),den(basis_mat(a))*num(basis_mat(b)))),1:degree(O),1:degree(O))
  O.basis_mat = FakeFmpqMat(c,den(basis_mat(a))*den(basis_mat(b)))
  return O
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfOrderSet)
  print(io, "Set of orders of the number field ")
  print(io, a.nf)
end  

function show(io::IO, a::NfOrder)
  print(io, "Order of ")
  println(io, a.nf)
  print(io, "with Z-basis ")
  print(io, _basis(a))
end

################################################################################
#
#  Parent call overloading
#
################################################################################

function Base.call(a::NfOrderSet)
  z = NfOrder()
  z.parent = a
  z.nf = a.nf
  return z
end

function Order(a::Array{nf_elem, 1}) 
  # check if it is a basis?
  return NfOrder(a)
end

function Order(a::NfNumberField, b::FakeFmpqMat)
  return NfOrder(a,b)
end

function EquationOrder(a::NfNumberField)
  # check if a is simple (when we have non-simple fields)
  z = NfOrder(a)
  z.isequationorder = true
  return z
end

################################################################################
#
#  Discriminant
#
################################################################################

function discriminant(O::NfOrder)
  if isdefined(O, :discriminant)
    return O.discriminant
  end

  A = MatrixSpace(ZZ, degree(O), degree(O))()
  for i in 1:degree(O)
    for j in 1:degree(O)
      A[i,j] = ZZ(trace(_basis(O)[i]*_basis(O)[j]))
    end
  end
  O.discriminant = determinant(A)
  return O.discriminant
end
