################################################################################
#
#  NfOrder.jl : Orders in Number fields
#
#  Copyright (C) 2015 Tommy Hofmann
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

abstract ComOrd

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

NfOrderID = Dict{Tuple{NfNumberField, FakeFmpqMat}, ComOrd}()

type NfOrder <: ComOrd
  nf::NfNumberField
  basis_ord # Array{NfOrder_elt, 1}
  basis_nf #_basis::Array{nf_elem, 1}
  basis_mat::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  index::fmpz
  disc::fmpz
  disc_fac
  isequationorder::Bool
  parent::NfOrderSet

  function NfOrder()
    z = new()
    return z
  end
end

# need outer constructor or else NfOrderElem is not known at this point
function NfOrder(a::NfNumberField)
  A = FakeFmpqMat(basis_mat(a,basis(a)))
  if haskey(NfOrderID, (a,A))
    return NfOrderID[(a,A)]
  else
    z = NfOrder()
    z.nf = a
    z.parent = NfOrderSet(a)
    z.basis_mat = A
    z.basis_nf = basis(a)
    z.basis_ord = Array(NfOrderElem, degree(a))
    z.basis_ord[1] = z(Nemo.one(a), false)
    for i in 2:degree(a)
      z.basis_ord[i] = z(gen(a)^(i-1), false)
    end
    NfOrderID[(a, A)] = z
    return z
  end
end

function NfOrder(K::NfNumberField, x::FakeFmpqMat)
  if haskey(NfOrderID, (K,x))
    return NfOrderID[(K,x)]
  else
    z = NfOrder()
    z.basis_mat = x
    z.nf = K
    B = Array(NfOrderElem, degree(K))
    BB = Array(nf_elem, degree(K))
    for i in 1:degree(K)
      t = element_from_mat_row(K, x.num, i)//K(x.den)
      BB[i] = t
      B[i] = z(t, false) 
    end
    z.basis_ord = B
    z.basis_nf = BB
    z.parent = NfOrderSet(z.nf)
    NfOrderID[(K,x)] = z
    return z
  end
end

function NfOrder(a::Array{nf_elem, 1})
  K = parent(a[1])
  A = FakeFmpqMat(basis_mat(K,a))
  if haskey(NfOrderID, (K,A))
    return NfOrderID[(K,A)]
  else
    z = NfOrder()
    z.nf = parent(a[1])
    z.basis_nf = a
    z.parent = NfOrderSet(z.nf)
    NfOrderID[(K,A)] = z
    return z
  end
end

function deepcopy(O::NfOrder)
  z = NfOrder()
  for x in fieldnames(O)
    if isdefined(O, x)
      z.(x) = O.(x)
    end
  end
  return z
end

 
################################################################################
#
#  Field access
#
################################################################################

function basis_ord(O::NfOrder)
  if isdefined(O, :basis_ord)
    return O.basis_ord
  end
  b = O.basis_nf
  B = Array(NfOrderElem, length(b))
  for i in 1:length(b)
    v = fill(ZZ(0), length(b))
    v[i] = ZZ(1)
    B[i] = O(b[i], v; check = false)
  end
  O.basis_ord = B
  return B
end

function basis(O::NfOrder)
  return basis_ord(O)
end

function basis(O::NfOrder, K::NfNumberField)
  nf(O) != K && error()
  return basis_nf(O)
end

function basis_nf(O::NfOrder)
  return O.basis_nf
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
  error("This should not happen")
  A = basis(O)
  B = Array(nf_elem, degree(O))
  for i in 1:degree(O)
    B[i] = elem_in_nf(A[i])
  end
  O.basis_mat = FakeFmpqMat(basis_mat(O.nf, B))
  return O.basis_mat
end

function basis_mat_inv(O::NfOrder)
  if isdefined(O, :basis_mat_inv)
    return O.basis_mat_inv
  end
  O.basis_mat_inv = inv(basis_mat(O))
  return O.basis_mat_inv
end

function isequationorder(O::NfOrder)
  if !isdefined(O, :isequationorder)
    return O.isequationorder
  end
  O.isequationorder = false
  return false
end

nf(O::NfOrder) = O.nf

degree(O::NfOrder) = degree(O.nf)

parent(O::NfOrder) = O.parent

################################################################################
#
#  Number field element containment
#
################################################################################

function _check_elem_in_order(a::nf_elem, O::NfOrder)
  d = denominator(a)
  b = d*a 
  M = MatrixSpace(ZZ, 1, degree(O))()
  element_to_mat_row!(M,1,b)
  t = FakeFmpqMat(M,d)
  x = t*basis_mat_inv(O)
  v = Array(fmpz, degree(O))
  for i in 1:degree(O)
    v[i] = x.num[1,i]
  end
  return (x.den == 1, v) 
end  


################################################################################
#
#  Binary operations
#
################################################################################

# This works only if something is coprime??
function +(a::NfOrder, b::NfOrder)
  c = sub(hnf(vcat(den(basis_mat(b))*num(basis_mat(a)),den(basis_mat(a))*num(basis_mat(b)))),1:degree(a),1:degree(a))
  O = Order(nf(a),FakeFmpqMat(c,den(basis_mat(a))*den(basis_mat(b))))
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
  print(io, basis(a))
end

################################################################################
#
#  Parent call overloading
#
################################################################################

@doc """ dasd sads """ ->
function Base.call(a::NfOrderSet)
  z = NfOrder()
  z.parent = a
  z.nf = a.nf
  return z
end

@doc """ ich produziere eine Ordnung"""->
function Order(a::Array{nf_elem, 1}) 
  # check if it is a basis?
  return NfOrder(a)
end

@doc """ ich auch """->
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
  if isdefined(O, :disc)
    return O.disc
  end

  A = MatrixSpace(ZZ, degree(O), degree(O))()
  B = basis(O)
  for i in 1:degree(O)
    for j in 1:degree(O)
      A[i,j] = ZZ(trace(B[i]*B[j]))
    end
  end
  O.disc = determinant(A)
  return O.disc
end
