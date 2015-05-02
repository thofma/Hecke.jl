################################################################################
#
#  NfOrder_elt.jl : Elements in orders of number fields
#
################################################################################

export NfOrderElem

export elem_in_order

type NfOrderElem
  elem_in_nf::nf_elem
  elem_in_basis::Array{fmpz, 1}
  parent::NfOrder

  function NfOrderElem(O::NfOrder, a::nf_elem)
    (x,y) = _check_elem_in_order(a,O)
    !x && error("Number field element not in the order")
    z = new()
    z.elem_in_nf = a
    z.elem_in_basis = y
    z.parent = O
    return z
  end

  function NfOrderElem(O::NfOrder, arr::Array{fmpz, 1})
    z = new()
    z.elem_in_nf = dot(O._basis, arr)
    z.elem_in_basis = arr
    z.parent = O
    return z
  end

  function NfOrderElem(O::NfOrder)
    z = new()
    z.parent = O
    return z
  end
end

function NfOrderElem!(O::NfOrder, a::nf_elem)
  z = O()
  z.elem_in_nf = a
end

parent(a::NfOrderElem) = a.parent
 
function Base.call(O::NfOrder, a::nf_elem)
  return NfOrderElem(O,a)
end

function Base.call(O::NfOrder, arr::Array{fmpz, 1})
  return NfOrderElem(O,arr)
end

function Base.call(O::NfOrder)
  return NfOrderElem(O)
end

function *(a::NfOrderElem, b::NfOrderElem)
  z = parent(a)()
  z.elem_in_nf = a.elem_in_nf * b.elem_in_nf
  return z
end

# compute a^i mod p (fast?)
function powermod(a::NfOrderElem, i::fmpz, p::fmpz)
  println(i)
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

#function mod(a::NfOrderElem, p::fmpz)
#  z = parent(a)()
#  t = MatrixSpace(ZZ,degree(parent(a)), degree(parent(a)))(p)
#  d = ZZ(1)
#  z.elem_in_nf = element_reduce_mod(a.elem_in_nf, to_array(basis_mat(parent(a))), to_array(basis_mat_inv(parent(a))), p)
#  return z
#end

function elem_in_basis(a::NfOrderElem)
  # I should check if it is really in the order

  if isdefined(a, :elem_in_basis)
    return a.elem_in_basis
  end

  (x,y) = _check_elem_in_order(a.elem_in_nf, parent(a))
  x && return y
  !x && error("Ooops! The underlying .elem_in_nf is not contained in the order")
end

function mod(a::NfOrderElem, m::fmpz)
  M = MatrixSpace(ZZ, 1, degree(parent(a)))(reshape(elem_in_basis(a),1,degree(parent(a))))
  MM = reduce_mod(M, m)
  return parent(a)(map(ZZ, vec(Array(MM))))
end
  
  
#  bas = to_array(basis_mat(parent(a)))
#  inv_bas = to_array(basis_mat_inv(parent(a)))
#
#  n = degree(parent(a))
#  M = MatrixSpace(ZZ, 1, n)();
#  d_a = denominator(a.elem_in_nf)
#  element_to_mat_row!(M, 1, a.elem_in_nf*d_a);
#  b, d = inv_bas
#  M = divexact(M*b, d*d_a)  
#  arr = Array(fmpz, n)
#  for i in 1:n
#    arr[i] = M[1,i]
#  end
#  return arr
#end

function *(a::NfOrderElem, b::fmpz)
  z = parent(a)()
  z.elem_in_nf = a.elem_in_nf *b
  return z
end

*(a::fmpz, b::NfOrderElem) = b*a

function zero(O::NfOrder)
  z = O()
  z.elem_in_nf = zero(O.nf)
  z.elem_in_basis = fill!(Array(fmpz, degree(O)), ZZ(0))
  return z
end


function +(a::NfOrderElem, b::NfOrderElem)
  z = parent(a)()
  z.elem_in_nf = a.elem_in_nf + b.elem_in_nf
  return z
end

function _check_elem_in_order(a::nf_elem, O::NfOrder)
  d = denominator(a)
  b = d*a 
  M = MatrixSpace(ZZ, 1, degree(O))()
  element_to_mat_row!(M,1,b)
  t = FakeFmpqMat(M,d)
  x = t*basis_mat_inv(O)
  println(x)
  return (x.den == 1, map(ZZ,vec(Array(x.num)))) ## Array() should really be already an array of fmpz's; Julia Arrays are a nightmare
end  

function elem_in_order(a::nf_elem, O::NfOrder)
  (x,y) = _check_elem_in_order(a, O)
  return (x, O(y))
end

function representation_mat(a::NfOrderElem)
  O = parent(a)
  A = representation_mat(a, parent(a).nf)
  A = basis_mat(O)*A*basis_mat_inv(O)
  @assert A.den == 1
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
  

