export NfOrderFracIdeal

export colon_ideal

NfOrderFracIdealSetID = ObjectIdDict()

type NfOrderFracIdealSet
  order::NfOrder
  
  function NfOrderFracIdealSet(a::NfOrder)
    try
      return NfOrderFracIdealSetID[a]
    catch
      NfOrderFracIdealSetID[a] = new(a)
      return NfOrderFracIdealSetID[a]
    end
  end
end

type NfOrderFracIdeal
  basis::Array{NfOrderElem, 1}
  basis_mat::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  parent::NfOrderFracIdealSet
  
  function NfOrderFracIdeal(O::NfOrder, a::FakeFmpqMat)
    z = new()
    z.basis_mat = a
    z.parent = NfOrderFracIdealSet(O)
    return z
  end
end

order(a::NfOrderFracIdealSet) = a.order

order(a::NfOrderFracIdeal) = order(a.parent)

function colon_ideal(a::NfOrderIdeal)
  B = basis(a)
  O = order(a)
  m = to_fmpz_mat(FakeFmpqMat(representation_mat(B[1]),ZZ(1))*basis_mat_inv(a))
  for i in 2:degree(O)
    m = hcat(to_fmpz_mat(FakeFmpqMat(representation_mat(B[i]),ZZ(1))*basis_mat_inv(a)),m)
  end
  n = hnf(transpose(m))
  n = transpose(sub(n,1:degree(O),1:degree(O)))
  b,d = pseudo_inverse(n)
  return NfOrderFracIdeal(O,FakeFmpqMat(b,d))
end  

function NfOrder(a::NfOrderFracIdeal)
  z = NfOrder(order(a).nf, a.basis_mat*order(a).basis_mat)
  return z
end
