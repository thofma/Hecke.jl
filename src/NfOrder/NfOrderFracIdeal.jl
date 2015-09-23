export NfOrderFracIdeal

export colon_ideal


order(a::NfOrderFracIdealSet) = a.order

order(a::NfOrderFracIdeal) = order(a.parent)

function colon_ideal(a::NfOrderIdeal)
  B = basis(a)
  O = order(a)
  @vprint :NfOrder 1 "$(representation_mat(B[1]))\n"
  @vprint :NfOrder 1 FakeFmpqMat(representation_mat(B[1]),ZZ(1))*basis_mat_inv(a)
  m = to_fmpz_mat(FakeFmpqMat(representation_mat(B[1]),ZZ(1))*basis_mat_inv(a))
  for i in 2:degree(O)
    m = hcat(to_fmpz_mat(FakeFmpqMat(representation_mat(B[i]),ZZ(1))*basis_mat_inv(a)),m)
  end
  n = hnf(transpose(m))
  # n is upper right HNF
  n = transpose(sub(n,1:degree(O),1:degree(O)))
  b,d = pseudo_inv(n)
  return NfOrderFracIdeal(O,hnf(FakeFmpqMat(b,d)))
end  

function NfOrder(a::NfOrderFracIdeal)
  z = NfOrder(nf(order(a)), a.basis_mat*order(a).basis_mat)
  return z
end
