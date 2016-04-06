export NfOrdFracIdl

export colon_ideal


order(a::NfOrdFracIdlSet) = a.order

order(a::NfOrdFracIdl) = order(a.parent)

function colon_ideal(a::NfOrdIdl)
  B = basis(a)
  O = order(a)
  @vprint :NfOrd 1 "$(representation_mat(B[1]))\n"
  @vprint :NfOrd 1 FakeFmpqMat(representation_mat(B[1]),ZZ(1))*basis_mat_inv(a)
  m = to_fmpz_mat(FakeFmpqMat(representation_mat(B[1]),ZZ(1))*basis_mat_inv(a))
  for i in 2:degree(O)
    m = hcat(to_fmpz_mat(FakeFmpqMat(representation_mat(B[i]),ZZ(1))*basis_mat_inv(a)),m)
  end
  n = hnf(transpose(m))
  # n is upper right HNF
  n = transpose(sub(n,1:degree(O),1:degree(O)))
  b,d = pseudo_inv(n)
  return NfOrdFracIdl(O,hnf(FakeFmpqMat(b,d)))
end  

function NfOrd(a::NfOrdFracIdl)
  z = NfOrd(nf(order(a)), a.basis_mat*order(a).basis_mat)
  return z
end
