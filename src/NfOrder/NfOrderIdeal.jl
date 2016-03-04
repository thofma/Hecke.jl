################################################################################
#
#  NfOrd_ideals: Ideals in orders of number fields
#
################################################################################

export NfOrdIdeal

export ideal, colon_ideal, basis_mat_inv


ideal(O::NfOrd, a::fmpz)  = NfOrdIdeal(O,a)

ideal(O::NfOrd, a::Integer) = NfOrdIdeal(O,ZZ(a))

ideal(O::NfOrd, a::fmpz_mat) = NfOrdIdeal(O,a)

order(a::NfOrdIdlSet) = a.order
  
order(a::NfOrdIdeal) = order(parent(a))

parent(a::NfOrdIdeal) = a.parent

function show(io::IO, a::NfOrdIdeal)
  print(io, "Ideal of (")
  print(io, order(a), ")\n")
  print(io, "with basis matrix\n")
  print(io, basis_mat(a))
end

function basis_mat(a::NfOrdIdeal)
  return a.basis_mat
end

function basis(a::NfOrdIdeal)
  O = order(a)
  if isdefined(a, :basis)
    return a.basis
  end
  B = Array(NfOrdElem, degree(order(a)))
  for i in 1:degree(O)
    t = O()
    t.elem_in_nf = zero(nf(O))
    v = Array(fmpz,degree(O))
    for j in 1:degree(O)
      t += basis(O)[j]*basis_mat(a)[i,j]
      #v[j] = basis_mat(a)[i,j]
    end
    B[i] = t
    #B[i].elem_in_basis = v
  end
  a.basis = B
  return a.basis
end

function basis_mat_inv(a::NfOrdIdeal)
  if isdefined(a, :basis_mat_inv)
    return a.basis_mat_inv
  else
    m,d = pseudo_inv(a.basis_mat)
    a.basis_mat_inv = FakeFmpqMat(m,d)
    return a.basis_mat_inv
  end
end
