################################################################################
#
#  NfOrd_ideals: Idls in orders of number fields
#
################################################################################

export NfOrdIdl

export ideal, colon_ideal, basis_mat_inv


ideal(O::NfOrd, a::fmpz)  = NfOrdIdl(O,a)

ideal(O::NfOrd, a::Integer) = NfOrdIdl(O,ZZ(a))

ideal(O::NfOrd, a::fmpz_mat) = NfOrdIdl(O,a)

order(a::NfOrdIdlSet) = a.order
  
order(a::NfOrdIdl) = order(parent(a))

parent(a::NfOrdIdl) = a.parent

function show(io::IO, a::NfOrdIdl)
  print(io, "Ideall of (")
  print(io, order(a), ")\n")
  print(io, "with basis matrix\n")
  print(io, basis_mat(a))
end

function basis_mat(a::NfOrdIdl)
  return a.basis_mat
end

function basis(a::NfOrdIdl)
  O = order(a)
  if isdefined(a, :basis)
    return a.basis
  end
  B = Array(elem_type(O), degree(order(a)))
  for i in 1:degree(O)
    t = zero(O)
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

function basis_mat_inv(a::NfOrdIdl)
  if isdefined(a, :basis_mat_inv)
    return a.basis_mat_inv
  else
    m,d = pseudo_inv(a.basis_mat)
    a.basis_mat_inv = FakeFmpqMat(m,d)
    return a.basis_mat_inv
  end
end
