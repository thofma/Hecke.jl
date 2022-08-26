#Hermitian-lattice database rufen
hld = Hecke.hermitian_lattice_database()
L = lattice(hld,75)#78 , 219, 375, 75, 56
E = base_field(L)
K = fixed_field(L)
pm = L.pmat 
A1,A2,A3 = pm.coeffs

function (E::Hecke.NfRel)(x::Vector{fmpq})

  abs_basis = absolute_basis(E)

  if length(abs_basis) != length(x) 
    error("Vector must have the same length as the absolute degree")
  end
  
  return sum(abs_basis[i]*x[i] for i = 1:length(abs_basis))
end

function (E::Hecke.NfRel)(x::fmpq_mat)

  abs_basis = absolute_basis(E)

  if length(abs_basis) != ncols(x) 
    error("Number of columns must have the same length as the absolute degree")
  end
  
  return [sum(abs_basis[i]*x[j,i] for i = 1:length(abs_basis))  for j = 1:nrows(x)] 
end

function _restrict_scalars_with_map(L)
  V = ambient_space(L)
  Vabs, f = restrict_scalars(V, FlintQQ)
  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = f\(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs), f
end

#OE = maximal_order(base_field(L))
function test(L)
  E = base_field(L)
  OE = maximal_order(E)
  b = gen(E)
  n = absolute_degree(E)

  K = base_field(E)
  OK = maximal_order(K)

  LL, f = _restrict_scalars_with_map(L)
  M = basis_matrix(LL)

  a = zeros(E, rank(L), rank(L))
  
  #constructing v_i = \sum A_i e_i -> A_i = B_{i1} y_1 + B_{i2} y_2
  for i = 1:rank(L)
    
    v = [M[1+(i-1)*n, j]  for j = 1:nrows(M)] #Convert type of the rows
    w = f(v) #
    lker = left_kernel(matrix(w))[2]
    rker = right_kernel(lker)[2]
    
    for j = 1:length(rker)
      a[i, j] = rker[j]
    end
    return a
    y = zeros(E, 2)
    A = M[1+(i-1)*n:i*n, 1:n]
    A_E = matrix(E(A))


    lker2 = left_kernel(A_E[[1,degree(K)+1], :])[2]
    rker2 = right_kernel(lker2)[2]

    for j = 1:length(rker2)
      y[j] = rker2[j]
    end

    return E(A), y
       
  end 
  
  #constructing A_i = \sum B_i v_i
  #return a, M

end


a = test(L)