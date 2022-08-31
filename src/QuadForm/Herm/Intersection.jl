#Hermitian-lattice database rufen

#Could be added in src Numfield 
function (E::Hecke.NfRel)(x::Vector{fmpq})

  abs_basis = absolute_basis(E)

  if length(abs_basis) != length(x) 
    error("Vector must have the same length as the absolute degree")
  end
  
  return sum(abs_basis[i]*x[i] for i = 1:length(abs_basis))
end

#_matQQ_to_vec_E
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

function _restrict_scalars_with_respect_to_map(L,f)

  if codomain(f) !== ambient_space(L)
    error("codomain of f must be equal to the ambient space of L")
  end

  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = f\(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs)

end

function _divide(x,y)
  
end


#rows = rank , cols = degree --> L -> Lherm : degree(L) = degree(Lherm)*abs_deg(E), rank L = rank Lh *absolute deg(E)
#OE = maximal_order(base_field(L))
function reconstruction_herm(L)
  E = base_field(L)
  OE = maximal_order(E)
  n = absolute_degree(E)

  K = base_field(E)
  OK = maximal_order(K)

  LL, f = _restrict_scalars_with_map(L)
  M = basis_matrix(LL)

  a = zeros(E, degree(L), degree(L))
  coeffs = (Hecke.fractional_ideal_type(OE))[]
  #constructing v_i = \sum A_i e_i -> A_i = B_{i1} y_1 + B_{i2} y_2
  for i = 1:rank(L)
    
    v = [M[1+(i-1)*n, j]  for j = 1:nrows(M)] #Convert type of the rows
    a[i,:] = f(v) 
    #handle cases where first row is 0 @req [] @asset index != nothing
    
    #Find first element in a which is not zero
    index = findfirst(k -> !iszero(a[i,k]), 1:degree(L))
    
    #Ai = B1 y1 + B2 y2 
    y = zeros(E, 2)
    A = M[(1+(i-1)*n):i*n, (1+(index-1)*n): index*n] 
    
    A_E = matrix(absolute_coordinates.(E(A) .// a[i,index]))
    
    y = [E(A_E[1, :])[1], E(A_E[degree(K)+1, :])[1]]
    A_E[1:degree(K),:] = matrix(absolute_coordinates.(E(A_E[1:degree(K),:]) .// y[1]))
    A_E[degree(K)+1:n,:] = matrix(absolute_coordinates.(E(A_E[degree(K)+1:n,:]) .// y[2]))  

    fk1 = FakeFmpqMat(A_E[1:degree(K),1:degree(K)])
    frac_ideal1 = fractional_ideal(OK,fk1)
    B1 = fractional_ideal(OE, frac_ideal1)
    
    fk2 = FakeFmpqMat(A_E[degree(K)+1:n,1:degree(K)])
    frac_ideal2 = fractional_ideal(OK,fk2)
    B2 = fractional_ideal(OE, frac_ideal2)
    #print(typeof(B2))
    Ai = 0*OE
    Ai = B1*y[1] + B2*y[2]
    push!(coeffs,Ai)
    #print(typeof(Ai))
  end 
  
  pmatrix = Hecke.PMat{Hecke.elem_type(E), Hecke.fractional_ideal_type(OE)}(matrix(a),coeffs)
  Lnew = lattice(ambient_space(L),pmatrix) #codomain of f
  return Lnew

end


hld = Hecke.hermitian_lattice_database()
L = lattice(hld,75)#78 , 219, 375, 75, 56
E = base_field(L)
K = fixed_field(L)
pm = L.pmat 
A1,A2,A3 = pm.coeffs
LL = _restrict_scalars_with_map(L)
pmatrix = reconstruction_herm(L)
#=

#quad and herm reconstruction 
     #check trivial cases
    #start with 0*OE and add Bi
    #PseudoMatrix to construct the lattice at the end coeff -> a , ideals A_i 

    
    lker2 = left_kernel(A_E[[1,degree(K)+1], :])[2]
    rker2 = right_kernel(lker2)[2]

    for j = 1:length(rker2)
      y[j] = rker2[j]
    end
    #Irgendwas mit dem y stimmt nicht ganz
    return A_E, y


    Todo: Rank not full
    no zero block
    if first line are zero
    quad lattice
    test
    intersection
    out hermitian lattice
    input zlat + type of f
    adjust function
    matrix / nfelem
    checks: eine hälfte zero bei den Bi , blöcke vielfache voneinander 
    =#