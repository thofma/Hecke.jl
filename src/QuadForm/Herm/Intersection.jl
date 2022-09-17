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

#
function _divide_matrix_nfelem(x,y,E)
  return matrix(absolute_coordinates.(E(x) .// y))
end


#rows = rank , cols = degree --> L -> Lherm : degree(L) = degree(Lherm)*abs_deg(E), rank L = rank Lh *absolute deg(E)
#OE = maximal_order(base_field(L))
#M not more rows than columns. 
#intersect is in Zlattice, : intersection/
#intersect quadform/lattice,jl reference the quadform intersect
#

#Takes the basis_matrix of the lattice
function _reconstruction_herm_lattice(L, E::Hecke.NfRel{nf_elem}, f::Hecke.VecSpaceRes{Hecke.NfRel{nf_elem}, Hecke.NfRelElem{nf_elem}}, Vas)
  M = basis_matrix(L)
  OE = maximal_order(E)
  n = absolute_degree(E)

  K = base_field(E)
  OK = maximal_order(K)
  deg = div(ncols(M),n)
  
  a = zeros(E, deg, deg)
  coeffs = (Hecke.fractional_ideal_type(OE))[]
  #constructing v_i = \sum A_i e_i -> A_i = B_{i1} y_1 + B_{i2} y_2
  for i = 1:deg
 
    ind = findfirst(k -> !iszero(M[k,:]), 1+(i-1)*n:i*n) + (i-1)*n
    if typeof(ind) == Nothing
      error("Zero block detected.")
    end
    v = [M[ind, j]  for j = 1:ncols(M)] #Convert type of the rows
    a[i, :] = f(v)  
    
    #handle cases where first row is 0 @req [] @asset index != nothing
    
    check = []
    for j = 1:deg
      if !iszero(a[i,j])
        push!(check, _divide_matrix_nfelem(M[(1+(i-1)*n):i*n, (1+(j-1)*n): j*n], a[i,j], E))  
      end 
    end
    if length(check) != 1
      for k = 1:length(check)-1
        if check[k] != check[k+1]
          error("The lattice cannot be lifted.")
        end
      end
    end
  
    #Find first element in a which is not zero
    index = findfirst(k -> !iszero(a[i, k]), 1:deg)
    
    #Ai = B1 y1 + B2 y2 
    
    A = M[(1+(i-1)*n):i*n, (1+(index-1)*n): index*n] 
    A_E = _divide_matrix_nfelem(A, a[i, index], E)
    y = [E(A_E[1, :])[1], E(A_E[degree(K)+1, :])[1]]
    A_E[1:degree(K),:] = _divide_matrix_nfelem(A_E[1:degree(K), :], y[1], E)
    A_E[degree(K)+1:n,:] = _divide_matrix_nfelem(A_E[degree(K)+1:n, :], y[2], E)
    
    
    if !iszero(A_E[:,degree(K)+1:end]) 
      error("The lattice cannot be lifted.")
    end
    
    fk1 = FakeFmpqMat(A_E[1:degree(K), 1:degree(K)])
    frac_ideal1 = fractional_ideal(OK, fk1)
    B1 = fractional_ideal(OE, frac_ideal1)
    
    fk2 = FakeFmpqMat(A_E[degree(K)+1:n, 1:degree(K)])
    frac_ideal2 = fractional_ideal(OK, fk2)
    B2 = fractional_ideal(OE, frac_ideal2)

    Ai = B1*y[1] + B2*y[2]
    push!(coeffs, Ai)
  end 
  
  pmatrix = Hecke.PMat{Hecke.elem_type(E), Hecke.fractional_ideal_type(OE)}(matrix(a), coeffs)
  Lnew = lattice(Vas, pmatrix) #codomain of f
  return Lnew

end


hld = Hecke.hermitian_lattice_database()
L = lattice(hld, 78) #78 , 219, 375, 75, 56
E = base_field(L)
LL,f = _restrict_scalars_with_map(L)
M = basis_matrix(LL)
Lrec = _reconstruction_herm_lattice(LL, E, f, ambient_space(L))
#_reconstruction_herm_lattice(intersect(LL,LL), E, f)



#=
    Todo: Rank not full (Gibt es in der Datenbank nicht)
    - no zero block
    - if first line are zero
    quad lattice
    test
    intersection
    - checks: eine hälfte zero bei den Bi , blöcke vielfache voneinander 


    Quadform -> lattices_ restrict_scalars ----
              -> Intersection -> intersect : if not full rank -> check if quad or herm _intersection_with_restriction_of_scalars
             -> Intersection/Satuation -> _divide_matrix_nfelem + _reconstruction_quad_lattice
    Same in herm 
             =#