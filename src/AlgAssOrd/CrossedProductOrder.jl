###############################################################################
#
#  Construction of a crossed product algebra
#
###############################################################################

function find_elem(G::Array{T,1}, el::T) where T
  i=1
  while true
    if el.prim_img==G[i].prim_img
      return i
    end
    i+=1
  end
end


#K/Q is a Galois extension.
function CrossedProductAlgebra(K::AnticNumberField, G::Array{T,1}, cocval::Array{nf_elem, 2}) where T

  n=degree(K)
  m=length(G)
  #=
  Multiplication table
  I order the basis in this way:
  First, I put the basis of the Galois Group, then the product of them with the first
  element of basis of the order and so on...
  =#
  
  M=Array{fmpq,3}(undef, n*m, n*m, n*m)
  for i=1:n*m
    for j=1:n*m
      for s=1:n*m
        M[i,j,s]=fmpq(0)
      end
    end
  end
  B=basis(K)
  for i=1:n
    for j=1:m
      #I have the element B[i]*G[j]
      for k=1:n
        for h=1:m
          # I take the element B[k]*G[h]
          # and I take the product 
          # B[i]*G[j]* B[k]*G[h]=B[i]*G[j](B[k])*c[j,h]*(G[j]*G[h])
          ind=find_elem(G,G[h] * G[j]) 
          x=B[i]*G[j](B[k])*cocval[j,h]
          #@show i, j, k,h,  ind,B[i],G[j](B[k]),cocval[j,h],  x
          for s=0:n-1
            M[j+(i-1)*n, h+(k-1)*n, ind+s*n]=coeff(x,s)
          end
          #@show M
        end
      end
    end
  end
  return AlgAss(FlintQQ, M)

end

function CrossedProductAlgebra(O::NfOrd, G::Array{T,1}, cocval::Array{nf_elem, 2}) where T

  n=degree(O)
  m=length(G)
  K=nf(O)
  #=
  Multiplication table
  I order the basis in this way:
  First, I put the basis of the Galois Group, then the product of them with the first
  element of basis of the order and so on...
  =#
  
  M=Array{fmpq,3}(undef, n*m, n*m, n*m)
  for i=1:n*m
    for j=1:n*m
      for s=1:n*m
        M[i,j,s]=fmpq(0)
      end
    end
  end
  B = basis(O, copy = false)
  el = O(0)
  for j=1:m
    for k=1:n
      l =O(G[j](K(B[k])), false)
      for h=1:m
        ind = find_elem(G, G[h] * G[j]) 
        t = O(cocval[j,h], false)
        for i=1:n
          #I have the element B[i]*G[j]
          # I take the element B[k]*G[h]
          # and I take the product 
          # B[i]*G[j]* B[k]*G[h]=B[i]*G[j](B[k])*c[j,h]*(G[j]*G[h])
          mul!(el, B[i], l)
          mul!(el, el, t)
          y = elem_in_basis(el)
          for s=0:n-1
            M[j+(i-1)*m, h+(k-1)*m, ind+s*m] = y[s+1]
          end
        end
      end
    end
  end
  j1 = find_identity(G, *)
  j = find_elem(G, j1)
  O1 = fmpq[0 for i=1:n*m]
  O1[j] = fmpq(1)
  A = AlgAss(FlintQQ, M, O1)
  A.issimple = 1
  return A

end

###############################################################################
#
#  Special functions to compute a maximal order
#
###############################################################################

function pradical_crossed_product(O::AlgAssAbsOrd, I1::AlgAssAbsOrdIdl, p::Int)
  
  A1, mA1 = quo(O, I1, p)
  lM = nmod_mat[transpose(representation_matrix(A1[i])) for i=1:dim(A1)]
  M = ModAlgAss(lM)
  ls = minimal_submodules(M)
  l = sum(nrows(x) for x in ls)
  M1 = zero_matrix(base_ring(A1), l, dim(A1))
  i=1
  for x in ls
    for j=1:nrows(x)
      for k=1:dim(A1)
        M1[i,k] = x[j,k]
      end
      i+=1
    end
  end
  r = rref!(M1)
  if r == dim(A1)
    return I1
  end
  M1 = view(M1, 1:r, 1:dim(A1))
  dM = transpose(nullspace(M1)[2])
  gens = Vector{elem_type(O)}(undef, nrows(dM))
  m = zero_matrix(FlintZZ, nrows(dM)+degree(O), degree(O))
  for i=1:nrows(dM)
    el = elem_in_basis(mA1(elem_from_mat_row(A1, dM, i)))
    for j=1:ncols(dM)
      m[i,j] = el[j]
    end
    gens[i]= elem_from_mat_row(O, m, i)
  end
  for i = 1:degree(O)
    for j = 1:degree(O)
      m[nrows(dM)+i, j] = I1.basis_mat[i,j]
    end
  end
  hnf_modular_eldiv!(m, fmpz(p))
  if isdefined(I1, :gens)
    append!(gens, I1.gens)
  else
    append!(gens, basis(I1, copy = false))
  end
  J=ideal(O, view(m, 1:degree(O), 1:degree(O)))
  J.gens=gens
  return J

end

function _ideal_in_radical(OL::NfOrd, G::Array{NfToNfMor, 1}, O::AlgAssAbsOrd, p::Int)
  
  A = algebra(O)
  I = pradical(OL, p)
  I.minimum = fmpz(p)
  _assure_weakly_normal_presentation(I)
  B = basis(I, copy = false)
  M = zero_matrix(FlintZZ, degree(O), degree(O))
  l = 0
  for i = 1:length(B)
    el = elem_in_basis(B[i])
    for j = 1:length(G)
      l += 1
      for k = 1:degree(OL)       
        M[l, j+ (k-1)*length(G)] = el[k]
      end
    end
  end
  K = nf(OL)
  phi = NfToNfMor(K, K, gen(K))
  j = find_elem(G, phi)
  #I need to save the generators of the ideal!
  gens = Array{AlgAssElem, 1}(undef, 2)
  el1 = elem_in_basis(OL(p))
  a = fmpq[0 for i=1:degree(O)]
  for k = 1:degree(OL)
    a[j+(k-1)*length(G)] = fmpq(el1[k])
  end
  gens[1] = A(a)
  a2 = fmpq[0 for i=1:degree(O)]
  el2 = elem_in_basis(I.gen_two)
  for k = 1:degree(OL)
    a2[j+(k-1)*length(G)] = fmpq(el2[k])
  end
  gens[2] = A(a2)
  return M, gens

end


function pmaximal_overorder_crossed_product(OL::NfOrd, G::Array{NfToNfMor, 1}, O::AlgAssAbsOrd, p::Int)

  d = discriminant(O)
  if rem(d, p^2) != 0  
    return O
  end
  
  A = algebra(O)
  extend = false
  #The p-radical of OL generates an ideal which is contained in the p-radical of the algebra. 
  #Therefore, to compute the maximal ideals, I can factor out the algebra by it.
  M, gens = _ideal_in_radical(OL, G, O, p)
  dd = fmpz(1)
  M = _hnf_modular_eldiv(M, fmpz(p))
  #Construct the ideal of O corresponding to the pradical in OL
  I1 = Hecke.AlgAssAbsOrdIdl{Hecke.AlgAss{fmpq},Hecke.AlgAssElem{fmpq, AlgAss{fmpq}}}(O, M)
  
  gensI1 = Array{AlgAssAbsOrdElem, 1}(undef, 2)
  gensI1[1] = O(gens[1])
  gensI1[2] = O(gens[2])
  I1.gens = gensI1
  @hassert :AlgAssOrd 1 check_ideal(I1)
  @vprint :AlgAssOrd 1 "Computing maximal ideals\n"
  @vtime :AlgAssOrd 1 max_id =_maximal_ideals(O, I1, p)
  for m in max_id
    @hassert :AlgAssOrd 1 check_ideal(m)
    @vtime :AlgAssOrd 1 OO = ring_of_multipliers(m, fmpz(p))
    dd = discriminant(OO)
    if d != dd
      extend = true
      O = OO
      d = dd
      break
    end
  end
   
  if extend
    return pmaximal_overorder(O, p)
  else
    return O
  end
end



