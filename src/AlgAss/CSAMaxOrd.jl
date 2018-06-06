
add_assert_scope(:CSAMaxOrd)

###############################################################################
#
#  Types
#
###############################################################################

mutable struct AlgAssOrd 
  A::AlgAss{fmpq}                  # CSA containing it
  dim::Int
  basis_alg::Vector{AlgAssElem{fmpq}}    # Basis as array of elements of the algebra
  basis_mat::FakeFmpqMat           # Basis matrix of order wrt basis of the algebra
  basis_mat_inv::FakeFmpqMat       # Inverse of basis matrix
  gen_index::fmpq                  # The det of basis_mat_inv as fmpq
  index::fmpz                      # The det of basis_mat_inv
                                   # (this is the index of the equation order
                                   #  in the given order)
  disc::fmpz                       # Discriminant
  
  ismaximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal
                                   
  trace_mat::fmpz_mat              # The reduced trace matrix (if known)


  function AlgAssOrd(a::AlgAss{fmpq}, basis::Array{AlgAssElem{fmpq},1})
    # "Default" constructor with default values.
    r = new()
    r.A=a
    r.dim=size(a.mult_table,1)
    @assert length(basis)==r.dim
    r.basis_alg=basis
    r.basis_mat=basis_mat(basis)
    r.basis_mat_inv=inv(r.basis_mat)
    r.ismaximal = 0
    return r
  end
  
  function AlgAssOrd(a::AlgAss{fmpq}, mat::FakeFmpqMat)
    r = new()
    r.A=a
    r.dim=size(a.mult_table,1)
    r.basis_alg=Array{AlgAssElem{fmpq},1}(rows(mat))
    for i=1:length(r.basis_alg)
      r.basis_alg[i]=elem_from_mat_row(a,mat.num, i, mat.den)
    end
    r.basis_mat=mat
    r.ismaximal = 0
    return r
  end
  
end

mutable struct AlgAssOrdElem
  elem_in_algebra::AlgAssElem{fmpq}
  elem_in_basis::Vector{fmpz}
  parent::AlgAssOrd

  function AlgAssOrdElem(O::AlgAssOrd, a::AlgAssElem)
    z = new()
    z.elem_in_algebra = a
    z.parent = O
    return z
  end

  function AlgAssOrdElem(O::AlgAssOrd, a::AlgAssElem, arr::Array{fmpz, 1})
    z = new()
    z.parent = O
    z.elem_in_algebra = a
    z.elem_in_basis = arr
    return z
  end

  function AlgAssOrdElem(O::AlgAssOrd, arr::Array{fmpz, 1})
    z = new()
    z.elem_in_algebra = dot(O.basis_alg, arr)
    z.elem_in_basis = arr
    z.parent = O
    return z
  end

end

mutable struct AlgAssOrdIdl
  O::AlgAssOrd                     # Order containing it
  basis_alg::Vector{AlgAssOrdElem} # Basis of the ideal as array of elements of the order
  basis_mat::fmpz_mat              # Basis matrix of ideal wrt basis of the order
  gens::Vector{AlgAssOrdElem}      # Generators of the ideal 
  
  function AlgAssOrdIdl(a::AlgAssOrd, basis::Array{AlgAssOrdElem,1})
    # "Default" constructor with default values.
    r = new()
    r.O=a
    r.basis_alg=basis
    r.basis_mat=zero_matrix(FlintZZ, a.dim, a.dim)
    for i=1:a.dim
      for j=1:a.dim
        r.basis_mat[i,j]=basis[i].elem_in_basis[j]
      end
    end
    return r
  end

  function AlgAssOrdIdl(a::AlgAssOrd, M::fmpz_mat)
    r = new()
    r.O=a
    r.basis_alg=Array{AlgAssOrdElem,1}(a.dim)
    for i=1:a.dim
      r.basis_alg[i]=elem_from_mat_row(a,M,i)
    end
    r.basis_mat=M
    return r
  end
  
end

###############################################################################
#
#  Some auxiliary functions
#
###############################################################################

function lift(M::fq_nmod_mat)

  N=zero_matrix(FlintZZ, rows(M), cols(M))
  for i=1:rows(M)
    for j=1:cols(M)
      N[i,j]=FlintZZ(coeff(M[i,j],0))
    end
  end
  return N
end

function FakeFmpqMat(x::Array{fmpq,1})
  dens=[denominator(x[i]) for i=1:length(x)]
  den=lcm(dens)
  M=zero_matrix(FlintZZ, 1, length(x))
  for i=1:length(x)
    M[1,i]=numerator(x[i])*divexact(den, dens[i])
  end
  return FakeFmpqMat(M,den)
end

function find_elem(G::Array{T,1}, el::T) where T
  i=1
  while true
    if el.prim_img==G[i].prim_img
      return i
    end
    i+=1
  end
end

###############################################################################
#
#  Functions for ideals
#
###############################################################################

function ideal(O::AlgAssOrd, mat::fmpz_mat)
  return AlgAssOrdIdl(O,mat)
end

function in(x::AlgAssOrdElem, I::AlgAssOrdIdl)

  y=matrix(FlintZZ, 1, length(I.basis_alg), elem_in_basis(x))
  M1, d =pseudo_inv(I.basis_mat)
  if FakeFmpqMat(y*M1, d).den==1
    return true
  else
    return false
  end

end


###############################################################################
#
#  Functions for elements of order
#
###############################################################################

@inline parent(x::AlgAssOrdElem)=x.parent

(O::AlgAssOrd)(a::Array{fmpz,1}) = AlgAssOrdElem(O,a)

function elem_in_basis(x::AlgAssOrdElem, copy::Type{Val{T}} = Val{true}) where T
  if isdefined(x, :elem_in_basis)
    if copy==Val{true}
      return deepcopy(x.elem_in_basis)
    else
      return x.elem_in_basis
    end
  else
    M=FakeFmpqMat(x.elem_in_algebra.coeffs)*x.parent.basis_mat_inv
    x.elem_in_basis=Array{fmpz,1}(M.c)
    for i=1:M.c
      x.elem_in_basis[i]=M.num[1,i]
    end
  end
  if copy==Val{true}
    return deepcopy(x.elem_in_basis)
  else
    return x.elem_in_basis
  end
end


function *(x::AlgAssOrdElem, y::AlgAssOrdElem)
  @assert parent(x)==parent(y)
  O=parent(x)
  return O(x.elem_in_algebra*y.elem_in_algebra)
end

function *(n::Int, x::AlgAssOrdElem)

  O=x.parent
  y=Array{fmpz,1}(O.dim)
  z=elem_in_basis(x, Val{false})
  for i=1:O.dim
    mul!(y[i], x.elem_in_basis[i], n)
  end
  return AlgAssOrdElem(O,y)
  
end

function in(x::AlgAssElem, O::AlgAssOrd)
  
  y=FakeFmpqMat(x.coeffs)
  if isdefined(O, :basis_mat_inv)
    M1=O.basis_mat_inv
  else
    M1=inv(O.basis_mat)
    O.basis_mat_inv=M1
  end
  if (y*M1).den==1
    return true
  else
    return false
  end

end

(O::AlgAssOrd)(a::AlgAssElem) = begin
  if !isdefined(O, :basis_mat_inv)
    O.basis_mat_inv=inv(O.basis_mat)
  end
  x=FakeFmpqMat(a.coeffs)*O.basis_mat_inv
  @assert denominator(x)==1
  return AlgAssOrdElem(O,vec(Array(x.num)))
end

function elem_from_mat_row(O::AlgAssOrd, M::fmpz_mat, i::Int)
  return AlgAssOrdElem(O, [M[i,j] for j=1:O.dim])
end

###############################################################################
#
#  Functions for orders
#
###############################################################################

function basis_mat(A::Array{AlgAssElem{fmpq}, 1})
  @assert length(A) > 0
  n = length(A)
  d = size(parent(A[1]).mult_table,1)

  M = zero_matrix(FlintZZ, n, d)

  dens = [lcm([denominator(A[i].coeffs[j]) for j=1:d]) for i=1:n]
  deno = lcm(dens)

  for i in 1:n
    temp_den = divexact(deno, dens[i])
    for j in 1:d
      M[i, j] = numerator(A[i].coeffs[j]*temp_den)
    end
  end
  return FakeFmpqMat(M, deno)
end

function elem_from_mat_row(A::AlgAss, M::fmpz_mat, i::Int, d::fmpz=fmpz(1))
  return A([M[i,j]//d for j=1:cols(M)])
end

function order_gen(O::AlgAssOrd)
  
  M=O.basis_mat
  if isdefined(O, :basis_mat_inv)
    M1=O.basis_mat_inv
  else
    M1=inv(M)
  end
  for x in O.basis_alg
    for y in O.basis_alg
      if !(x*y in O)
        a=FakeFmpqMat((x*y).coeffs)
        N=vcat(M,a)
        return AlgAssOrd(O.A, hnf(N))
      end
    end
  end

end



###############################################################################
#
#  Sum of orders
#
###############################################################################

# Be careful!
# To be used only in the case of the construction of a maximal order!
function +(a::AlgAssOrd, b::AlgAssOrd)
  aB = a.basis_mat
  bB = b.basis_mat
  d = a.dim
  c = sub(_hnf(vcat(bB.den*aB.num, aB.den*bB.num), :lowerleft), d + 1:2*d, 1:d)
  return AlgAssOrd(a.A, FakeFmpqMat(c, aB.den*bB.den))
end


###############################################################################
#
#  Print
#
###############################################################################

function show(io::IO, O::AlgAssOrd)
  print(io, "Order of ")
  println(io, O.A)
end

function show(io::IO, a::AlgAssOrdElem)
  print(io, a.elem_in_algebra.coeffs)
end

function show(io::IO, a::AlgAssOrdIdl)
  print(io, "Ideal of ")
  print(io, a.O)
  println(io, "with basis matrix")
  print(io, a.basis_mat)
end

###############################################################################
#
#  Construction of a crossed product algebra
#
###############################################################################

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
  
  M=Array{fmpq,3}(n*m, n*m, n*m)
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
          ind=find_elem(G,G[j]*G[h]) 
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

function CrossedProductAlgebraWithMaxOrd(O::NfOrd, G::Array{T,1}, cocval::Array{nf_elem, 2}) where T

  n=degree(O)
  m=length(G)
  K=nf(O)
  #=
  Multiplication table
  I order the basis in this way:
  First, I put the basis of the Galois Group, then the product of them with the first
  element of basis of the order and so on...
  =#
  
  M=Array{fmpq,3}(n*m, n*m, n*m)
  for i=1:n*m
    for j=1:n*m
      for s=1:n*m
        M[i,j,s]=fmpq(0)
      end
    end
  end
  B=basis(O)
  for i=1:n
    for j=1:m
      #I have the element B[i]*G[j]
      for k=1:n
        for h=1:m
          # I take the element B[k]*G[h]
          # and I take the product 
          # B[i]*G[j]* B[k]*G[h]=B[i]*G[j](B[k])*c[j,h]*(G[j]*G[h])
          ind=find_elem(G,G[j]*G[h]) 
          x=B[i]*O(G[j](K(B[k])))*O(cocval[j,h])
          y=elem_in_basis(x)
          for s=0:n-1
            M[j+(i-1)*n, h+(k-1)*n, ind+s*n]=y[s+1]
          end
        end
      end
    end
  end
  return AlgAss(FlintQQ, M)

end


###############################################################################
#
#  Quaternion algebras
#
###############################################################################

function quaternion_algebra(a::Int, b::Int)
  
  M=Array{fmpq,3}(4,4,4)
  for i=1:4
    for j=1:4
      for k=1:4
        M[i,j,k]=0
      end
    end
  end  
  M[1,1,1]=1 # 1*1=1
  M[1,2,2]=1 # 1*i=i
  M[1,3,3]=1 # 1*j=j
  M[1,4,4]=1 # 1*ij=1
  
  M[2,1,2]=1
  M[2,2,1]=a
  M[2,3,4]=1
  M[2,4,3]=a
  
  M[3,1,3]=1
  M[3,2,4]=-1
  M[3,3,1]=b
  M[3,4,2]=-b
  
  M[4,1,4]=1
  M[4,2,3]=-a
  M[4,3,2]=b
  M[4,4,1]=-a*b
  return AlgAss(FlintQQ, M)
  
end

###############################################################################
#
#  Quotient
#
###############################################################################

function quo(O::AlgAssOrd, p::Int)

  F,a=FiniteField(p,1,"a")
  M=Array{fq_nmod, 3}(O.dim, O.dim, O.dim)
  x=fmpz[0 for i=1:O.dim]
  for i=1:O.dim
    x[i]=1
    N=representation_matrix(O(x))
    for j=1:O.dim
      for k=1:O.dim
        M[i,j,k]=F(N[j,k])
      end
    end
    x[i]=0
  end
  oneO=elem_in_basis(O(one(O.A)))
  oneQ=fq_nmod[F(s) for s in oneO]
  return AlgAss(F,M, oneQ)
  
end

function _mod(x::fmpz_mat, y::fmpz_mat, pivots::Array{Int,1})
   for i=1:length(pivots)
     for k=1:cols(x)
       z=div(x[pivots[i],k], y[k,k])
       if z!=0
         for j=k:cols(x)
           x[pivots[i],j]-=z*y[k,j]
         end
       end
     end     
   end
   return nothing
end


function quo(O::AlgAssOrd, I::AlgAssOrdIdl, p::Int)
  pivots=Int[]
  for i=1:O.dim
    if I.basis_mat[i,i]==p
      push!(pivots, i)
    end
  end
  @hassert :CSAMaxOrd 1 check_ideal(I)
  F,a=FlintFiniteField(p,1,"a")
  M=Array{fq_nmod, 3}(length(pivots), length(pivots), length(pivots))
  x=fmpz[0 for s=1:O.dim]
  for i=1:length(pivots)
    x[pivots[i]]=1
    y=O(x)
    N=representation_matrix(y)
    _mod(N, I.basis_mat, pivots)
    for j=1:length(pivots)
      #reduce the vector with respect to the ideal.
      #I assume that the basis of the ideal is in upper triangular HNF 
      for k=1:length(pivots)
        M[i,j,k]=F(N[pivots[j],pivots[k]])
      end
    end
    x[pivots[i]]=0
  end
  A=AlgAss(F,M)
  function AtoO(a::AlgAssElem)
    x=fmpz[0 for i=1:O.dim]
    for i=1:length(pivots)
      x[pivots[i]]=FlintZZ(coeff(a.coeffs[i],0))
    end
    return O(x)
  end 
  
  return A, AtoO

end



###############################################################################
#
#  Some tests
#
###############################################################################

function check_ideal(I::AlgAssOrdIdl)
  
  O=I.O
  x=fmpz[0 for i=1:O.dim]
  for i=1:O.dim
    x[i]=1
    y=O(x)
    for j=1:O.dim
      @assert y*I.basis_alg[j] in I
      @assert I.basis_alg[j]*y in I
    end 
    x[i]=0    
  end
  return true
  
end

function check_order(O::AlgAssOrd)
  
  for x in O.basis_alg
    @assert denominator(minpoly(x))==1
    for y in O.basis_alg
      if !(x*y in O)
        @show x,y
        error("not in the order!")
      end
    end
  end
  return true

end

function check_pradical(I::AlgAssOrdIdl, p::Int)
  
  O=I.O
  for i=1:O.dim
    x=elem_from_mat_row(O,I.basis_mat, i)
    for j=1:O.dim
      @assert divisible(numerator(trace(x.elem_in_algebra*O.basis_alg[j])), p)
    end
  end
  #=
  if p==2
    for i=1:O.dim
      x=elem_from_mat_row(O,I.basis_mat, i)
      for j=1:O.dim
        for k=1:clog(fmpz(O.dim), p)
          @assert divisible(numerator(trace((x.elem_in_algebra*O.basis_alg[j])^(p^k))), p^(k+1))
        end
      end
    end
  end
  =#
  return true
end


###############################################################################
#
#  ring of multipliers
#
###############################################################################

doc"""
***
    ring_of_multipliers(I::AlgAssOrdIdl)
        
> Given an ideal I, it returns the ring (I : I)
"""

function ring_of_multipliers(I::AlgAssOrdIdl, p::fmpz=fmpz(1))

  O = I.O
  @hassert :CSAMaxOrd 1 Hecke.check_associativity(O.A)
  @hassert :CSAMaxOrd 1 Hecke.check_distributivity(O.A)
  @hassert :CSAMaxOrd 1 check_ideal(I)
  bmatinv, deno =pseudo_inv(I.basis_mat)
  if isdefined(I, :gens) && length(I.gens)<O.dim
    m=zero_matrix(FlintZZ, O.dim*length(I.gens), O.dim)
    for i=1:length(I.gens)
      M=representation_matrix(I.gens[i])
      mul!(M, M, bmatinv)
      if deno==1
        for s=1:O.dim
          for t=1:O.dim
            m[t+(i-1)*(O.dim),s]=M[s,t]
          end
        end
      else
        for s=1:O.dim
          for t=1:O.dim
            @hassert :CSAMaxOrd 1 divisible(M[s,t], deno)
            m[t+(i-1)*(O.dim),s]=divexact(M[s,t], deno)
          end
        end
      end
    end
  else
    B= I.basis_alg
    m=zero_matrix(FlintZZ, O.dim^2, O.dim)
    for i=1:O.dim
      M=representation_matrix(B[i])
      mul!(M, M, bmatinv)
      if deno==1
        for s=1:O.dim
          for t=1:O.dim
            m[t+(i-1)*(O.dim),s]=M[s,t]
          end
        end
      else
        for s=1:O.dim
          for t=1:O.dim
            @hassert :CSAMaxOrd 1 divisible(M[s,t], deno)
            m[t+(i-1)*(O.dim),s]=divexact(M[s,t], deno)
          end
        end
      end
    end
  end
  #In the case of the p-radical, it is important to do this modulo p
  if p==1
    m = hnf(m)
  else
    hnf_modular_eldiv!(m, p)
  end
  s = prod(m[i,i] for i=1:cols(m))
  if s==1
    return AlgAssOrd(O.A, deepcopy(O.basis_mat))
  end
  # n is upper right HNF
  n=transpose(sub(m, 1:O.dim, 1:O.dim))
  b= FakeFmpqMat(pseudo_inv(n))
  O1=AlgAssOrd(O.A, mul!(b,b,O.basis_mat))
  O1.disc=divexact(O.disc, s^2)
  @hassert :CSAMaxOrd 1 check_order(O1)
  return O1
end



###############################################################################
#
#  p-radical
#
###############################################################################

function assure_basis_mat_inv(O::AlgAssOrd)
  if !isdefined(O, :basis_mat_inv)
    O.basis_mat_inv=inv(O.basis_mat)
  end
  return nothing
end

function pradical_meataxe(O::AlgAssOrd, p::Int)
  
  A1 = quo(O, p)
  lM = fq_nmod_mat[transpose(representation_matrix(A1[i])) for i=1:O.dim]
  M = FqGModule(lM)
  ls = minimal_submodules(M)
  l = sum(rows(x) for x in ls)
  M1 = zero_matrix(base_ring(A1), l, O.dim)
  i=1
  for x in ls
    for j=1:rows(x)
      for k=1:O.dim
        M1[i,k]=x[j,k]
      end
      i+=1
    end
  end
  r = rref!(M1)
  if r == O.dim
    J= AlgAssOrdIdl(O,MatrixSpace(FlintZZ, O.dim, O.dim, false)(p))
    J.gens=AlgAssOrdElem[O(p*one(O.A))]
    return J
  end
  M1 = sub(M1, 1:r, 1:O.dim)
  dM = transpose(nullspace(M1)[2])
  gens=Vector{AlgAssOrdElem}(rows(dM)+1)
  m = zero_matrix(FlintZZ, O.dim, O.dim)
  for i=1:rows(dM)
    for j=1:cols(dM)
      m[i,j]=FlintZZ(coeff(dM[i,j],0))
    end
    gens[i]= elem_from_mat_row(O,m,i)
  end
  hnf_modular_eldiv!(m, fmpz(p))
  gens[rows(dM)+1]=O(p*one(O.A))
  J=AlgAssOrdIdl(O,m)
  J.gens=gens
  return J

end



doc"""
***
    pradical(O::AlgAssOrd, p::Int)
            
> Given an order O and a prime p, it returns the radical of the ideal generated by p
"""

function pradical(O::AlgAssOrd, p::Int)
  
  #See the paper from Ronyai, Structure of finite algebra
  l=clog(fmpz(O.dim),p)
  if l>1
    return pradical_meataxe(O,p)
  end
  n=root(O.dim,2)
    
  F=ResidueRing(FlintZZ, p, cached=false)


  #First step: kernel of the trace matrix mod p 
  W=MatrixSpace(F,O.dim,O.dim, false)
  I=W(n*redtrace_mat(O))
  k,B=nullspace(I)
  # The columns of B give the coordinates of the elements in the order.
  if k==0
    J= AlgAssOrdIdl(O,MatrixSpace(FlintZZ, O.dim, O.dim, false)(p))
    J.gens=AlgAssOrdElem[O(p*one(O.A))]
    return J
  end

  if l==1
    #In this case, we can output I: it is the standard p-trace method.
    M=zero_matrix(FlintZZ, O.dim, O.dim)
    for i=1:cols(B)
      for j=1:O.dim
        M[i,j]=B[j,i].data
      end
    end
    M1=hnf_modular_eldiv!(M, fmpz(p))
    res=AlgAssOrdIdl(O,sub(M1,1:O.dim,1:O.dim))
    B1=lift(B')
    res.gens=Array{AlgAssOrdElem, 1}(k+1)
    for i=1:k
      res.gens[i]= elem_from_mat_row(O,B1,i)
    end
    res.gens[k+1]= O(p*one(O.A))
    @hassert :CSAMaxOrd 1 check_pradical(res,p)
    return res
  end
  
  Ide=transpose(lift(B))
  #Now, iterate: we need to find the kernel of tr((xy)^(p^i))/p^i mod p
  #on the subspace generated by I
  #Hard to believe, but this is linear on I!!!!
  for i=1:l
    N=zero_matrix(F, O.dim, rows(Ide))
    a=O.A()
    for t=1:rows(Ide)
      elm=elem_from_mat_row(O,Ide,t)
      for s=1:O.dim
        mul!(a, elm.elem_in_algebra, O.basis_alg[s])
        bbb = (a^(p^i))
        trel=trace(bbb)
        el=divexact(numerator(trel),p^i)
        N[s,t]=F(el)
      end
    end
    k, B2=nullspace(N)
    if k==0
      J= AlgAssOrdIdl(O,MatrixSpace(FlintZZ, O.dim, O.dim, false)(p))
      J.gens=AlgAssOrdElem[O(p*one(O.A))]
      return J
    end
    Ide=lift(transpose(B2))*Ide
  end
  gens = Vector{AlgAssOrdElem}(rows(Ide)+1)
  for i in 1:rows(Ide)
    gens[i] = elem_from_mat_row(O, Ide, i)
  end
  gens[rows(Ide)+1]= O(p*one(O.A))
  #Now, I have to give a basis for the ideal.
  m=zero_matrix(FlintZZ, O.dim, O.dim)
  for i=1:rows(Ide)
    for j=1:cols(Ide)
      m[i,j]=Ide[i,j]
    end
  end
  hnf_modular_eldiv!(m,fmpz(p))
  res=AlgAssOrdIdl(O,m)
  res.gens=gens
  @hassert :CSAMaxOrd 1 check_pradical(res,p)
  return res
  
end

###############################################################################
#
#  Trace, Discriminant and Reduced Trace Matrix 
#
###############################################################################


function representation_matrix(x::AlgAssOrdElem)

  O = parent(x)
  M = O.basis_mat
  if isdefined(O, :basis_mat_inv)
    M1 = O.basis_mat_inv
  else
    M1 = inv(O.basis_mat)
    O.basis_mat_inv=M1
  end
  B = FakeFmpqMat(representation_matrix(x.elem_in_algebra))
  mul!(B, M, B)
  mul!(B, B, M1)

  @assert B.den==1
  return B.num
end

function trace(x::AlgAssOrdElem)
  return trace(x.elem_in_algebra)
end

function redtrace_mat(O::AlgAssOrd)

  A=O.A
  if isdefined(O, :trace_mat)
    return O.trace_mat
  end
  x=O.basis_alg
  m=length(x)
  n=root(O.dim,2)
  M=zero_matrix(FlintZZ, m, m)
  a=A()
  for i=1:m
    mul!(a, x[i], x[i])
    M[i,i]=divexact(numerator(trace(a)),n)
  end
  for i=1:m
    for j=i+1:m
      mul!(a, x[i], x[j])
      b=divexact(numerator(trace(a)),n)
      M[i,j]=b
      M[j,i]=b
    end
  end
  O.trace_mat=M
  return M
  
end

function discriminant(O::AlgAssOrd) 
  
  if isdefined(O, :disc)
    return O.disc
  end
  M=redtrace_mat(O)
  O.disc=det(M)
  return O.disc

end


###############################################################################
#
#  Schur Index at Infinity
#
###############################################################################


#Steel Nebe paper
doc"""
***
    schur_index_at_real_plc(O::AlgAssOrd)
        
> Given an order O, this function returns the schur index 
> of the algebra over the field of real numbers
"""
function schur_index_at_real_plc(O::AlgAssOrd)
  
  x=trace_signature(O)
  n=root(O.dim,2)
  if x[1]==divexact(n*(n+1),2)
    return 1
  else
    return 2
  end
  
end


function trace_signature(O::AlgAssOrd)
  
  M=redtrace_mat(O)
  # This can be improved using Sturm sequences
  Zx,x=PolynomialRing(FlintZZ, "x")
  f=charpoly(Zx,M)
  if issquarefree(f)
    p=64
    while p<1024
      sgtposf=0
      sgtnegf=0
      R=AcbField(p, false)
      Rx=AcbPolyRing(R, Symbol("x"), false)
      g=Rx(f)
      l=roots(g)
      for i=1:length(l)
        y=real(l[i])
        if ispositive(y)
          sgtposf+=1
        end
        if isnegative(y)
          sgtnegf+=1
        end
      end
      if sgtposf+sgtnegf==degree(g)
        return sgtposf, sgtnegf
      else
        p*=2
      end
    end
    if p>1024
      error("Precision issue")
    end
#=    
  if issquarefree(f)
    a=number_positive_roots(f)
   b=degree(f)-a
    return (a,b)
=#
  else
    ff=factor(f)
    sgtpos=0
    sgtneg=0
    for (h,v) in ff.fac
      if degree(h)==1
        if coeff(h,0)>0
          sgtneg+=v
        else
          sgtpos+=v
        end
        continue
      end
      p=64
      while p<1024
        sgtposf=0
        sgtnegf=0
        R=AcbField(p, false)
        Rx=AcbPolyRing(R, Symbol("x"), false)
        g=Rx(h)
        l=roots(g)
        for i=1:length(l)
          y=real(l[i])
          if ispositive(y)
            sgtposf+=1
          end
          if isnegative(y)
            sgtnegf+=1
          end
        end
        if sgtposf+sgtnegf==degree(h)
          sgtpos+=sgtposf*v
          sgtneg+=sgtnegf*v
          break
        else
          p*=2
        end
      end
      if p>1024
        error("Precision issue")
      end
    end
    return (sgtpos, sgtneg)
  end
  
end


###############################################################################
#
#  Schur Index at p
#
###############################################################################

doc"""
***
    schur_index_at_p(O::AlgAssOrd, p::fmpz)
        
> Given a maximal order O and a prime p, this function returns the schur index 
> of the completion of the algebra at p 
"""
function schur_index_at_p(O::AlgAssOrd, p::fmpz)
  @assert O.ismaximal==1
  d=discriminant(O)
  v=valuation(d,p)
  if v==0
    return 1
  end
  n=root(O.dim,2)
  t = n - divexact(v,n)
  return divexact(n,t)
end


###############################################################################
#
#  p-maximal overorder
#
###############################################################################

function _maximal_ideals(O::AlgAssOrd, p::Int)
  
  A1 = quo(O, p)
  lM = fq_nmod_mat[representation_matrix(A1[i]) for i=1:O.dim]
  append!(lM, fq_nmod_mat[representation_matrix(A1[i], :right) for i=1:O.dim])
  M = FqGModule(lM)
  ls = maximal_submodules(M)
  ideals=AlgAssOrdIdl[]
  poneO=O(p*one(O.A))
  for x in ls
    @hassert :CSAMaxOrd 1 closure(x, M.G)==rref(x)[2]
    m = zero_matrix(FlintZZ, O.dim, O.dim)
    gens=Vector{AlgAssOrdElem}(rows(x)+1)
    for i=1:rows(x)
      for j=1:cols(x)
        m[i,j]=FlintZZ(coeff(x[i,j],0))
      end
      gens[i]= elem_from_mat_row(O,m,i)
    end
    hnf_modular_eldiv!(m, fmpz(p))
    gens[rows(x)+1]=poneO
    J=AlgAssOrdIdl(O,m)
    J.gens=gens
    push!(ideals, J)
  end
  return ideals

end

function pmaximal_overorder(O::AlgAssOrd, p::Int)

  d=discriminant(O)
  if rem(d, p^2) != 0  
    return O
  end

  if p>O.dim
    return pmaximal_overorder_trace(O,p)
  else
    return pmaximal_overorder_meataxe(O,p)
  end
end

function pmaximal_overorder_meataxe(O::AlgAssOrd, p::Int)

  extend = false
  d=discriminant(O)
  while true
    dd = fmpz(1)
    max_id =_maximal_ideals(O, p)
    for i = 1:length(max_id)
      OO = ring_of_multipliers(max_id[i], fmpz(p))
      dd = discriminant(OO)
      if d != dd
        extend = true
        O = OO
        d = dd
        break
      end
    end

    if extend
      v = valuation(dd, p)
      if v == 0 || v == 1
        break
      end
      extend = false
      continue
    else
      break
    end
    
  end
  return O
end

function pmaximal_overorder_trace(O::AlgAssOrd, p::Int)

  #First, the head order by computing the pradical and its ring of multipliers
  d=discriminant(O)
  I=pradical(O,p)
  OO=ring_of_multipliers(I, fmpz(p))
  dd=discriminant(OO)
  while dd!= d
    O=OO
    I=pradical(O,p)
    OO=ring_of_multipliers(I, fmpz(p))
    dd=discriminant(OO)
  end
  #Now, we have to check the maximal ideals.
  extend = false
  while true
    dd = fmpz(1)
    max_id =_maximal_ideals(O, p)
    for i = 1:length(max_id)
      OO = ring_of_multipliers(max_id[i], fmpz(p))
      dd = discriminant(OO)
      if d != dd
        extend = true
        O = OO
        d = dd
        break
      end
    end

    if extend
      v = valuation(dd, p)
      if v == 0 || v == 1
        break
      end
      extend = false
      continue
    else
      break
    end
    
  end
  return O
end

###############################################################################
#
#  Maximal Order
#
###############################################################################

doc"""
***
    MaximalOrder(O::AlgAssOrd)
        
> Given an order O, this function returns a maximal order containing O
"""

function MaximalOrder(O::AlgAssOrd)
  @vtime :NfOrd fac = factor(root(abs(discriminant(O)),2))
  OO=O
  for (p,j) in fac
    OO = pmaximal_overorder(OO, Int(p))
  end
  OO.ismaximal=1
  return OO
end


###############################################################################
#
#  IsSplit
#
###############################################################################

doc"""
***
    issplit(A::AlgAss)
        
> Given a Q-algebra A, this function returns true if A splits over Q, false otherwise
"""

function issplit(A::AlgAss)
  O=Hecke.AlgAssOrd(A, [A[i] for i=1:dim(A)])
  i=schur_index_at_real_plc(O)
  if i==2
    return false
  end  
  fac = factor(root(abs(discriminant(O)),2))
  for (p,j) in fac
    O1 = pmaximal_overorder(O, Int(p))
    if valuation(O1.disc, Int(p))!=0
      return false
    end
  end
  return true

end


###############################################################################
#
#  Sturm sequence
#
#########à#####################################################################

function sturm_sequence(f::fmpq_poly)

  g=f
  h=derivative(g)
  seq=fmpq_poly[g,h]
  while true
    q, r=divrem(g,h)
    if r!=0
      push!(seq, -r)
      g=h
      h=r
    else 
      break
    end
  end
  return seq

end

function _number_changes(a::Array{fmpz,1})
  nc=0
  filter!(x -> x!=0, a)
  for i=2:length(a)
    if sign(a[i])!=sign(a[i-1])
      nc+=1
    end
  end  
  return nc
end

function number_positive_roots(f::fmpz_poly)

  Qx, x=PolynomialRing(FlintQQ, "z")
  f1 = Qx(f)
  s = sturm_sequence(f1)
  evinf=fmpz[numerator(coeff(x, degree(x))) for x in s]
  ev0=fmpz[numerator(coeff(x,0)) for x in s]
  return _number_changes(ev0)-_number_changes(evinf)
end


