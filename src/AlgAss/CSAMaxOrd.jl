###############################################################################
#
#  Types
#
###############################################################################

mutable struct AlgAssOrd 
  A::AlgAss{fmpq}                  # CSA containing it
  dim::Int
  basis_alg::Vector{AlgAssElem}    # Basis as array of elements of the algebra
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
    r.ismaximal = 0
    return r
  end
  
  function AlgAssOrd(a::AlgAss{fmpq}, mat::FakeFmpqMat)
    r = new()
    r.A=a
    r.dim=size(a.mult_table,1)
    r.basis_alg=Array{AlgAssElem,1}(rows(mat))
    for i=1:length(r.basis_alg)
      r.basis_alg[i]=elem_from_mat_row(a,mat.num, i, mat.den)
    end
    r.basis_mat=mat
    r.ismaximal = 0
    return r
  end
  
end

mutable struct AlgAssOrdElem
  elem_in_algebra::AlgAssElem
  elem_in_basis::Vector{fmpz}
  has_coord::Bool
  parent::AlgAssOrd

  function AlgAssOrdElem(O::AlgAssOrd, a::AlgAssElem)
    z = new()
    z.elem_in_algebra = a
    z.elem_in_basis = Vector{fmpz}(length(O.basis_alg))
    z.parent = O
    z.has_coord = false
    return z
  end

  function AlgAssOrdElem(O::AlgAssOrd, a::AlgAssElem, arr::Array{fmpz, 1})
    z = new()
    z.parent = O
    z.elem_in_algebra = a
    z.has_coord = true
    z.elem_in_basis = arr
    return z
  end

  function AlgAssOrdElem(O::AlgAssOrd, arr::Array{fmpz, 1})
    z = new()
    z.elem_in_algebra = dot(O.basis_alg, arr)
    z.has_coord = true
    z.elem_in_basis = arr
    z.parent = O
    return z
  end

end

mutable struct AlgAssOrdIdl
  O::AlgAssOrd                     # Order containing it
  basis_alg::Vector{AlgAssOrdElem} # Basis of the ideal as array of elements of the order
  basis_mat::fmpz_mat              # Basis matrix of ideal wrt basis of the order
  
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

parent(x::AlgAssOrdElem)=x.parent

function *(n::Int, x::AlgAssOrdElem)

  O=x.parent
  y=Array{fmpz,1}(O.dim)
  for i=1:O.dim
    y[i]=n*x.elem_in_basis[i]
  end
  return AlgAssOrdElem(O,y)
  
end

function ideal(O::AlgAssOrd, mat::fmpz_mat)
  return AlgAssOrdIdl(O,mat)
end

(O::AlgAssOrd)(a::AlgAssElem) = begin
  if !isdefined(O, :basis_mat_inv)
    O.basis_mat_inv=inv(O.basis_mat)
  end
  x=FakeFmpqMat(a.coeffs)*O.basis_mat_inv
  @assert denominator(x)==1
  return AlgAssOrdElem(O,vec(Array(x.num)))
end

function FakeFmpqMat(x::Array{fmpq,1})
  dens=[denominator(x[i]) for i=1:length(x)]
  den=lcm(dens)
  M=zero_matrix(FlintZZ, 1, length(x))
  for i=1:length(x)
    M[1,i]=numerator(x[i]*divexact(den, dens[i]))
  end
  return FakeFmpqMat(M,den)
end
#=
function FakeFmpqMat(x::fmpq_mat)
  den=lcm(denominator(x[i,j]) for i=1:rows(x) for j=1:cols(x))
  M=zero_matrix(FlintZZ, rows(x), cols(x))
  for i=1:rows(x)
    for j=1:cols(x)
      M[i,j]=numerator(x[i,j])*divexact(den, denominator(x[i,j]))
    end
  end
  return FakeFmpqMat(M,den)

end
=#
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

function elem_from_mat_row(O::AlgAssOrd, M::fmpz_mat, i::Int)
  return AlgAssOrdElem(O, [M[i,j] for j=1:O.dim])
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
#  Construction of a cross product algebra
#
###############################################################################
#=

Qx,x=PolynomialRing(FlintQQ, "x")
K,a=NumberField(x^2-7)
O=maximal_order(K);
cocval=Array{nf_elem,2}(degree(K), degree(K))
G=Hecke.automorphisms(K)
G=[G[2],G[1]]
cocval[1,1]=K(1)
cocval[1,2]=K(1)
cocval[2,1]=K(1)
cocval[2,2]=K(-1)
A=Hecke.CrossedProductAlgebra(K,G,cocval)
O=Hecke.AlgAssOrd(A, [A[1], A[2], A[3], A[4]])
p=7
L=[p*O(A[1]), p*O(A[2]), p*O(A[3]), p*O(A[4])] 
I=Hecke.AlgAssOrdIdl(O,L)
=#
#K/Q is a Galois extension.
function CrossedProductAlgebra(K::AnticNumberField, G::Array{T,1}, cocval::Array{nf_elem, 2}) where T

  n=degree(K)
  
  #=
  Multiplication table
  I order the basis in this way:
  First, I put the basis of the Galois Group, then the product of them with the first
  element of basis of the order and so on...
  =#
  
  M=Array{fmpq,3}(n^2, n^2, n^2)
  for i=1:n^2
    for j=1:n^2
      for s=1:n^2
        M[i,j,s]=fmpq(0)
      end
    end
  end
  B=basis(K)
  for i=1:n
    for j=1:n
      #I have the element B[i]*G[j]
      for k=1:n
        for h=1:n
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


function find_elem(G::Array{T,1}, el::T) where T
  i=1
  while true
#    @show found= el.prim_img==G[i].prim_img
    if el.prim_img==G[i].prim_img
      return i
    end
    i+=1
  end
end


###############################################################################
#
#  p-overorder construction
#
###############################################################################

function ring_of_multipliers(I::AlgAssOrdIdl)
  O = I.O
  B=I.basis_alg
  bmatinv =FakeFmpqMat(pseudo_inv(I.basis_mat))
  # Riscrivere e anche nel caso commutativo perché questa cosa è letale.
  # Le moltiplicazioni vanno eseguite con mul! utilizzando un'unica matrice e 
  # copiando poi tutto in m, che deve essere definita una volta sola.
  # è il caso di distinguere tra determinante di bmatinv =1 e != 1
  # Nel primo caso, la moltiplicazione è tra fmpz_mat.
  # nel secondo caso, bisogna dividere le entrate per il denominatore.
  
  m = to_fmpz_mat(FakeFmpqMat(representation_mat(B[1].elem_in_algebra))*bmatinv)
  for i in 2:O.dim
    m = hcat(to_fmpz_mat(FakeFmpqMat(representation_mat(B[i].elem_in_algebra))*bmatinv),m)
  end
  n = hnf(transpose(m))
  # n is upper right HNF
  n = transpose(sub(n, 1:O.dim, 1:O.dim))
  b, d = pseudo_inv(n)
  return AlgAssOrd(O.A, FakeFmpqMat(b, d)*O.basis_mat)
end

function pradical(O::AlgAssOrd, p::Int)
  
  #See the paper from Ronyai, Structure of finite algebra
  basis=[O(p*O.basis_alg[i]) for i=1:O.dim]
  F,a=FlintFiniteField(p,1,"a", cached=false)
  l=clog(fmpz(O.dim),p)
  #First step: kernel of the trace matrix mod p 
  W=MatrixSpace(F,O.dim,O.dim)
  I=W(O.trace_mat)
  k,B=nullspace(I)
  # The columns of B give the coordinates of the elements in the order.
  if k==0
    return AlgAssOrdIdl(O,basis)
  end
  I=transpose(lift(B))
  if l==1
    #In this case, we can output I: it is the standard p-trace method.
    M1=zero_matrix(FlintZZ, rows(I)+O.dim, O.dim)
    for i=1:rows(I)
      for j=1:cols(I)
        M1[i,j]=I[i,j]
      end
    end
    for i=rows(I)+1:rows(I)+O.dim
      M1[i,i-rows(I)]=p
    end
    M2=hnf(M1)
    return AlgAssOrdIdl(O,sub(M2,1:O.dim,1:O.dim))
  end
  #Now, iterate: we need to find the kernel of tr((xy)^(p^i))/p^i mod p
  #on the subspace generated by I
  #Hard to believe, but this is linear on I!!!!
  for i=1:l
    list=[elem_from_mat_row(O,I,j) for j=1:rows(I)]
    @show list
    M=zero_matrix(F,  O.dim,rows(I))
    for s=1:rows(I)
      for t=1:cols(M)
        a=list[s].elem_in_algebra*O.basis_alg[t]
        prd=a^(p^i)
        trel=trace(prd)
        el=divexact(numerator(trel),p^i)
        M[t,s]=F(el)
      end
    end
    M
    k,B=nullspace(M)
    if k==0
      return AlgAssOrdIdl(O,basis)
    end
    I=transpose(lift(transpose(B))*I)
    @show I
  end
  s=rows(I)

  I=vcat(I,eye(I, O.dim))
  for i=1:O.dim
    for j=1:O.dim
      I[s+i, j]=basis[i].elem_in_algebra[j]
    end
  end
  return I
  
  

end

function lift(M::fq_nmod_mat)

  N=zero_matrix(FlintZZ, rows(M), cols(M))
  for i=1:rows(M)
    for j=1:cols(M)
      N[i,j]=FlintZZ(coeff(M[i,j],0))
    end
  end
  return N
end



###############################################################################
#
#  Trace, Discriminant and Reduced Trace Matrix 
#
###############################################################################


function trace(x::AlgAssElem)
  M=representation_mat(x)
  return trace(M)
end

function trace(x::AlgAssOrdElem)
  return trace(x.elem_in_algebra)
end

function redtrace_mat(O::AlgAssOrd)
  
  if isdefined(O, :trace_mat)
    return O.trace_mat
  end
  x=O.basis_alg
  n=O.dim
  M=zero_matrix(FlintZZ, length(x), length(x))
  for i=1:length(x)
    M[i,i]=divexact(numerator(trace(x[i]^2)),n)
  end
  for i=1:length(x)
    for j=i+1:length(x)
      M[i,j]=divexact(numerator(trace(x[i]*x[j])),n)
      M[j,i]=divexact(numerator(trace(x[i]*x[j])),n)
    end
  end
  O.trace_mat=M
  return M
  
end


function discriminant(O::AlgAssOrd) 

  M=redtrace_mat(O)
  return det(M)

end


###############################################################################
#
#  Schur Index at Infinity
#
###############################################################################


#Steel Nebe paper
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
      @show l=roots(g)
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
