
export meataxe, charpoly, composition_factors, composition_series


####################################################################
#
#  Utilities for MeatAxe
#
#####################################################################


#
# Given a matrix $M$ in echelon form and a vector, it returns
# the vector reduced with respect to $M$
#
function cleanvect(M::MatElem, v::MatElem)
  
  @assert rows(v)==1
  w=deepcopy(v)
#  println("M=",M, "\n","v=",v, "\n")
  if iszero(v)
    return w  
  end
  for i=1:rows(M)
    ind=1
    while M[i,ind]==0
      ind+=1
    end
    if iszero(w[1,ind])
      continue
    end
    mult=w[1,ind]//M[i,ind]
    w[1,ind]=parent(M[1,1])(0)
    for k=ind+1:cols(M)
      w[1,k]-= mult*M[i,k]
    end      
  end
  return w

end

function cleanmat(M::MatElem,N::MatElem)
  
  S=MatrixSpace(parent(M[1,1]), rows(N),cols(N))()
  for i=1:nrows(N)
    v=MatrixSpace(parent(M[1,1]), 1 ,cols(N))()
    for j=1:cols(N)
      v[j]=N[i,j]
    end
    w=cleanvec(M,v)
    for j=1:cols(N)
      S[i,j]=w[j]
    end
  end
  return S
  
end


function submatrix(M::MatElem, x::UnitRange{Int}, y::UnitRange{Int})
  
  numrows=x.stop-x.start+1
  numcols=y.stop-y.start+1
  A=MatrixSpace(parent(M[1,1]), numrows, numcols)()
  for i=1:numrows
    for j=1:numcols
      A[i,j]=M[x.start+i-1, y.start+j-1]
    end
  end
  return A
  
end


#
#  Given a matrix C containing the coordinates of vectors v_1,dots, v_k 
#  in echelon form, the function computes a basis for the submodule they generate
# 

function closure(C::MatElem, G)

  rref!(C)
  i=1
  while i != rows(C)+1
    for j=1:length(G)
      res= cleanvect(C,submatrix(C, i:i, 1:cols(C))*G[j])
      if !iszero(res)
        C=vcat(C,res)
      end
    end  
    i+=1
  end
  return C

end

#
#  Given a matrix C containing the coordinates of vectors v_1,dots, v_k,
#  the function computes a basis for the submodule they generate
# 

function spinning(C::MatElem,G)

  preimage=[i for i=1:rows(C)]
  gens=[0 for i=1:rows(C)]
  X=rref(C)[2]
  B=deepcopy(C)
  i=1
  while i != rows(B)+1
    for j=1:length(G)
      el=submatrix(B, i:i, 1:cols(B))*G[j]
#      println("X=", X, "\n")
      res= cleanvect(X,el)
#      println("el=", el, "\n res=", res, "\n")
      if !iszero(res)
        X=vcat(X,res)
        rref!(X)
        B=vcat(B,el)
        push!(gens,j)
        push!(preimage,i)
      end
    end  
    i+=1
  end
  return B,gens, preimage
  

end


#
#  Function to obtain the action of G on the quotient and on the submodule
#


function clean_and_quotient(M::MatElem,N::MatElem,pivotindex::Set{Int})
  
  
  coeff=MatrixSpace(parent(M[1,1]),rows(N),rows(M))()
  for i=1:rows(N)
    for j=1:rows(M)
      ind=1
      while iszero(M[j,ind])
        ind+=1
      end
      coeff[i,j]=N[i,ind]//M[j,ind]  
      for s=1:cols(N)
        N[i,s]-=coeff[i,j]*M[j,s]
      end
    end
  end 
  vec= MatrixSpace(parent(M[1,1]),rows(N),cols(M)-length(pivotindex))()
  for i=1:rows(N)  
    pos=0
    for s=1:cols(M)
      if !(s in pivotindex)
        pos+=1
        vec[i,pos]=N[i,s]
      end 
    end
  end
  return coeff, vec
end

function _split(C::MatElem,G)
# I am assuming that C is a Fp[G]-submodule
  equot=MatElem[]
  esub=MatElem[]
  pivotindex=Set{Int}()
  for i=1:rows(C)
    ind=1
    while iszero(C[i,ind])
      ind+=1
    end
    push!(pivotindex,ind)   
  end
  for a=1:length(G)
    subm,vec=clean_and_quotient(C, C*G[a],pivotindex)
    push!(esub,subm)
    s=MatrixSpace(parent(C[1,1]),cols(G[1])-length(pivotindex),cols(G[1])-length(pivotindex))()
    pos=0
    for i=1:rows(G[1])
      if !(i in pivotindex)
        m,vec=clean_and_quotient(C,submatrix(G[a],i:i,1:rows(G[1])),pivotindex)
        for j=1:cols(vec)
          s[i-pos,j]=vec[1,j]
        end
      else 
        pos+=1
      end
    end
    push!(equot,s)
  end
  return esub,equot,pivotindex

end

#
#  Function that determine if two G-modules are isomorphic
#

function isisomorphic{T}(G::Array{T,1},H::Array{T,1})
  
 @assert length(G)==length(H)
  
#  println("Alive")
  if cols(G[1])!=cols(H[1])
    return false
  end

  K=parent(G[1][1,1])
#  @assert isfinite(order(K))
  Kx,x=K["x"]
  n=cols(G[1])
  A=MatrixSpace(K,n,n)()
  B=MatrixSpace(K,n,n)()
  lincomb=Int[]
  f=Kx(1)
#  counteris=0

  while true
    
    for i=1:length(G)
      push!(lincomb,rand(1:10))
      A+=lincomb[i]*G[i]
    end
#    counteris+=1
#    println("counteris:", counteris)

    cp=char_poly(A)
    sq=factor_squarefree(cp)
    lf=factor(collect(keys(sq.fac))[1])
    for t in keys(lf.fac)
      if degree(t)==n-rank(t(A))
        f=t
        break  
      end
    end
    if degree(f)==n-rank(f(A))
      break
    else 
      lincomb=Int[]
      A=MatrixSpace(K,n,n)()
    end
  end
  for i=1:length(G)
    B+=lincomb[i]*H[i]
  end
  
  M=f(A)
  a,kerA=nullspace(transpose(M))
  kerA=transpose(kerA)
  
  N=f(B)
  b,kerB=nullspace(transpose(M))
  kerA=transpose(kerA)

  if a!=b
    return false
  end
  
  M, gensA, preimageA = spinning(submatrix(kerA, 1:1, 1:n), G)
  N, gensB, preimageB = spinning(submatrix(kerB, 1:1, 1:n), H)
  
  
  for i=1:length(G)
    if M*G[1]*inv(M) != N*H[1]*inv(N)
      return false
    end
  end
  return true
end

###############################################################
#
#  Characteristic Polynomial
#
#################################################################


function ordpoly(M::MatElem,S::MatElem,v::MatElem)

  K=parent(M[1,1])
  D=cleanvect(S,v)
  C=MatrixSpace(K, 1, cols(M)+1)()
  C[1,1]=K(1)
  if iszero(D)
    return C
  end
  ind=2
  vec=v
  while true
    vec=vec*M
    D=vcat(D, cleanvect(S,vec))
    E=MatrixSpace(K, 1, cols(M)+1)()
    E[1,ind]=K(1)
    C=vcat(C,E)
    for i=1:ind-1
      nonzero=1
      while iszero(D[i, nonzero])
      nonzero+=1
      end
      mult=D[ind,nonzero]//D[i,nonzero]
      for j=1:cols(M)+1
        C[ind,j]-=mult*C[i,j]
      end
      for j=1:cols(M)
        D[ind,j]-=mult*D[i,j]
      end
    end
    if iszero(submatrix(D, ind:ind, 1:cols(D)))
      break
    end
    ind+=1
  end
  return submatrix(C, ind:ind, 1:cols(D)+1), submatrix(D, 1:ind-1, 1:cols(D))
  
end

function charpoly_fact(M::MatElem)
  
  @assert cols(M)>0 && cols(M)==rows(M) 
  
  K=parent(M[1,1])
  polys=[]
  v=MatrixSpace(K, 1, cols(M))()
  v[1,1]=K(1)
  pol,B=ordpoly(M,MatrixSpace(K, 0, 0)(),v)
#  println("In Ordpoly, B=", B, "\n")
  push!(polys,pol)
  if pol[1,cols(B)+1]!=0
    return polys
  end
  v[1,1]=K(0)
  for i=2:cols(M)
    v[1,i]=K(1)
    red=cleanvect(B,v)
    if !iszero(red)
      x=ordpoly(M,B,red)
      push!(polys,x[1])
      B=vcat(B,x[2])
    end
    v[1,i]=K(0)
  end
  return polys
end


doc"""
***
    charpoly(M::MatElem) -> PolyElem

> Returns the characteristic polynomial of the square matrix M

"""

function charpoly(M::MatElem)
  
  @assert rows(M)>0 && rows(M)==cols(M)
  K=parent(M[1,1])
  Kx,x=K["x"]
  polys=charpoly_fact(M)
  f=Kx(1)
  for pol in polys
    coeff=[pol[1,i] for i=1:cols(pol)]
    f*=Kx(coeff)
  end
  return f
end


#################################################################
#
#  MeatAxe, Composition Factors and Composition Series
#
#################################################################



doc"""
***
    meataxe(G::Array{MatElem,1}) -> Bool, MatElem

> Given a set of matrices $G$, returns true if the module is irreducible (and the identity matrix) and false if the space is reducible, togheter with a basis of a submodule\

"""

function meataxe{T}(G::Array{T,1})

  K=parent(G[1][1,1])
#  @assert isfinite(order(K))
  Kx,x=K["x"]
  n=cols(G[1])
#  counter=0
  while true
#    counter+=1
 #   println(counter)
  #
  # First, choose a random combination of the generators of G
  #
    A=MatrixSpace(K,n,n)()
    for i=1:length(G)
      A+=rand(1:10)*G[i]
    end
 
  #
  # Compute the characteristic polynomial and, for irreducible factor f, try the Norton test
  # 
    poly=charpoly_fact(A)
    for fact in poly
      c=[fact[1,i] for i=1:cols(fact)]
      sq=factor_squarefree(Kx(c))
      lf=factor(collect(keys(sq.fac))[1])
      for t in keys(lf.fac)
        M=t(A)
        a,kern=nullspace(transpose(M))
        kern=transpose(kern)
#        println("kern=", kern, "\n")
  
        #
        #  Norton test
        #   
        for j=1:rows(kern)  
          B=closure(submatrix(kern,j:j, 1:n),G)
  #        println("Spinning returns ", B, "\n")
          if rows(B)!=n
            return false, B
          end
        end
  #        println("Passing to dual\n")
        
        kernt=nullspace(M)[2]
        
        for j=1:cols(kernt)
          Bt=closure(transpose(submatrix(kernt,1:n,j:j)),[transpose(x) for x in G])
  #        println("Dual spinning returns ",Bt, "\n")
          if rows(Bt)!=n
            subs=nullspace(transpose(Bt))[2]
            return false, transpose(subs)
          end
        end
        if degree(t)==a
#           println("f is a good factor, irreducibility!")
          return true, eye(G[1],n)
        end
      end
    end
  end
end

doc"""
***
    composition_series(G::Array{MatElem,1}) -> Array{MatElem,1}

> Given a set of matrices $G$, returns a sequence of submodules such that the quotient of two consecutive submodules is irreducible

"""



function composition_series{T}(G::Array{T,1})

  K=parent(G[1][1,1])
  bool, C = meataxe(G)
  #
  #  If the module is irreducible, we just return a basis of the space
  #
  if bool ==true
    return [eye(G[1],rows(G[1]))]
  end
  #
  #  The module is reducible, so we call the algorithm on the quotient and on the subgroup
  #
  esub,equot,pivotindex=_split(C,G)
  sub_list = composition_series(esub)
  quot_list = composition_series(equot)
  #
  #  Now, we have to write the submodules of the quotient and of the submodule in terms of our basis
  #
  list=MatElem[]
  for a in sub_list
    m=MatrixSpace(K,rows(a), cols(C))()
    for i=1:rows(a)
      for s=1:cols(a)
        for j=1:cols(C)
          m[i,j]+=a[i,s]*C[s,j]
        end
      end
    end
    push!(list,m)
  end
  for a in quot_list
    s=MatrixSpace(K,rows(a), cols(C))()
    for i=1:rows(a)
      pos=0
      for j=1:cols(C)
        if j in pivotindex
          pos+=1
        else
          s[i,j]=a[i,j-pos]
        end
      end
    end
    push!(list,vcat(C,s))
  end
  return list
end

doc"""
***
    composition_factors(G::Array{MatElem,1})

> Given a set of matrices $G$ determining a module $M$, returns, up to isomorphism, the composition factors of $M$ with their multiplicity

"""



function composition_factors{T}(G::Array{T,1})
  
  K=parent(G[1][1,1])
  bool, C = meataxe(G)
  #
  #  If the module is irreducible, we just return a basis of the space
  #
  if bool == true
    return [[G,1]]
  end
  #
  #  The module is reducible, so we call the algorithm on the quotient and on the subgroup
  #
  esub,equot,pivotindex=_split(C,G)
  sub_list = composition_factors(esub)
  quot_list = composition_factors(equot)
  #
  #  Now, we check if the factors are isomorphic
  #
  list=vcat(sub_list,quot_list)
  i=1
  while i<=length(list)
    j=i+1
    while j<=length(list)
      if isisomorphic(list[i][1], list[j][1])
        list[i][2]+=list[j][2]
        deleteat!(list,j)
      end
      j+=1
    end
    i+=1
  end

  return list

end






#=

Qx,x=QQ["x"]
K,a=NumberField(x^2+87,"a")
O=maximal_order(K)
prime_decomposition(O,5)
F,mF=ResidueField(O,ans[1][1])

M=MatrixSpace(F,3,3)([0,0,1,1,0,0,0,1,0])


G=[M]

meataxe(G)

M=MatrixSpace(F,7,7)() 
M[7,6]=F(1)
M[6,5]=F(1)
M[5,4]=F(1)
M[4,3]=F(1)
M[3,2]=F(1)
M[2,1]=F(1)
M[1,7]=F(1)
=# 


