add_assert_scope(:AlgAssOrd)
add_verbose_scope(:AlgAssOrd)

elem_type(::Type{AlgAssAbsOrd{S, T}}) where {S, T} = AlgAssAbsOrdElem{S, T}

elem_type(::AlgAssAbsOrd{S, T}) where {S, T} = AlgAssAbsOrdElem{S, T}

ideal_type(O::AlgAssAbsOrd{S, T}) where {S, T} = AlgAssAbsOrdIdl{S, T}

algebra(O::AlgAssAbsOrd) = O.algebra

################################################################################
#
#  Construction
#
################################################################################

function Order(A::S, B::Vector{T}) where {S <: AbsAlgAss, T <: AbsAlgAssElem}
  return AlgAssAbsOrd{S, T}(A, B)
end

function Order(A::S, basis_mat::FakeFmpqMat) where {S <: AbsAlgAss}
  return AlgAssAbsOrd{S}(A, basis_mat)
end

################################################################################
#
#  Index
#
################################################################################

function index(O::AlgAssAbsOrd)
  B = inv(O.basis_mat)
  n = det(B)
  @assert isinteger(n)
  return FlintZZ(n)
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function _assure_has_basis(O::AlgAssAbsOrd)
  if !isdefined(O, :basis)
    B = basis(O.algebra)
    v = Vector{AlgAssAbsOrdElem}(undef, degree(O))
    for i in 1:degree(O)
      w = sum(O.basis_mat.num[i, j]//O.basis_mat.den * B[j] for j in 1:degree(O))
      v[i] = O(w)
    end
    O.basis = v
  end
  return nothing
end

function assure_basis_mat_inv(O::AlgAssAbsOrd)
  if !isdefined(O, :basis_mat_inv)
    O.basis_mat_inv=inv(O.basis_mat)
  end
  return nothing
end

################################################################################
#
#  Basis
#
################################################################################

function basis(O::AlgAssAbsOrd, copy::Type{Val{T}} = Val{true}) where T
  _assure_has_basis(O)
  if copy == Val{true}
    return deepcopy(O.basis)
  else
    return O.basis
  end
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

function basis_mat(x::AlgAssAbsOrd, copy::Type{Val{T}} = Val{true}) where T
  if copy == Val{true}
    return deepcopy(x.basis_mat)
  else
    return x.basis_mat
  end
end

function basis_mat_inv(O::AlgAssAbsOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_basis_mat_inv(O)
  if copy == Val{true}
    return deepcopy(O.basis_mat_inv)
  else
    return O.basis_mat_inv
  end
end

################################################################################
#
#  Degree
#
################################################################################

function degree(O::AlgAssAbsOrd)
  return dim(O.algebra)
end

################################################################################
#
#  Inclusion of algebra elements
#
################################################################################

function _check_elem_in_order(a::T, O::AlgAssAbsOrd{S, T}, short::Type{Val{U}} = Val{false}) where {S, T, U}
  t = zero_matrix(FlintQQ, 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = FakeFmpqMat(t)
  t = t*basis_mat_inv(O, Val{false})
  if short == Val{true}
    return isone(t.den)
  elseif short == Val{false}
    if !isone(t.den)
      return false, Vector{fmpz}()
    else
      v = Vector{fmpz}(undef, degree(O))
      for i = 1:degree(O)
        v[i] = deepcopy(t.num[1, i])
      end
      return true, v
    end
  end
end

function in(x::T, O::AlgAssAbsOrd{S, T}) where {S, T}
  y = FakeFmpqMat(x.coeffs)
  if isdefined(O, :basis_mat_inv)
    M1 = O.basis_mat_inv
  else
    M1 = inv(O.basis_mat)
    O.basis_mat_inv = M1
  end
  if (y*M1).den == 1
    return true
  else
    return false
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

################################################################################
#
#  Random elements
#
################################################################################

function rand(O::AlgAssAbsOrd, R::UnitRange{T}) where T <: Integer
  return O(map(fmpz, rand(R, degree(O))))
end

function rand(O::AlgAssAbsOrd, n::Integer)
  return rand(O, -n:n)
end

function rand(O::AlgAssAbsOrd, n::fmpz)
  return rand(O, -BigInt(n):BigInt(n))
end

###############################################################################
#
#  Basis matrices from generators
#
###############################################################################

function basis_mat(A::Array{S, 1}) where {S <: AbsAlgAssElem}
  @assert length(A) > 0
  n = length(A)
  d = size(parent(A[1]).mult_table,1)

  M = zero_matrix(FlintZZ, n, d)

  dens = [lcm([denominator(A[i].coeffs[j]) for j=1:d]) for i=1:n]
  deno = lcm(dens)

  for i in 1:n
    for j in 1:d
      temp_den = divexact(deno, denominator(A[i].coeffs[j]))
      M[i, j] = numerator(A[i].coeffs[j]) * temp_den
    end
  end
  return FakeFmpqMat(M, deno)
end

function basis_mat(A::Array{AlgAssAbsOrdElem{S, T}, 1}) where S where T
  @assert length(A) > 0
  n = length(A)
  d = parent(A[1]).dim
  M = zero_matrix(FlintZZ, n, d)

  for i in 1:n
    el = elem_in_basis(A[i])
    for j in 1:d
      M[i, j] = el[j]
    end
  end
  return M
end

function order_gen(O::AlgAssAbsOrd)
  
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
        return AlgAssAbsOrd(O.algebra, hnf(N))
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
function +(a::AlgAssAbsOrd, b::AlgAssAbsOrd)
  aB = a.basis_mat
  bB = b.basis_mat
  d = a.dim
  c = sub(_hnf(vcat(bB.den*aB.num, aB.den*bB.num), :lowerleft), d + 1:2*d, 1:d)
  return Order(a.algebra, FakeFmpqMat(c, aB.den*bB.den))
end

###############################################################################
#
#  Print
#
###############################################################################

function show(io::IO, O::AlgAssAbsOrd)
  compact = get(io, :compact, false)
  if compact
    print(io, "Order of ")
    show(IOContext(io, :compact => true), O.algebra)
  else
    print(io, "Order of ")
    print(io, O.algebra)
    println(io, " with basis matrix ")
    print(io, basis_mat(O))
  end
end

###############################################################################
#
#  Quaternion algebras
#
###############################################################################

function quaternion_algebra(a::Int, b::Int)
  
  M = Array{fmpq,3}(undef, 4,4,4)
  for i = 1:4
    for j = 1:4
      for k = 1:4
        M[i,j,k] = 0
      end
    end
  end  
  M[1,1,1] = 1 # 1*1=1
  M[1,2,2] = 1 # 1*i=i
  M[1,3,3] = 1 # 1*j=j
  M[1,4,4] = 1 # 1*ij=1
  
  M[2,1,2] = 1
  M[2,2,1] = a
  M[2,3,4] = 1
  M[2,4,3] = a
  
  M[3,1,3] = 1
  M[3,2,4] = -1
  M[3,3,1] = b
  M[3,4,2] = -b
  
  M[4,1,4] = 1
  M[4,2,3] = -a
  M[4,3,2] = b
  M[4,4,1] = -a*b
  O = fmpq[1, 0, 0, 0]
  return AlgAss(FlintQQ, M, O)
  
end

###############################################################################
#
#  Quotient
#
###############################################################################

function quo(O::AlgAssAbsOrd, p::Int)
  # p must be prime

  R = GF(p, cached = false)
  M = Array{gfp_elem, 3}(undef, O.dim, O.dim, O.dim)
  x = fmpz[0 for i=1:O.dim]
  for i = 1:O.dim
    x[i] = 1
    N = representation_matrix(O(x))
    for j = 1:O.dim
      for k = 1:O.dim
        M[i, j, k] = R(N[j, k])
      end
    end
    x[i] = 0
  end
  oneO = elem_in_basis(O(one(O.algebra)))
  oneQ = gfp_elem[R(s) for s in oneO]
  return AlgAss(R, M, oneQ)
end

function _mod(x::fmpz_mat, y::fmpz_mat, pivots::Array{Int,1})
   
   for i=1:length(pivots)
     for k=1:cols(x)
       z = div(x[pivots[i],k], y[k,k])
       if z!=0
         for j=k:cols(x)
           x[pivots[i],j]-=z*y[k,j]
         end
       end
     end     
   end
   return nothing
end


function quo(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl, p::Int)
  
  pivots=Int[]
  for i=1:O.dim
    if I.basis_mat[i,i]==p
      push!(pivots, i)
    end
  end
  @hassert :AlgAssOrd 1 check_ideal(I)
  F= GF(p, cached = false)
  M=Array{gfp_elem, 3}(undef, length(pivots), length(pivots), length(pivots))
  x=fmpz[0 for s=1:O.dim]
  for i=1:length(pivots)
    x[pivots[i]]=1
    y=O(x)
    N=representation_matrix(y)
    _mod(N, I.basis_mat, pivots)
    for j = 1:length(pivots)
      #reduce the vector with respect to the ideal.
      #I assume that the basis of the ideal is in upper triangular HNF 
      for k = 1:length(pivots)
        M[i,j,k] = F(N[pivots[j],pivots[k]])
      end
    end
    x[pivots[i]] = 0
  end
  oneO = elem_in_basis(O(one(O.algebra)))
  #I reduce the entry of the element
  for i=1:dim(O.algebra)
    z = div(x[i], I.basis_mat[i,i])
    if z != 0
      for j=i:length(x)
        x[j] -= z*I.basis_mat[i,j]
      end
    end
  end
  oneA = Array{gfp_elem, 1}(undef, length(pivots))
  for i=1:length(pivots)
    oneA[i] = F(oneO[pivots[i]])
  end
  A = AlgAss(F, M, oneA)
  function AtoO(a::AlgAssElem)
    x = fmpz[0 for i=1:O.dim]
    for i=1:length(pivots)
      x[pivots[i]] = lift(a.coeffs[i])
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

function check_ideal(I::AlgAssAbsOrdIdl)
  
  O = order(I)
  B = basis(O)
  B1 = basis(I)
  for i = 1:length(B)
    for j = 1:length(B1)
      if !(B[i]*B1[j] in I)
        @show elem_in_basis(B[i]*B1[j])
        error("Ideal not closed under multiplication")
      end 
      if !(B1[j]*B[i] in I)
        @show elem_in_basis(B1[j]*B[i])
        error("Ideal not closed under multiplication")
      end 
    end 
  end
  return true
end

function ==(S::AlgAssAbsOrd, T::AlgAssAbsOrd)
  return basis_mat(S, Val{false}) == basis_mat(T, Val{false})
end

function defines_order(A::AlgAss{fmpq}, v::Array{AlgAssElem{fmpq, AlgAss{fmpq}}, 1})
  d = dim(A)
  M = zero_matrix(FlintQQ, d, d)
  for i in 1:d
    c = v[i].coeffs
    for j in 1:d
      M[i, j] = c[j]
    end
  end
  O = Order(A, FakeFmpqMat(M))
  b = _check_order(O)
  return b, FakeFmpqMat(M)
end

function _check_order(O::AlgAssAbsOrd)
  for x in O.basis_alg
    @assert denominator(minpoly(x))==1
    for y in O.basis_alg
      if !(x*y in O)
        return false
      end
    end
  end
  return true
end

function check_order(O::AlgAssAbsOrd)
  b = _check_order(O)
  if !b 
    error("Not an order")
  else
    return true
  end
end

function check_pradical(I::AlgAssAbsOrdIdl, p::Int)
  
  O= order(I)
  for i=1:O.dim
    x=elem_from_mat_row(O,I.basis_mat, i)
    assure_elem_in_algebra(x)
    for j=1:O.dim
      @assert divisible(numerator(tr(x.elem_in_algebra*O.basis_alg[j])), p)
    end
  end
  #=
  if p==2
    for i=1:O.dim
      x=elem_from_mat_row(O,I.basis_mat, i)
      for j=1:O.dim
        for k=1:clog(fmpz(O.dim), p)
          @assert divisible(numerator(tr((x.elem_in_algebra*O.basis_alg[j])^(p^k))), p^(k+1))
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

@doc Markdown.doc"""
***
    ring_of_multipliers(I::AlgAssAbsOrdIdl)
        
> Given an ideal I, it returns the ring (I : I)
"""

function ring_of_multipliers(I::AlgAssAbsOrdIdl, p::fmpz=fmpz(1))

  O = order(I)
  @hassert :AlgAssOrd 1 Hecke.check_associativity(O.algebra)
  @hassert :AlgAssOrd 1 Hecke.check_distributivity(O.algebra)
  @hassert :AlgAssOrd 1 check_ideal(I)
  bmatinv, deno = pseudo_inv(I.basis_mat)
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
            @hassert :AlgAssOrd 1 divisible(M[s,t], deno)
            m[t+(i-1)*(O.dim),s] = divexact(M[s,t], deno)
          end
        end
      end
    end
  else
    B = basis(I, Val{false})
    m = zero_matrix(FlintZZ, O.dim^2, O.dim)
    for i=1:O.dim
      M = representation_matrix(B[i])
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
            @hassert :AlgAssOrd 1 divisible(M[s,t], deno)
            m[t+(i-1)*(O.dim),s] = divexact(M[s,t], deno)
          end
        end
      end
    end
  end
  #In the case of the p-radical, it is important to do this modulo p
  if p == 1
    m = hnf(m)
  else
    hnf_modular_eldiv!(m, p)
  end
  s = prod(m[i,i] for i=1:cols(m))
  if s==1
    return O
  end
  # n is upper right HNF
  n = transpose(view(m, 1:O.dim, 1:O.dim))
  b = FakeFmpqMat(pseudo_inv(n))
  mul!(b, b, O.basis_mat)
  O1 = Order(O.algebra, b)
  O1.disc = divexact(O.disc, s^2)
  @hassert :AlgAssOrd 1 check_order(O1)
  return O1
end

###############################################################################
#
#  p-radical
#
###############################################################################

function pradical_meataxe(O::AlgAssAbsOrd, p::Int)
  
  A1 = quo(O, p)
  #@show dim(A1)
  @vtime :AlgAssOrd 1 lg = Hecke.gens(A1)
  #@show length(lg)
  lM = nmod_mat[transpose(representation_matrix(lg[i])) for i=1:length(lg)]
  #lM = nmod_mat[transpose(representation_matrix(A1[i])) for i=1:dim(A1)]
  M = ModAlgAss(lM)
  ls = minimal_submodules(M)
  l = sum(rows(x) for x in ls)
  M1 = zero_matrix(base_ring(A1), l, O.dim)
  i=1
  for x in ls
    for j=1:rows(x)
      for k=1:O.dim
        M1[i,k] = x[j,k]
      end
      i+=1
    end
  end
  r = rref!(M1)
  if r == O.dim
    J= AlgAssAbsOrdIdl(O, MatrixSpace(FlintZZ, O.dim, O.dim, false)(p))
    J.gens=AlgAssAbsOrdElem[O(p*one(O.algebra))]
    return J
  end
  M1 = view(M1, 1:r, 1:O.dim)
  dM = transpose(nullspace(M1)[2])
  gens=Vector{elem_type(O)}(undef, rows(dM)+1)
  m = zero_matrix(FlintZZ, O.dim, O.dim)
  for i=1:rows(dM)
    for j=1:cols(dM)
      m[i,j] = lift(dM[i,j])
    end
    gens[i]= elem_from_mat_row(O,m,i)
  end
  hnf_modular_eldiv!(m, fmpz(p))
  gens[rows(dM)+1]=O(p*one(O.algebra))
  J=ideal(O,m)
  J.gens=gens
  return J

end

@doc Markdown.doc"""
***
    pradical(O::AlgAssAbsOrd, p::Int)
            
> Given an order O and a prime p, it returns the radical of the ideal generated by p
"""

function pradical(O::AlgAssAbsOrd, p::Int)
  
  #See the paper from Ronyai, Structure of finite algebra
  l = clog(fmpz(O.dim),p)
  if l > 1
    return pradical_meataxe(O,p)
  end
  n = root(O.dim,2)
  F = GF(p, cached=false)

  #First step: kernel of the trace matrix mod p 
  W = MatrixSpace(F,O.dim, O.dim, false)

  I = W(n*trred_matrix(O))
  k, B = nullspace(I)
  # The columns of B give the coordinates of the elements in the order.
  if k==0
    J= ideal(O, MatrixSpace(FlintZZ, O.dim, O.dim, false)(p))
    J.gens = AlgAssAbsOrdElem[O(p*one(O.algebra))]
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
    M1 = hnf_modular_eldiv!(M, fmpz(p))
    res = ideal(O, view(M1,1:O.dim,1:O.dim))
    B1 = lift(B')
    res.gens = Vector{elem_type(O)}(undef, k+1)
    for i=1:k
      res.gens[i] = elem_from_mat_row(O, B1, i)
    end
    res.gens[k+1] = O(p*one(O.algebra))
    @hassert :AlgAssOrd 1 check_pradical(res,p)
    return res
  end
  
  Ide = transpose(lift(B))
  #Now, iterate: we need to find the kernel of tr((xy)^(p^i))/p^i mod p
  #on the subspace generated by I
  #Hard to believe, but this is linear on I!!!!
  for i = 1:l
    N = zero_matrix(F, O.dim, rows(Ide))
    a = O.algebra()
    for t = 1:rows(Ide)
      elm = elem_from_mat_row(O,Ide,t)
      for s = 1:O.dim
        mul!(a, elm.elem_in_algebra, O.basis_alg[s])
        bbb = (a^(p^i))
        trel = tr(bbb)
        el = divexact(numerator(trel),p^i)
        N[s,t] = F(el)
      end
    end
    k, B2 = nullspace(N)
    if k == 0
      J = ideal(O, MatrixSpace(FlintZZ, O.dim, O.dim, false)(p))
      J.gens = AlgAssAbsOrdElem[O(p*one(O.algebra))]
      return J
    end
    Ide = lift(transpose(B2))*Ide
  end
  gens = Vector{AlgAssAbsOrdElem}(undef, rows(Ide)+1)
  for i in 1:rows(Ide)
    gens[i] = elem_from_mat_row(O, Ide, i)
  end
  gens[rows(Ide)+1]= O(p*one(O.algebra))
  #Now, I have to give a basis for the ideal.
  m=zero_matrix(FlintZZ, O.dim, O.dim)
  for i=1:rows(Ide)
    for j=1:cols(Ide)
      m[i,j]=Ide[i,j]
    end
  end
  hnf_modular_eldiv!(m, fmpz(p))
  res = ideal(O, m)
  res.gens=gens
  @hassert :AlgAssOrd 1 check_pradical(res,p)
  return res
  
end

###############################################################################
#
#  Discriminant and Reduced Trace Matrix
#
###############################################################################

function trred_matrix(O::AlgAssAbsOrd)

  A=O.algebra
#  if isdefined(O, :trred_matrix)
#    return O.trred_matrix
#  end
  x=O.basis_alg
  m=length(x)
  M=zero_matrix(FlintZZ, m, m)
  a=A()
  for i=1:m
    a = mul!(a, x[i], x[i])
    M[i,i] = FlintZZ(trred(a))
  end
  for i = 1:m
    for j = i+1:m
      mul!(a, x[i], x[j])
      b = FlintZZ(trred(a))
      M[i,j] = b
      M[j,i] = b
    end
  end
  O.trred_matrix = M
  return M
end

function discriminant(O::AlgAssAbsOrd) 
  if isdefined(O, :disc)
    return O.disc
  end
  M = trred_matrix(O)
  O.disc = det(M)
  return O.disc
end


###############################################################################
#
#  Schur Index at Infinity
#
###############################################################################


#Steel Nebe paper
@doc Markdown.doc"""
***
    schur_index_at_real_plc(O::AlgAssAbsOrd)
        
> Given an order O, this function returns the schur index 
> of the algebra over the field of real numbers
"""
function schur_index_at_real_plc(O::AlgAssAbsOrd)
  
  x=trace_signature(O)
  n=root(O.dim,2)
  if x[1] == divexact(n*(n+1),2)
    return 1
  else
    return 2
  end
  
end


function trace_signature(O::AlgAssAbsOrd)
  
  @vtime :AlgAssOrd 1 M = trred_matrix(O)
  Zx, x = PolynomialRing(FlintZZ, "x")
  Qy, y = PolynomialRing(FlintQQ, "y")
  @vtime :AlgAssOrd 1 f = charpoly(Zx, M)
  @vtime :AlgAssOrd 1 fac = factor_squarefree(Qy(f))
  npos = 0
  for (t,e) in fac
    @vtime :AlgAssOrd a = number_positive_roots(Zx(t))
    npos += a*e 
  end
  return (npos, degree(f) - npos)
  
end


###############################################################################
#
#  Schur Index at p
#
###############################################################################

@doc Markdown.doc"""
***
    schur_index_at_p(O::AlgAssAbsOrd, p::fmpz)
        
> Given a maximal order O and a prime p, this function returns the schur index 
> of the completion of the algebra at p 
"""
function schur_index_at_p(O::AlgAssAbsOrd, p::fmpz)
  @assert O.ismaximal==1
  d = discriminant(O)
  v = valuation(d,p)
  if v == 0
    return 1
  end
  n = root(O.dim,2)
  t = n - divexact(v,n)
  return divexact(n,t)
end


###############################################################################
#
#  p-maximal overorder
#
###############################################################################

function _maximal_ideals(O::AlgAssAbsOrd, p::Int)
  
  A1 = quo(O, p)
  #@show dim(A1)
  @vtime :AlgAssOrd 1 lg = gens(A1)
  #@show length(lg)
  lM = gfp_mat[representation_matrix(lg[i]) for i=1:length(lg)]
  append!(lM, gfp_mat[representation_matrix(lg[i], :right) for i=1:length(lg)])  
  #lM = nmod_mat[representation_matrix(A1[i]) for i=1:dim(A1)]
  #append!(lM, nmod_mat[representation_matrix(A1[i], :right) for i=1:dim(A1)])
  M = ModAlgAss(lM)
  ls = maximal_submodules(M)
  #@show length(ls)
  poneO = O(p*one(O.algebra))
  return ( _from_submodules_to_ideals(M, O, x, fmpz(p), poneO) for x in ls )

end

function _maximal_ideals(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl, p::Int)
  
  A1, A1toO = quo(O, I, p)  
  #@show dim(A1)
  @vtime :AlgAssOrd 1 lg = gens(A1)
  #@show length(lg)
  lM = gfp_mat[representation_matrix(lg[i]) for i=1:length(lg)]
  append!(lM, gfp_mat[representation_matrix(lg[i], :right) for i=1:length(lg)])
  #lM = nmod_mat[representation_matrix(A1[i]) for i=1:dim(A1)]
  #append!(lM, nmod_mat[representation_matrix(A1[i], :right) for i=1:dim(A1)])
  M = ModAlgAss(lM)
  ls = maximal_submodules(M)
  #@show ls
  poneO = O(p*one(O.algebra))
  return ( _from_submodules_to_ideals(M, O, I, x, fmpz(p), poneO, A1, A1toO) for x in ls )

end

function _from_submodules_to_ideals(M::ModAlgAss, O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl, x::Zmodn_mat, p::fmpz, poneO::AlgAssAbsOrdElem, A1::AlgAss, A1toO::Function)
  @hassert :AlgAssOrd 1 begin r = rref(x)[1]; closure(x, M.action) == sub(rref(x)[2], 1:r, 1:cols(x)) end
  m = zero_matrix(FlintZZ, rows(x)+O.dim , O.dim)
  gens = Vector{AlgAssAbsOrdElem}(undef, rows(x))
  for i = 1:rows(x)
    el = A1toO(elem_from_mat_row(A1, x, i))
    for j = 1:O.dim
      m[i,j] = elem_in_basis(el, Val{false})[j]
    end
    gens[i] = elem_from_mat_row(O, m, i)
  end
  for i=rows(x)+1:rows(m)
    for j=1:O.dim
      m[i,j] = I.basis_mat[i-rows(x), j]
    end
  end
  hnf_modular_eldiv!(m, fmpz(p))
  J = ideal(O, view(m, 1:O.dim, 1:O.dim))
  if isdefined(I, :gens)
    append!(gens, I.gens)
    J.gens = gens
  else
    append!(gens, basis(I, Val{false}))
  end
  return J

end

function _from_submodules_to_ideals(M::ModAlgAss, O::AlgAssAbsOrd, x::Zmodn_mat, p::fmpz, poneO::AlgAssAbsOrdElem)

  @hassert :AlgAssOrd 1 begin r = rref(x)[1]; closure(x, M.action) == sub(rref(x)[2], 1:r, 1:cols(x)) end
  m = zero_matrix(FlintZZ, O.dim, O.dim)
  gens = Vector{AlgAssAbsOrdElem}(undef, rows(x)+1)
  for i = 1:rows(x)
    for j = 1:cols(x)
      m[i,j] = x[i,j].data
    end
    gens[i] = elem_from_mat_row(O, m, i)
  end
  hnf_modular_eldiv!(m, fmpz(p))
  gens[rows(x)+1] = poneO
  J = ideal(O, m)
  J.gens = gens
  return J

end


function pmaximal_overorder(O::AlgAssAbsOrd, p::Int)

  d=discriminant(O)
  if rem(d, p^2) != 0  
    return O
  end

  if p > O.dim
    @vtime :AlgAssOrd 1 O1 = pmaximal_overorder_tr(O,p)::AlgAssAbsOrd
    return O1
  else
    @vtime :AlgAssOrd 1 O1 = pmaximal_overorder_meataxe(O,p)::AlgAssAbsOrd
    return O1
  end
end

function pmaximal_overorder_meataxe(O::AlgAssAbsOrd, p::Int)

  extend = false
  d = discriminant(O)
  while true
    dd = fmpz(1)
    @vtime :AlgAssOrd 1 max_id =_maximal_ideals(O, p)
    for m in max_id
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
      if rem(d, p^2) != 0
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

function prime_ideals_over(O::AlgAssAbsOrd, p::fmpz)
  pp = Int(p)
  @vtime :AlgAssOrd 1 I = pradical(O, pp)
  @vtime :AlgAssOrd 1 max_id = collect(_maximal_ideals(O, pp))
  return max_id
end

function pmaximal_overorder_tr(O::AlgAssAbsOrd, p::Int)
  #First, the head order by computing the pradical and its ring of multipliers
  d = discriminant(O)
  @vtime :AlgAssOrd 1 I = pradical(O, p)
  @vtime :AlgAssOrd 1 OO = ring_of_multipliers(I, fmpz(p))
  dd = discriminant(OO)
  if rem(dd, p^2) != 0
    return OO
  end
  while dd!= d
    d = dd
    O = OO
    @vtime :AlgAssOrd 1 I = pradical(O,p)
    @vtime :AlgAssOrd 1 OO = ring_of_multipliers(I, fmpz(p))
    dd = discriminant(OO)
    if rem(dd, p^2) != 0
      return OO
    end
  end
  #Now, we have to check the maximal ideals.
  
  extend = false
  @vtime :AlgAssOrd 1 max_id = _maximal_ideals(O, I, p)
  for m in max_id
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
    if rem(dd, p^2) != 0
      return OO
    end
    extend = false
  else
    return OO
  end
  while true
    dd = fmpz(1)
    @vtime :AlgAssOrd 1 max_id = _maximal_ideals(O, p)
    for m in max_id
      OO = ring_of_multipliers(m, fmpz(p))
      dd = discriminant(OO)
      if d != dd
        extend = true
        O = OO
        d = dd
        break
      end
    end

    if extend
      if rem(dd, p^2) != 0
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

@doc Markdown.doc"""
***
    MaximalOrder(O::AlgAssAbsOrd)
        
> Given an order O, this function returns a maximal order containing O
"""

function MaximalOrder(O::AlgAssAbsOrd)
  @vtime :NfOrd fac = factor(abs(discriminant(O)))
  OO=O
  for (p,j) in fac
    OO += pmaximal_overorder(O, Int(p))
  end
  OO.ismaximal=1
  return OO
end

###############################################################################
#
#  IsSplit
#
###############################################################################

@doc Markdown.doc"""
***
    issplit(A::AlgAss)

> Given a Q-algebra A, this function returns true if A splits over Q, false otherwise
"""

function issplit(A::AlgAss)
  O = Order(A, basis(A))
  i = schur_index_at_real_plc(O)
  if i==2
    return false
  end  
  fac = factor(root(abs(discriminant(O)),2))
  for (p,j) in fac
    O1 = pmaximal_overorder(O, Int(p))
    if valuation(O1.disc, Int(p)) != 0
      return false
    end
  end
  return true
end
