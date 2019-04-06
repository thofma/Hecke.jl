export fixed_field, subfields

function _subfield_basis(K, elt)
  n = degree(K)
  bas = elem_type(K)[one(K)]
  phase = 1
  local B::FakeFmpqMat

  for e = elt
    if phase == 2
      C = basis_mat([e])
      fl, _ = can_solve(matrix(FlintQQ, B.num), matrix(FlintQQ, C.num), side = :left)
      fl && continue
    end
    df = n-1
    f = one(K)
    for i=1:df
      mul!(f, f, e)
      if phase == 2
        C = matrix(FlintQQ, basis_mat(elem_type(K)[f]).num)
        reduce_mod!(C, matrix(FlintQQ, B.num))
        fl = iszero(C) 
        fl && break
      end
      b = elem_type(K)[e*x for x in bas]
      append!(bas, b)
      if length(bas) >= n
        B = basis_mat(bas)
        hnf!(B)
        rk = nrows(B) - n + 1
        while iszero_row(B, rk)
          rk += 1
        end
        B = sub(B, rk:nrows(B), 1:n)
        phase = 2
        bas = elem_type(K)[ elem_from_mat_row(K, B.num, i, B.den) for i = 1:nrows(B) ]
      end
    end
  end

  if length(bas) >= n
    B = basis_mat(bas)
    hnf!(B)
    rk = nrows(B) - n + 1
    # This is wrong. But I need to see an actual error
    if iszero_row(B.num, rk)
      error("data does not define an order: dimension to small")
    end
    B = sub(B, rk:nrows(B), 1:n)
    bas = elem_type(K)[ elem_from_mat_row(K, B.num, i, B.den) for i = 1:nrows(B) ]
  end

  return bas
end

function _improve_subfield_basis(K, bas)
  # First compute the maximal order of <bas> by intersecting and saturating
  # Then B_Ok = N * B_LLL_OK
  # Then B' defined as lllN * B_LLL_OK will hopefully be small
  OK = maximal_order(K)
  OKbmatinv = basis_mat_inv(OK, copy = false)
  basinOK = bas * matrix(FlintQQ, OKbmatinv.num) * fmpq(1, OKbmatinv.den)
  deno = fmpz(1)
  for i in 1:nrows(basinOK)
    for j in 1:ncols(basinOK)
      deno = lcm(deno, denominator(basinOK[i, j]))
    end
  end
  S = saturate(matrix(FlintZZ, basinOK * deno))
  SS = S * basis_mat(OK, copy = false)
  lllOK = lll(OK)
  N = (SS * basis_mat_inv(lllOK)).num
  lllN = lll(N)
  maybesmaller = lllN * basis_mat(lllOK)
  return maybesmaller
end

function _subfield_primitive_element_from_basis(K, elt)
  if length(elt) == 0
    return gen(K)
  end

  s = zero(K)

  # First check basis elements
  for i in 1:length(elt)
    if degree(minpoly(elt[i])) == length(elt)
      return elt[i]
    end
  end

  while true
    rand!(s, elt, 0:1)
    if (degree(minpoly(s)) == length(elt))
      return s
    end
  end
end

#returns minimal subfield of K containing A
function subfield(K::S, elt::Array{T, 1}; isbasis::Bool = false) where {S <: Union{AnticNumberField, Hecke.NfRel}, T <: Union{nf_elem, Hecke.NfRelElem}}
  if length(elt) == 1
    return _subfield_from_primitive_element(K, elt[1])
  end

  if isbasis
    s = _subfield_primitive_element_from_basis(K, elt)
  else
    bas = _subfield_basis(K, elt)
    s = _subfield_primitive_element_from_basis(K, bas)
  end

  return _subfield_from_primitive_element(K, s)
end
# There is a deterministic version due to Lenstra--Silverberg
#    if alg=="L"
#        G_ar = [minpoly(B[i]) for i in 1:length(B)];
#        K_ar = Array{fmpz,1}(undef,length(B));
#        D_ar = Array{fmpz,1}(undef,length(B)+1);
#        D_ar[1] = 1;
#        for i in 1:length(B)
#            k = ZZ(1);
#            for j in 1:degree(G_ar[i])
#                k *= denominator(coeff(G_ar[1],j));
#            end
#            K_ar[i]=k;
#            fi = G_ar[i]*x*K_ar[i]^(degree(G_ar[i])-1);
#            dfi = ZZ(discriminant(fi));
#            d=2
#            while gcd(dfi,d^2)!=1
#                d=d+1;
#            end
#            D_ar[i+1]=d;
#        end
#        D_ar = D_ar[1:length(B)];
#        Al = [B[i]*K_ar[i] for i in 1:length(B)];
#        D_ar = accumulate(*,D_ar);
#        return subfield(K,Al'*D_ar)
#    end

function _subfield_from_primitive_element(K, s)
  f = minpoly(s)
  L,_ = NumberField(f)
  return L, hom(L, K, s)
end

################################################################################
#
#  Fixed field
#
################################################################################

function fixed_field(K::S, auto::T; simplify::Bool = true) where {S <: Union{AnticNumberField, NfRel}, T <: Union{NfToNfMor, NfRelToNfRelMor}}
  return fixed_field(K, T[auto], simplify = simplify)
end

function fixed_field(K::S, autos::Array{T, 1}; simplify::Bool = true) where {S <: Union{AnticNumberField, NfRel}, T <: Union{NfToNfMor, NfRelToNfRelMor}}

  if length(autos) == 0
    return K, id_hom(K)
  end

  F = base_field(K)
  a = gen(K)
  n = degree(K)
  ar_mat = Vector{dense_matrix_type(elem_type(F))}()
  v = Vector{elem_type(K)}(undef, n)
  for i in 1:length(autos)
    o = one(K)
    as = autos[i](a)
    if a == as
      continue
    end
    v[1] = o
    for j in 2:n
      o = o * as
      v[j] = o
    end

    bm = basis_mat(v)
    
    if S === AnticNumberField
      m = matrix(FlintQQ, bm.num)
      for j in 1:n
        m[j, j] = m[j, j] - bm.den # This is - identity
      end
    else
      m = bm - identity_matrix(F, degree(K))
    end

    push!(ar_mat, m)
  end

  if length(ar_mat) == 0
    return K, id_hom(K)
  else
    bigmatrix = hcat(ar_mat)
    k, Ker = kernel(bigmatrix, side = :left)
    bas = Vector{elem_type(K)}(undef, k)
    if S === AnticNumberField
      # Try to find a small basis for absolute simple number fields
      if simplify
        KasFMat = _improve_subfield_basis(K, Ker)
        for i in 1:k
          bas[i] = elem_from_mat_row(K, KasFMat.num, i, KasFMat.den)
        end
      else
        KasFMat = FakeFmpqMat(Ker)
        Ksat = saturate(KasFMat.num)
        Ksat = lll(Ksat)
        onee = one(fmpz)
        for i in 1:k
          bas[i] = elem_from_mat_row(K, Ksat, i, onee)
        end
      end
    else
      for i in 1:k
        bas[i] = elem_from_mat_row(K, Ker, i)
      end
    end

    return subfield(K, bas, isbasis = true)
  end
end

################################################################################
#
#  Principal subfields
#
################################################################################

function _principal_subfields_basis(K::AnticNumberField)
  f = K.pol
  Kx, x = PolynomialRing(K, "x", cached = false)
  n = degree(K)
  #f in Kx
  #fk = Kx([coeff(f,i) for i in 0:n])
  #determine roots
  rts = roots(f, K)
  ar_lin_fac = elem_type(Kx)[x - root for root in rts]
  fK = change_ring(f, Kx)
  ##divide by roots
  for lin_fac in ar_lin_fac
    fK = div(fK, lin_fac)#divaxa
  end

  fac = factor(fK)

  for (g, e) in fac
    push!(ar_lin_fac, g)
  end

  factor_ar = ar_lin_fac
  k = base_field(K)
  principal_subfields_ar = dense_matrix_type(elem_type(k))[]

  # #compute kernel of (phi - id)
  for fi in factor_ar
    M = zero_matrix(k, n, n * degree(fi))
    im_ar = elem_type(Kx)[(mod(x^l,fi)-gen(K)^l) for l in 0:n-1]
    for j in 1:n
      for l in 0:degree(fi)-1
        t = basis_mat([coeff(im_ar[j], l)])
        for m in 1:n
          M[j, l * n + m] = (t.num[1, m])//t.den
        end
      end
    end
    nu, ker = kernel(M, side = :left)

    # This might be expensive for bigger fields?
    ker_rref = matrix(FlintQQ, lll(saturate(FakeFmpqMat(rref(ker)[2]).num)))

    # TODO: Remove this madness once we switched to Nemo >=0.13.2
    if ker_rref in [ b for b in principal_subfields_ar if nrows(b) == nrows(ker_rref)]
      continue
    else
      push!(principal_subfields_ar, ker_rref)
    end
  end
  return principal_subfields_ar
end

function principal_subfields(K::T) where {T}
  ba = _principal_subfields_basis(K)
  elts = Vector{Vector{nf_elem}}(undef, length(ba))
  for i in 1:length(ba)
    baf = FakeFmpqMat(ba[i])
    elts[i] = elem_type(K)[elem_from_mat_row(K, baf.num, j, baf.den) for j in 1:nrows(ba[i])]
  end
  return Tuple{T, morphism_type(T)}[ subfield(K, elts[i], isbasis = true) for i in 1:length(elts)]
end

# Computes the minpoly of a over M if k(a)=K/M/k
# TODO: Improve this. Don't call rank so often
function _get_sfpoly(Kx, M)
  K = base_ring(Kx)
  k = base_field(K)
  n = degree(K)
  @assert k === base_ring(M)
  M = transpose(M)
  if rank(M) == 1
      return Kx([K(coeff(minpoly(gen(K)),i)) for i in 0:degree(minpoly(gen(K)))])
  end
  my = div(n, rank(M))
  ar_basis = Vector{elem_type(K)}(undef, rank(M))
  for i in 1:rank(M)
    elem_basis = zero(K)
    for j in 1:n
      elem_basis += M[j,i] * gen(K)^(j-1)
    end
    ar_basis[i] = elem_basis
  end
  null_mat = zero_matrix(k, n, 0)
  for i in 1:length(ar_basis)
    null_mat = hcat(null_mat,representation_matrix(ar_basis[i])'[:,1:my])
  end
  temp = zero_matrix(k,n,1)
  temp[my+1,1] = one(k)
  null_mat = hcat(null_mat,temp)
  mat_poly = nullspace(null_mat)[2]
  ar_coeff = Array{elem_type(K),1}(undef,my)
  for i = 1:my
    indx = 1
    temp_coeff = K(0)
    for j = i:my:n
      temp_coeff += mat_poly[j,1] * ar_basis[indx]
      indx += 1
    end
    ar_coeff[i] = temp_coeff
  end
  #w.l. we cannot assume basis ordered in any way
  push!(ar_coeff,K(mat_poly[n+1,1]))
  if !isone(mat_poly[n+1,1])
      error("LC of minpoly not 1")
  end
  return Kx(ar_coeff)
end

# TODO:
# The algorithm works with subfields represented as vector spaces and it needs
# to compute intersections and test containment
# - Improve this by exploiting that everything should be in rref (use reduce_mod)
# - Maybe also cache the pivots

# Computes the intersection of subfields A,B of K/k, represented as k-VS
function intersect_spaces(A::Hecke.AbstractAlgebra.Generic.MatElem, B::Hecke.AbstractAlgebra.Generic.MatElem)
  A = transpose(A)
  B = transpose(B)
  M = nullspace(hcat(A,-B))[2][1:size(A)[2],:]
  intersect_mat = MatrixSpace(base_ring(A),size(A)[1],size(M)[2])()
  for i in 1:size(intersect_mat)[2]
      intersect_mat[:,i] = A * M[:,i]
  end
  return transpose(intersect_mat)
end

# Computes the intersection of subfields A = [a1,...,an] of K/k, represented as k-VS
function intersect_spaces(A::Vector{T}) where T
    if length(A) < 1
        @error("empty array")
    elseif length(A) == 1
        return A[1]
    elseif length(A) == 2
        return intersect_spaces(A[1],A[2])
    else
        intersection_temp = intersect_spaces(A[1],A[2])
        for i in 3:length(A)
            intersection_temp = intersect_spaces(intersection_temp,A[i])
        end
        return intersection_temp
    end
end

# Returns true if A is subspace of B,otherwise false, for A,B k-VS
function issubspace(A::Hecke.AbstractAlgebra.Generic.MatElem, B::Hecke.AbstractAlgebra.Generic.MatElem,proper_subspace::Bool = false)     #or cmpr remark7
  intersectAB = intersect_spaces(A, B)
  Bol = rank(intersectAB) == rank(A)
  if proper_subspace
    return Bol && (rank(intersectAB) < rank(B))
  else
    return Bol
  end
end

function generating_subfields(S, len::Int64 = -1)
  ar_2delete = Bool[false for i in 1:length(S)]
  for i in 1:length(S)
    if nrows(S[i]) >= len
      ar_intersection = typeof(S)()
      for j in 1:length(S)
        if issubspace(S[i],S[j],true)
          push!(ar_intersection, S[j])
        end
      end
      #K always principal_subfield
      if length(ar_intersection) == 0
        ar_2delete[i] = true
      else
        intersection = intersect_spaces(ar_intersection)
        if issubspace(intersection, S[i]) && issubspace(S[i], intersection)
          ar_2delete[i] == true
        end
      end
    else
      ar_2delete[i] = true
    end
  end
  generating_subfields_ar = S
  indx = length(ar_2delete)
  while indx > 0
    if ar_2delete[indx]
      deleteat!(generating_subfields_ar, indx)
    end
    indx -= 1
  end
  return generating_subfields_ar
end

function allSubfields(K, S::Vector{T}, len::Int64 = -1) where {T}
    Kx, _  = PolynomialRing(K, "x", cached = false)
    if length(S) == 0
        return S
    end
    #compute associated tuple of K
    e = Int[0 for i in 1:length(S)]
    K_mat = identity_matrix(base_field(K), degree(K))
    sf_ar = elem_type(Kx)[_get_sfpoly(Kx, M) for M in S]
    ListSubfields = T[K_mat]
    nextSubfields(ListSubfields, Kx, S ,K_mat,e,0,sf_ar, len)
    return ListSubfields
end

#Hilfsfunktion for allSubfields
function nextSubfields(ListSubfields, Kx, S::Vector{T}, L::T, e::Array{Int64,1}, s::Int64, sf_ar, len::Int64) where {T}
  i = s + 1
  while i <= length(S)
    if e[i] == 0
      M = intersect_spaces(L,S[i])
      #check len
      if rank(M) >= len
        #constr associated tuple of M
        ee = Int[0 for j in 1:length(S)]
        for j in 1:length(S)
          #    if issubspace(M,S[j])
          if iszero(mod(_get_sfpoly(Kx, M),sf_ar[j]))
            ee[j] = 1
          end
        end
        #check whether to append M
        # This should be checked when creating the e'
        appnd = true
        for j in 1:i-1
          if ee[j] > e[j]
            appnd = false
            break
          end
        end
        if appnd
          push!(ListSubfields,M)
          hi = i
          nextSubfields(ListSubfields, Kx, S,M,ee,hi,sf_ar, len)
        end
      end
    end
    i += 1
  end
  #check length
  if len != -1
    indx = length(ListSubfields)
    while indx > 0
      if rank(ListSubfields[indx]) != len
        deleteat!(ListSubfields,indx)
      end
      indx -= 1
    end
  end
end

function subfields(K::T; degree::Int64 = -1) where {T <: Union{AnticNumberField, Hecke.NfRel}}
  n = Hecke.degree(K) # I want to keep the degree keyword
  k = base_field(K)
  #K = k[x]/f
  # K no generating subfield
  if degree == n
    return Tuple{T, morphism_type(T)}[(K, id_hom(K))]
  else
    princ_subfields = _principal_subfields_basis(K)
    gg = generating_subfields(princ_subfields)
    sf_asmat_ar = allSubfields(K, gg, degree)
  end
  #compute embedding
  Res = Vector{Tuple{typeof(K), morphism_type(typeof(K))}}()
  #get minimal polynomial of primitive elem k(pe) = M, over k
  for sf_mat in sf_asmat_ar
    #interpret column vectors as field elems
    #sf_mat = transpose(sf_mat)
    sf_mat_f = FakeFmpqMat(sf_mat)
    basis_ar = Array{elem_type(K),1}(undef, nrows(sf_mat_f))
    for i in 1:nrows(sf_mat_f)
      basis_ar[i] = elem_from_mat_row(K, sf_mat_f.num, i, sf_mat_f.den)
      #field_elem = K(0)
      #for j in 1:n
      #  field_elem += sf_mat[j,i] * gen(K)^(j-1)
      #end
      #basis_ar[i] = field_elem
    end
    push!(Res,subfield(K, basis_ar, isbasis = true))
  end
  return Res
end

# TODO: Write a dedicated function for the normal case and use the subgroup functions
