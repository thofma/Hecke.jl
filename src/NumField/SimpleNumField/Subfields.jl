################################################################################
#
#  Enumeration of subfields
#
################################################################################

# This is a simple implementation of the algorithms described in
# "Generating subfields" by van Hoeij, Kluners and Novocin
# (see https://doi.org/10.1016/j.jsc.2012.05.010).

#################################################################################
#
#  Principal subfields
#
################################################################################

# Compute the bases of the principal subfields
function _principal_subfields_basis(K::SimpleNumField)
  f = K.pol
  Kx, x = polynomial_ring(K, "x", cached = false)
  n = degree(K)
  fK = change_base_ring(K, f, parent = Kx)
  fac = factor(fK)
  k = base_field(K)
  principal_subfields_ar = dense_matrix_type(elem_type(k))[]

  #compute kernel of (phi - id)
  for (fi, _) in fac
    M = zero_matrix(k, n, n * degree(fi))
    im_ar = elem_type(Kx)[(mod(x^l,fi)-gen(K)^l) for l in 0:n-1]
    for j in 1:n
      for l in 0:degree(fi)-1
        t = basis_matrix([coeff(im_ar[j], l)])
        for m in 1:n
          M[j, l * n + m] = t[1, m]
        end
      end
    end
    ker = kernel(M, side = :left)

    # This might be expensive for bigger fields?
    if K isa NumField{QQFieldElem}
      ker_rref = QQMatrix(lll(saturate(FakeFmpqMat(rref(ker)[2]).num)))
    else
      ker_rref = rref(ker)[2]
    end

    if ker_rref in [ b for b in principal_subfields_ar if nrows(b) == nrows(ker_rref)]
      continue
    else
      push!(principal_subfields_ar, ker_rref)
    end
  end
  return principal_subfields_ar
end

# Height is the maximum absolute numerator or denominator of the rational
# coordinates of the coefficients, in the fixed absolute basis of the common
# base field. Small rational coefficients can still have large denominators.
function _subfield_polynomial_height(f::PolyRingElem{<:NumFieldElem})
  h = one(ZZ)
  for c in coefficients(f), a in absolute_coordinates(c)
    h = max(h, abs(numerator(a)), denominator(a))
  end
  return h
end

# The coefficients of the minimal polynomial of gen(K) over L generate L/k.
# They often give smaller defining polynomials than an echelonized basis.
function _subfield_coefficient_generator_with_minpoly(K::SimpleNumField, M::MatElem)
  d = nrows(M)
  Kx, _ = polynomial_ring(K, "x", cached = false)
  g = _get_sfpoly(Kx, M)
  cf = [coeff(g, j) for j in degree(g)-1:-1:0]

  for c in cf
    f = minpoly(c)
    degree(f) == d && return c, f
  end

  # A proper intermediate field contains s(t) = sum_j cf[j]*t^(j-1) for fewer
  # than length(cf) values of t (Vandermonde), and there are finitely many.
  t = 1
  while true
    s = cf[end]
    for j in length(cf)-1:-1:1
      s = cf[j] + t*s
    end
    f = minpoly(s)
    degree(f) == d && return s, f
    t += 1
  end
end

# Return a primitive element of the subfield L with k-basis given by M.
function _subfield_small_primitive_element(K::SimpleNumField, M::MatElem)
  return first(_subfield_small_primitive_element_with_minpoly(K, M))
end

function _subfield_small_primitive_element_with_minpoly(K::SimpleNumField, M::MatElem)
  d = nrows(M)
  d == 1 && return one(K), parent(K.pol)([-1, 1])
  d == degree(K) && return gen(K), divexact(K.pol, leading_coefficient(K.pol))

  bas = [elem_from_mat_row(K, M, j) for j in 1:d]
  s, f = _subfield_primitive_element_from_basis_with_minpoly(K, bas)
  c, g = _subfield_coefficient_generator_with_minpoly(K, M)

  # Keep the basis generator on ties, preserving the previous presentation.
  if _subfield_polynomial_height(g) < _subfield_polynomial_height(f)
    return c, g
  end
  return s, f
end

@doc raw"""
    principal_subfields(L::SimpleNumField) -> Vector{Tuple{NumField, Map}}

Return the principal subfields of $L$ as pairs consisting of a subfield $k$
and an embedding $k \to L$.

# Examples

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = number_field(x^8 - x^4 + 1);

julia> length(principal_subfields(K))
8
```
"""
function principal_subfields(K::SimpleNumField)
  v = get_attribute(K, :principal_subfields)
  v === nothing || return v

  ba = _principal_subfields_basis(K)
  T = typeof(K)
  res = Tuple{T, morphism_type(T)}[]
  for M in ba
    if K isa NumField{QQFieldElem}
      baf = FakeFmpqMat(M)
      elts = [elem_from_mat_row(K, baf.num, j, baf.den) for j=1:nrows(baf)]
      push!(res, subfield(K, elts, isbasis = true))
    else
      s, f = _subfield_small_primitive_element_with_minpoly(K, M)
      push!(res, _subfield_from_primitive_element(K, s, f))
    end
  end
  set_attribute!(K, :principal_subfields => res)
  return res
end

# Computes the minpoly of a over M if k(a)=K/M/k
# TODO: Improve this.
function _get_sfpoly(Kx, M)
  K = base_ring(Kx)
  k = base_field(K)
  n = degree(K)
  @assert k === base_ring(M)
  M = transpose(M)
  rk = rank(M)
  if rk == 1
      return Kx([K(coeff(minpoly(gen(K)),i)) for i in 0:degree(minpoly(gen(K)))])
  end
  my = div(n, rk)
  ar_basis = Vector{elem_type(K)}(undef, rk)
  for i in 1:rk
    elem_basis = zero(K)
    for j in 1:n
      elem_basis += M[j,i] * gen(K)^(j-1)
    end
    ar_basis[i] = elem_basis
  end
  null_mat = zero_matrix(k, n, 0)
  for i in 1:length(ar_basis)
    null_mat = hcat(null_mat,transpose(representation_matrix(ar_basis[i]))[:,1:my])
  end
  temp = zero_matrix(k,n,1)
  temp[my+1,1] = one(k)
  null_mat = hcat(null_mat,temp)
  mat_poly = kernel(null_mat, side = :right)
  @assert ncols(mat_poly) == 1
  mat_poly = inv(mat_poly[n + 1, 1])*mat_poly # produce a 1 in the lowest entry
  ar_coeff = Vector{elem_type(K)}(undef,my)
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
  return Kx(ar_coeff)
end

# TODO:
# The algorithm works with subfields represented as vector spaces and it needs
# to compute intersections and test containment
# - Improve this by exploiting that everything should be in rref (use reduce_mod)
# - Maybe also cache the pivots
# - Maybe use blocks instead to identify the fields?

# Computes the intersection of subfields A,B of K/k, represented as k-VS
# TODO (easy): Get rid of the transpose :)
function _intersect_spaces(A::Hecke.AbstractAlgebra.Generic.MatElem, B::Hecke.AbstractAlgebra.Generic.MatElem)
  A = transpose(A)
  B = transpose(B)
  M = kernel(hcat(A,-B), side = :right)[1:size(A)[2],:]
  intersect_mat = zero_matrix(base_ring(A), nrows(A), ncols(M))
  for i in 1:ncols(intersect_mat)
    intersect_mat[:,i] = A * M[:,i]
  end
  return transpose(intersect_mat)
end

# Computes the intersection of subfields A = [a1,...,an] of K/k, represented as k-VS
function _intersect_spaces(A::Vector{T}) where T
  if length(A) < 1
    error("Number of spaces must be non-zero")
  elseif length(A) == 1
    return A[1]
  elseif length(A) == 2
    return _intersect_spaces(A[1],A[2])
  else
    intersection_temp = _intersect_spaces(A[1],A[2])
    for i in 3:length(A)
      intersection_temp = _intersect_spaces(intersection_temp,A[i])
    end
    return intersection_temp
  end
end

# Returns true if A is subspace of B,otherwise false, for A,B k-VS
# TODO (easy): Make this great again :)
function _issubspace(A::MatElem, B::MatElem, proper_subspace::Bool = false)     #or cmpr remark7
  intersectAB = _intersect_spaces(A, B)
  Bol = rank(intersectAB) == rank(A)
  if proper_subspace
    return Bol && (rank(intersectAB) < rank(B))
  else
    return Bol
  end
end

function _generating_subfields(S, len::Int = -1)
  # I don't know (yet) why it is necessary, but we have to do it
  if length(S) == 1
    return S
  end
  ar_2delete = Bool[false for i in 1:length(S)]
  for i in 1:length(S)
    if nrows(S[i]) >= len
      ar_intersection = typeof(S)()
      for j in 1:length(S)
        if _issubspace(S[i],S[j],true)
          push!(ar_intersection, S[j])
        end
      end
      #K always principal_subfield
      if length(ar_intersection) == 0
        ar_2delete[i] = true
      else
        intersection = _intersect_spaces(ar_intersection)
        if _issubspace(intersection, S[i]) && _issubspace(S[i], intersection)
          ar_2delete[i] == true
        end
      end
    else
      ar_2delete[i] = true
    end
  end
  _generating_subfields_ar = S
  indx = length(ar_2delete)
  while indx > 0
    if ar_2delete[indx]
      deleteat!(_generating_subfields_ar, indx)
    end
    indx -= 1
  end
  return _generating_subfields_ar
end

function _all_subfields(K, S::Vector{T}, len::Int = -1) where {T}
    Kx, _  = polynomial_ring(K, "x", cached = false)
    if length(S) == 0
        return S
    end
    #compute associated tuple of K
    e = Int[0 for i in 1:length(S)]
    K_mat = identity_matrix(base_field(K), degree(K))
    sf_ar = elem_type(Kx)[_get_sfpoly(Kx, M) for M in S]
    ListSubfields = T[K_mat]
    _next_subfields(ListSubfields, Kx, S ,K_mat,e,0,sf_ar, len)
    return ListSubfields
end

#Hilfsfunktion for _all_subfields
function _next_subfields(ListSubfields, Kx, S::Vector{T}, L::T, e::Vector{Int}, s::Int, sf_ar, len::Int) where {T}
  i = s + 1
  while i <= length(S)
    if e[i] == 0
      M = _intersect_spaces(L,S[i])
      #check len
      if rank(M) >= len
        #constr associated tuple of M
        ee = Int[0 for j in 1:length(S)]
        for j in 1:length(S)
          #    if _issubspace(M,S[j])
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
          _next_subfields(ListSubfields, Kx, S,M,ee,hi,sf_ar, len)
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

################################################################################
#
#  Subfield function
#
################################################################################

@doc raw"""
    subfields(L::SimpleNumField) -> Vector{Tuple{NumField, Map}}

Given a simple extension $L/K$, returns all subfields of $L$ containing
$K$ as tuples $(k, \iota)$ consisting of a simple extension $k$
and an embedding $\iota k \to K$.
"""
function subfields(K::SimpleNumField; degree::Int = -1)
  s = get_attribute(K, :all_subfields)
  T = typeof(K)
  if s !== nothing
    if degree == -1
      return s
    end
    return Tuple{T, morphism_type(T)}[x for x = s if Hecke.degree(x[1]) == degree]
 end

  n = Hecke.degree(K) # I want to keep the degree keyword
  k = base_field(K)
  #K = k[x]/f
  # K no generating subfield

  # TODO (medium)
  # I don't know why we have to do this.
  # This needs to be fixed properly
  if n == 1 || degree == n
    return Tuple{T, morphism_type(T)}[(K, id_hom(K))]
  end

  if is_prime(n)
    res = Tuple{T, morphism_type(T)}[]
    if degree == n
      push!(res, (K, id_hom(K)))
    elseif degree == 1
      kt, t = polynomial_ring(k, "t", cached = false)
      k_as_field = number_field(t-1, check = false, cached = false)[1]
      push!(res, (k_as_field, hom(k_as_field, K, one(K))))
    elseif degree == -1
      kt, t = polynomial_ring(k, "t", cached = false)
      k_as_field = number_field(t-1, check = false, cached = false)[1]
      push!(res, (K, id_hom(K)))
      push!(res, (k_as_field, hom(k_as_field, K, one(K))))
      set_attribute!(K, :all_subfields => res)
    end
    return res
  end
  princ_subfields = _principal_subfields_basis(K)
  gg = _generating_subfields(princ_subfields)
  sf_asmat_ar = _all_subfields(K, gg, degree)
  #compute embedding
  ResidueRingElem = Vector{Tuple{typeof(K), morphism_type(K)}}()
  #get minimal polynomial of primitive elem k(pe) = M, over k
  for sf_mat in sf_asmat_ar
    #interpret column vectors as field elems
    #sf_mat = transpose(sf_mat)
    #sf_mat_f = FakeFmpqMat(sf_mat)#
    sf_mat_f = sf_mat
    basis_ar = Vector{elem_type(K)}(undef, nrows(sf_mat_f))
    for i in 1:nrows(sf_mat_f)
      if K isa NumField{QQFieldElem}
        _t = FakeFmpqMat(sf_mat_f)
        basis_ar[i] = elem_from_mat_row(K, _t.num, i, _t.den)
      else
        basis_ar[i] = elem_from_mat_row(K, sf_mat_f, i)
      end

    end
    push!(ResidueRingElem, subfield(K, basis_ar, isbasis = true))
  end
  degree == -1 && set_attribute!(K, :all_subfields => ResidueRingElem)
  return ResidueRingElem
end

# TODO: Write a dedicated function for the normal case and use the subgroup functions
function subfields_normal(K::SimpleNumField, classes::Bool = false)
  G, mG = automorphism_group(K)
  subs = subgroups(G, conjugacy_classes = classes)
  res = Vector{Tuple{typeof(K), morphism_type(typeof(K))}}()
  for (i, (H, mH)) in enumerate(subs)
    auts = morphism_type(typeof(K))[ mG(mH(h)) for h in H ]
    push!(res, fixed_field(K, auts))
  end
  return res
end
