function closure_with_pol(v::MatElem{T}, M::MatElem{T}) where T <: FieldElem
  i = 1
  E = rref(v)[2]
  w = v*M
  res = Hecke.cleanvect(E, w)
  v = deepcopy(v) # the output should not "share" entries with the input
  while !iszero(res)
    v = vcat(v, w)
    E = vcat(E, res)
    rref!(E)
    i += 1
    w = w*M
    res = Hecke.cleanvect(E, w)
  end
  fl, c = can_solve_with_solution(v, w, side = :left)
  @assert fl
  return v, c
end

function decompose_primary(M::MatElem{T}) where T <: FieldElem
  dimsum = 0
  i = 1
  K = base_ring(M)
  Kt, t = polynomial_ring(K, "t", cached = false)
  L = Dict{typeof(t), Vector{Tuple{typeof(M), typeof(M)}}}()
  S = zero_matrix(K, 0, ncols(M))
  while isempty(L) || sum(nrows(y[1]) for x in values(L) for y in x) < ncols(M)
    ei = zero_matrix(K, 1, ncols(M))
    ei[1, i] = 1
    res = Hecke.cleanvect(S, ei)
    while iszero(res)
      ei[1, i] = 0
      i += 1
      ei[1, i] = 1
      res = Hecke.cleanvect(S, ei)
    end
    C, coeffs = closure_with_pol(ei, M)
    S = vcat(S, C)
    rref!(S)
    cccc = [-coeffs[1, l] for l = 1:ncols(coeffs)]
    push!(cccc, K(1))
    m = Kt(cccc)
    p = one(Kt)
    for (g, s) in L
      f, fu = ppio(m, g)
      if isone(f)
        continue
      end
      w = ei * Hecke._subst(fu, M)
      p = p*f
      W = closure_with_pol(w, M)[1]
      W1 = W
      for (sub, gensub) in s
        W1 = vcat(W1, sub)
      end
      rk = rank(W1)
      if rk == nrows(W1) - nrows(W)
        continue
      end
      if rk == nrows(W1)
        #The space is independent from the one I had before
        push!(s, (W, w))
      else
        independent_from = Int[]
        intersect_not_contained = Int[]
        is_contained = []
        for j = 1:length(s)
          Ws = vcat(W, s[j][1])
          rk = rank(Ws)
          if rk == nrows(Ws)
            push!(independent_from, j)
          elseif rk == nrows(W)
            push!(is_contained, j)
          else
            push!(intersect_not_contained, j)
          end
        end
        if isempty(intersect_not_contained)
          #W contains some subspaces but it is independent from the others
          snew = Vector{Tuple{typeof(M), typeof(M)}}(undef, length(s) - length(is_contained) +1)
          indn = 1
          for z = 1:length(s)
            if !(z in is_contained)
              snew[indn] = s[z]
              indn += 1
            end
          end
          snew[end] = (W, w)
          L[g] = snew
        else
          snew = Vector{Tuple{typeof(M), typeof(M)}}(undef, length(s) - length(is_contained) -length(intersect_not_contained) +1)
          indn = 1
          newsub = W
          for z = 1:length(s)
            if !(z in is_contained) && !(z in intersect_not_contained)
              snew[indn] = s[z]
              indn += 1
            elseif (z in intersect_not_contained)
              newsub = vcat(s[z][1], newsub)
            end
          end
          rk = rref!(newsub)
          newsub1 = zero_matrix(K, rk, ncols(M))
          for r = 1:rk
            for cc = r:ncols(M)
              newsub1[r, cc] = newsub[r, cc]
            end
          end
          snew[end] = (newsub1, zero_matrix(K, 1, ncols(M)))
          L[g] = snew
        end
      end
    end
    ei = ei*Hecke._subst(p, M)
    m = divexact(m, p)
    if !isone(m)
      fac = factor(m)
      for (q, e) in fac
        qq = divexact(m, q^e)
        w = ei*Hecke._subst(qq, M)
        W = closure_with_pol(w, M)[1]
        L[q] = [(W, w)]
      end
    end
  end
  return L
end


@doc raw"""
    companion_matrix(p::PolyRingElem) -> MatElem

Returns the companion matrix of $p = \sum_{i=0}^n a_ix^i$, i.e. the matrix


    0 1  0  $\dots$  0
    0  0  1  $\dots$  0
    $\vdots$  $\vdots$  $\ddots$  $\vdots$  $\vdots$
    0  0  $\vdots$  0  1
    $-a_0$  $-a_1$  $-a_2$  $\dots$  $-a_{n-1}$

"""
function companion_matrix(p::PolyRingElem)
  K = base_ring(p)
  p1 = divexact(p, leading_coefficient(p))
  M = zero_matrix(K, degree(p), degree(p))
  for i = 1:degree(p)-1
    setindex!(M, one(K), i, i+1)
  end
  for i = 1:degree(p)
    setindex!(M, -coeff(p1, i-1), degree(p), i)
  end
  return M
end

function jordan_block(p::PolyRingElem, e::Int)
  K = base_ring(p)
  M = zero_matrix(K, degree(p)*e, degree(p)*e)
  C = companion_matrix(p)
  for i = 1:e
    _copy_matrix_into_matrix(M, 1+degree(p)*(i-1), 1+degree(p)*(i-1), C)
  end
  for i = 1:e-1
    M[i*degree(p), i*degree(p)+1] = K(1)
  end
  return M
end

@doc raw"""
    is_similar(M::MatElem{T}, N::MatElem{T}) where T <: FieldElem -> Bool

Returns true if the matrices are similar (conjugated) and false otherwise.
"""
function is_similar(M::MatElem{T}, N::MatElem{T}) where T <: FieldElem
  CM = rational_canonical_form(M)[1]
  CN = rational_canonical_form(N)[1]
  return CM == CN
end

@doc raw"""
    conjugating_matrix(M::MatElem{T}, N::MatElem{T}) where T <: FieldElem -> MatElem{T}

Returns a matrix $S$ such that $S\times N \times S^{-1} = M$.
"""
function conjugating_matrix(M::MatElem{T}, N::MatElem{T}) where T <: FieldElem
  CM, SM = rational_canonical_form(M)
  CN, SN = rational_canonical_form(N)
  if CM != CN
    error("Matrices are not similar!")
  end
  return inv(SM)*SN
end

################################################################################
#
#  Rational canonical form - Geck's algorithm
#
################################################################################

function maximal_vector(M::MatElem{T}, Kt, max_deg::Int = -1) where T <: FieldElem
  K = base_ring(M)
  v = zero_matrix(K, 1, ncols(M))
  bound = ncols(M)
  if max_deg != -1
    bound = min(max_deg, bound)
  end
  v[1, 1] = 1
  to_reduce, coeffs_vect = closure_with_pol(v, M)
  coeffs = T[-coeffs_vect[1, i] for i = 1:length(coeffs_vect)]
  push!(coeffs, K(1))
  mp = Kt(coeffs)
  if nrows(to_reduce) == bound
    return v, mp
  end
  rref!(to_reduce)
  for i = 2:nrows(M)
    v1 = zero_matrix(K, 1, ncols(M))
    v1[1, i] = 1
    res = Hecke.cleanvect(to_reduce, v1)
    if iszero(res)
      continue
    end
    C1, coeffs_vect2 = closure_with_pol(v1, M)
    coeffs2 = T[-coeffs_vect2[1, i] for i = 1:length(coeffs_vect2)]
    to_reduce = vcat(to_reduce, C1)
    rref!(to_reduce)
    push!(coeffs2, K(1))
    mp2 = Kt(coeffs2)
    if divides(mp, mp2)[1]
      continue
    end
    if nrows(C1) == bound
      return v1, mp2
    end
    f1, f2 = coprime_fact(mp, mp2)
    if f1 == mp && f2 == mp2
      v = v + v1
    else
      v = v*Hecke._subst(divexact(mp, f1), M) + v1*Hecke._subst(divexact(mp2, f2), M)
    end
    C, coeffs_vect = closure_with_pol(v, M)
    coeffs = T[-coeffs_vect[1, i] for i = 1:length(coeffs_vect)]
    push!(coeffs, K(1))
    mp = Kt(coeffs)
    if nrows(C) == bound
      return v, mp
    end
  end
  return v, mp
end

#Finds a1, b1 such that a1*b1 = a*b/gcd(a, b) and a1, b1 are coprime
function coprime_fact(a::PolyRingElem{T}, b::PolyRingElem{T}) where T <: FieldElem
  d = gcd(a, b)
  if isone(d)
    return a, b
  end
  atilde = divexact(a, d)
  btilde = divexact(b, d)
  b1 = gcd(btilde^(degree(b)), b)
  bprime = divexact(b, b1)
  a1 = bprime*atilde
  return a1, b1
end

function find_pivots(M::MatElem{T}) where T <: FieldElem
  pivots = Vector{Int}(undef, nrows(M))
  j = 1
  for i = 1:nrows(M)
    while iszero(M[i, j])
      j += 1
    end
    pivots[i] = j
  end
  return pivots
end

@doc raw"""
    complete_to_basis(C::MatElem{T}) where T <: FieldElem -> MatElem{T}

Returns a matrix representing a basis of $K^n$ whose first elements are given by the rows of $C$.
"""
function complete_to_basis(C::MatElem{T}) where T <: FieldElem
  CEF = rref(C)[2]
  pivots = find_pivots(CEF)
  S = zero_matrix(base_ring(C), ncols(C), ncols(C))
  _copy_matrix_into_matrix(S, 1, 1, C)
  j = nrows(C)+1
  for i = 1:ncols(C)
    if i in pivots
      continue
    end
    S[j, i] = 1
    j += 1
  end
  return S
end

function find_invariant_complement(M::MatElem{T}, C::MatElem{T}) where T <: FieldElem
  #I follow Geck's approach. It would be nice if we were able to do the computation without
  # a base change
  #First, I have to complete to a basis C
  S = complete_to_basis(C)
  Sinv = inv(S)
  TB = S*M*Sinv
  ed = zero_matrix(base_ring(M), ncols(C), 1)
  ed[nrows(C), 1] = 1
  N = zero_matrix(base_ring(M), ncols(C), ncols(C))
  N[nrows(C), 1] = 1
  for i = 2:nrows(C)
    ed = TB*ed
    for j = 1:ncols(C)
      N[j, i] = ed[j, 1]
    end
  end
  K = kernel(N, side = :left)
  return K*S
end

function _closure(M::MatElem{T}, v::MatElem{T}, d::Int) where T <: FieldElem
  res = zero_matrix(base_ring(M), d, ncols(M))
  for i = 1:ncols(M)
    res[1, i] = v[1, i]
  end
  w = v
  for i = 2:d
    w = w*M
    for j = 1:ncols(M)
      res[i, j] = w[1, j]
    end
  end
  return res
end

#M represents a linear map on a vector space and S gives a basis for an invariant subspace.
#The function returns a matrix representing the restriction of the linear map to the subspace
function restriction(M::MatElem{T}, S::MatElem{T}) where T <: FieldElem
  TR = S*M
  fl, R = can_solve_with_solution(S, TR, side = :left)
  if !fl
    error("The subspace is not invariant!")
  end
  return view(R, 1:nrows(S), 1:nrows(S))
end


@doc raw"""
    _rational_canonical_form_setup(M)

Returns minpolys, the basis transformation and the vectors generating the blocks of the
rational canonical form of $M$.
"""
function _rational_canonical_form_setup(M::MatElem{T}) where T <: FieldElem
  K = base_ring(M)
  Kt, t = polynomial_ring(K, "t", cached = false)
  v, mp = maximal_vector(M, Kt)
  pols = typeof(mp)[mp]
  basis_transf = typeof(M)[]
  gens = typeof(v)[v]
  C = _closure(M, v, degree(mp))
  push!(basis_transf, C)
  K = find_invariant_complement(M, C)
  N = restriction(M, K)
  bound = degree(mp)
  while sum(nrows(x) for x in basis_transf) < nrows(M)
    w, mp1 = maximal_vector(N, Kt, bound)
    push!(pols, mp1)
    push!(gens, w*K)
    subclos = _closure(N, w, degree(mp1))
    push!(basis_transf, subclos*K)
    if nrows(subclos) == nrows(N)
      break
    end
    K1 = find_invariant_complement(N, subclos)
    K = K1*K
    N = restriction(M, K)
    bound = degree(mp1)
  end
  return pols, basis_transf, gens
end

@doc raw"""
    rational_canonical_form(M::MatElem{T}) where T <: FieldElem -> MatElem{T}, MatElem{T}

Returns matrices $C$ and $S$ such that $C = SMS^{-1}$ and $C$ is in rational canonical form.
"""
function rational_canonical_form(M::MatElem{T}) where T <: FieldElem
  @assert is_square(M)
  pols, basis_transf, gens = _rational_canonical_form_setup(M)
  N = zero(M)
  S = zero(M)
  ind = nrows(M)+1
  for i = 1:length(pols)
    C = companion_matrix(pols[i])
    ind -= nrows(C)
    _copy_matrix_into_matrix(N, ind, ind, C)
    _copy_matrix_into_matrix(S, ind, 1, basis_transf[i])
  end
  return N, S
end

function pre_factorization(pols::Vector)
  coprime_factors = Vector{typeof(pols[1])}(undef, length(pols))
  coprime_factors[length(pols)] = pols[length(pols)]
  for i = length(pols)-1:-1:1
    coprime_factors[i] = ppio(pols[i], pols[i+1])[2]
  end
  factors = Vector{typeof(coprime_factors[1])}()
  for i = 1:length(coprime_factors)
    fac = factor(coprime_factors[i])
    for (p, v) in fac
      push!(factors, divexact(p, leading_coefficient(p)))
    end
  end
  return factors
end

function factor_over(f::PolyRingElem{T}, l::Vector) where T <: FieldElem
  exps = Vector{Int}(undef, length(l))
  for i = 1:length(l)
    exps[i] = Int(valuation(f, l[i]))
  end
  return exps
end

function refine_for_jordan(pols::Vector, gens::Vector, M::MatElem)
  factors = pre_factorization(pols)
  gens_polys_mults = Vector{Tuple{typeof(gens[1]), typeof(pols[1]), Int}}()
  for i = length(pols):-1:1
    lef = factor_over(pols[i], factors)
    for j = 1:length(lef)
      if iszero(lef[j])
        continue
      end
      vj = gens[i]*Hecke._subst(divexact(pols[i], factors[j]^lef[j]), M)
      push!(gens_polys_mults, (vj, factors[j], lef[j]))
    end
  end
  return factors, gens_polys_mults
end

@doc raw"""
    jordan_normal_form(M::MatElem{T}) where T <: FieldElem -> MatElem{T}, MatElem{T}

Returns matrices $J$ and $S$ such that $J = SMS^{-1}$ and $J$ is in Jordan normal form.
"""
function jordan_normal_form(M::MatElem{T}) where T <: FieldElem
  @assert is_square(M)
  pols, basis_transf, gens = _rational_canonical_form_setup(M)
  factors, gens_polys_mults = refine_for_jordan(pols, gens, M)
  J = zero(M)
  S = zero(M)
  ind = 1
  for i = 1:length(factors)
    for j = 1:length(gens_polys_mults)
      el = gens_polys_mults[j]
      if el[2] != factors[i]
        continue
      end
      JB = jordan_block(factors[i], el[3])
      _copy_matrix_into_matrix(J, ind, ind, JB)
      #Now, the transformation
      N = Hecke._subst(factors[i], M)
      w = el[1]
      for k = 1:el[3]
        aux = w
        for t = 1:degree(el[2])
          for s = 1:ncols(M)
            S[ind+(k-1)*degree(el[2])+t-1, s] = aux[1, s]
          end
          aux = aux*M
        end
        w = w*N
      end
      ind += nrows(JB)
    end
  end
  return J, S
end


@doc raw"""
    jordan_decomposition(M::MatElem{T}) where T <:FieldElem -> MatElem{T}, MatElem{T}

Returns matrices $S$ and $N$ such that $N$ is nilpotent, $S$ is semisimple and $M = S+N$.
"""
function jordan_decomposition(M::MatElem{T}) where T <: FieldElem
  @assert is_square(M)
  K = base_ring(M)
  pols, basis_transf, gens = _rational_canonical_form_setup(M)
  factors, gens_polys_mults = refine_for_jordan(pols, gens, M)
  J = similar(M)
  B = similar(M)
  N = similar(M)
  ind = 1
  for i = 1:length(factors)
    for j = 1:length(gens_polys_mults)
      el = gens_polys_mults[j]
      if el[2] != factors[i]
        continue
      end
      #Now, the transformation
      N1 = Hecke._subst(factors[i], M)
      w = el[1]
      for k = 1:el[3]
        aux = w
        for t = 1:degree(el[2])
          for s = 1:ncols(M)
            B[ind+(k-1)*degree(el[2])+t-1, s] = aux[1, s]
          end
          aux = aux*M
        end
        w = w*N1
      end
      for c = 1:el[3]-1
        N[ind+c*degree(el[2])-1, ind+c*degree(el[2])] = one(K)
      end
      JB = jordan_block(factors[i], 1)
      for c = 1:el[3]
        _copy_matrix_into_matrix(J, ind, ind, JB)
        ind += degree(el[2])
      end
    end
  end
  Binv = inv(B)
  return Binv*J*B, Binv*N*B
end

@doc raw"""
    multiplicative_jordan_decomposition(M::MatElem{T}) where T <:FieldElem -> MatElem{T}, MatElem{T}

Returns matrices $S$ and $U$ such that $U$ is unipotent, $S$ is semisimple and $M = SU$.
"""
function multiplicative_jordan_decomposition(M::MatElem{T}) where T <:FieldElem
  S, N = jordan_decomposition(M)
  U = inv(S)*N + identity_matrix(base_ring(M), ncols(M))
  return S, U
end


################################################################################
#
#  Algorithm from Steel - Requires factorization!
#
################################################################################

function split_primary(L::Dict, M::MatElem{T}) where T <: FieldElem
  for (g, S) in L
    newl = Vector{Tuple{MatElem{T}, MatElem{T}}}()
    for (W, w) in S
      if !iszero(w)
        push!(newl, (W, w))
        continue
      end
      #I need the sequence of the kernels of g^i(M) \cap W
      #So I restrict to W the endomorphism
      MW = restriction(M, W)
      #Now, MW is the restriction of M to W.
      #I compute g(MW) and then the kernels of the powers
      gMW = Hecke._subst(g, MW)
      kernels = Vector{typeof(M)}()
      push!(kernels, zero_matrix(base_ring(MW), 0, ncols(gMW)))
      K = kernel(gMW, side = :left)
      rref!(K)
      push!(kernels, K)
      M1 = gMW
      while true
        M1 *= gMW
        if iszero(M1)
          push!(kernels, identity_matrix(base_ring(MW), ncols(M1)))
          break
        end
        K = kernel(M1, side = :left)
        rref!(K)
        push!(kernels, K)
      end
      #Now, I start taking vectors from the kernels till I generate the entire space
      subgen = zero_matrix(base_ring(M), 0, ncols(K))
      for i = length(kernels)-1:-1:1
        j = 1
        to_reduce = vcat(kernels[i], subgen)
        rref!(to_reduce)
        while j <= nrows(kernels[i+1])
          ej = sub(kernels[i+1], j:j, 1:ncols(K))
          res = Hecke.cleanvect(to_reduce, ej)
          while iszero(res) && j < nrows(kernels[i+1])
            j += 1
            ej = sub(kernels[i+1], j:j, 1:ncols(K))
            res = Hecke.cleanvect(to_reduce, ej)
          end
          if iszero(res)
            break
          end
          C = closure_with_pol(ej, MW)[1]
          push!(newl, (C*W, ej*W))
          subgen = vcat(subgen, C)
          rref!(subgen)
          if nrows(subgen) == nrows(W)
            i = 1
            break
          end
          to_reduce = vcat(kernels[i], subgen)
          rref!(to_reduce)
          j += 1
        end
      end
    end
   L[g] = newl
  end
  return L
end

function jordan_normal_form1(M::MatElem{T}) where T <: FieldElem
  K = base_ring(M)
  L = decompose_primary(M)
  L = split_primary(L, M)
  J = similar(M)
  B = similar(M)
  ind = 1
  for (g, v) in L
    d = degree(g)
    for i = 1:length(v)
      e = divexact(nrows(v[i][1]), d)
      J1 = jordan_block(g, e)
      w = v[i][2]
      for k = 1:e
        aux = w
        for j = 1:degree(g)
          aux = aux*M
          for s = 1:ncols(M)
            B[ind+(k-1)*d+j-1, s] = aux[1, s]
          end
        end
        w = w*Hecke._subst(g, M)
      end
      _copy_matrix_into_matrix(J, ind, ind, J1)
      ind += d*e
    end
  end
  return J, B
end

function rational_canonical_form1(M::MatElem{T}) where T <: FieldElem
  K = base_ring(M)
  L = decompose_primary(M)
  L = split_primary(L, M)
  #order the subspace by dimension
  max_length = 0
  for (q, v) in L
    v1 = sort(v, by = x -> nrows(x[1]))
    if length(v1) > max_length
      max_length = length(v1)
    end
    L[q] = v1
  end
  vectors_and_minpolys = Vector{Tuple{typeof(M), typeof(first(keys(L)))}}(undef, max_length)
  Kt = parent(first(keys(L)))
  for i = 1:max_length
    mp = one(Kt)
    w = zero_matrix(K, 1, ncols(M))
    for (q, v) in L
      if length(v) < i
        continue
      end
      W = v[length(v)-i+1][1]
      gw = v[length(v)-i+1][2]
      mult = divexact(nrows(W), degree(q))
      w += gw
      mp *= q^mult
    end
    vectors_and_minpolys[i] = (w, mp)
  end
  #Now, the matrix and the transformation matrix
  CF = similar(M)
  TM = similar(M)
  ind = 1
  for i = max_length:-1:1
    w, mp = vectors_and_minpolys[i]
    C = companion_matrix(mp)
    _copy_matrix_into_matrix(CF, ind, ind, C)
    S = closure_with_pol(w, M)[1]
    _copy_matrix_into_matrix(TM, ind, 1, S)
    ind += nrows(S)
  end
  return CF, TM
end

################################################################################
#
#  Simultaneous diagonalization
#
################################################################################

function commute_pairwise(L::Vector{S}) where S <: Hecke.MatElem{T} where T <:Hecke.FieldElem

  n = length(L)

  # Check pairwise commutativity
  for i in 1:n
    for j in i+1:n
      if L[i]*L[j] != L[j]*L[i]
        return false
      end
    end
  end
  return true
end

function is_simultaneous_diagonalizable(L::Vector{S}) where S <: Hecke.MatElem{T} where T <:Hecke.FieldElem

  if !commute_pairwise(L)
    return false
  end

  for i = 1:length(L)
    f = minpoly(L[i])
    if !is_squarefree(f)
      return false
    end
    lr = roots(f)
    if length(lr) != degree(f)
      return false
    end
  end
  return true
end


function _intersect(A::Hecke.MatElem{T}, B::Hecke.MatElem{T}) where T <: Hecke.FieldElem
  n = Hecke.nrows(A)
  M = Hecke.vcat(A, B)
  N = kernel(M, side = :left)
  return view(N, 1:nrows(N), 1:n)*A
end


function simultaneous_diagonalization(L...; check::Bool = true)
  return simultaneous_diagonalization(collect(L), check = check)
end

@doc raw"""
    simultaneous_diagonalization(L::Vector{S}; check::Bool=false)

Returns a tuple whose first entry is the transformation matrix and whose
second entry is an array of matrices containing the diagonal forms of
the elements of $L$. If "check" is set to `true`, the algorithm checks whether
the matrices in $L$ are simultaneous diagonalizable before computing the transformation matrix. Default value is "true".
"""
function simultaneous_diagonalization(L::Vector{S}; check::Bool = true) where S <: MatElem{T} where T <: FieldElem

  if check
    if !is_simultaneous_diagonalizable(L)
      error("The matrices are not simultaneous diagonalizable")
    end
  end

  n = length(L)
  if n == 1
    error("Only one matrix as input!")
  end
  s = Hecke.nrows(L[1])

  # Compute transformation matrix
  CE = common_eigenspaces(L, side = :left)
  A = reduce(vcat, values(CE))

  # Compute diagonal forms
  D = [ zero_matrix(base_ring(L[1]), nrows(L[1]), ncols(L[1])) for i = 1:length(L) ]
  m = 0
  for (v, k) in CE
    nr = Hecke.nrows(k)
    for j in 1:nr
      for i in 1:n
        D[i][m + j, m + j] = v[i]
      end
    end
    m = m + nr
  end
  return A, D
end

@doc raw"""
    simultaneous_diagonalization(L::Vector{MatElem}, K::Field; check::Bool=false)

Returns a tuple whose first entry is the transformation matrix and whose
second entry is an array of matrices containing the diagonal forms of
the elements of $L$ computed over the field $K$. If "check" is set to `true`, the algorithm checks whether
the matrices in $L$ are simultaneous diagonalizable before computing the transformation matrix. Default value is "true".
"""
function simultaneous_diagonalization(L::Vector{S}, K::W; check::Bool = true) where S <: MatElem{T} where T <: FieldElem where W<:Field
  L1 = [change_base_ring(K, x) for x in L]
  return simultaneous_diagonalization(L1, check = check)
end

@doc raw"""
    common_eigenspaces(L::Vector{<: MatElem{T}}; side::Symbol = :left)
      where T <: FieldElem -> Dict{Vector{T}, MatElem{T}}

Return a dictionary containing vectors of eigenvalues of the matrices in `L` as
keys and the corresponding eigenspaces as values, that is, if `(k, v)` is a pair
of a key and a value, then `v` is the eigenspace of `L[i]` w.r.t. the eigenvalue
`k[i]` for all `i`.
If side is `:right`, the right eigenspaces are computed, if it is `:left` then the
left eigenspaces are computed.
"""
function common_eigenspaces(L::Vector{<: MatElem{T}}; side::Symbol = :left) where T <: FieldElem
  eigs = [ eigenspaces(M; side = side) for M in L ]
  return intersect_eigenspaces([ Dict([x] => v for (x, v) in eig) for eig in eigs ], side = side)
end

function intersect_eigenspaces(L::Vector{Dict{Vector{T}, S}}; side::Symbol = :left) where S <: MatElem{T} where T <: FieldElem
  @assert !isempty(L)

  n = length(L)
  if n == 1
    return L[1]
  elseif n == 2
    D = Dict{keytype(L[1]), valtype(L[1])}()
    for (k1, v1) in L[1]
      for (k2, v2) in L[2]
        if side == :right
          I = transpose(_intersect_spaces(transpose(v1), transpose(v2)))
        else
          I = _intersect_spaces(v1, v2)
        end
        if !iszero(I)
          push!(D, vcat(k1, k2)  => I)
        end
      end
    end
    return D
  else
    k = floor(typeof(n), n//2)
    return intersect_eigenspaces([ intersect_eigenspaces(L[1:k], side = side), intersect_eigenspaces(L[k + 1:n], side = side) ], side = side)
  end
end
