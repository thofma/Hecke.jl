export spectrum, eigenspace, jordan_normal_form, rational_canonical_form, companion_matrix

@doc Markdown.doc"""
    spectrum(M::MatElem{T}) where T <: FieldElem -> Dict{T, Int}
Returns the spectrum of a matrix, i.e. the set of eigenvalues of M with multiplicities.
"""
function spectrum(M::MatElem{T}) where T <: FieldElem
  @assert issquare_matrix(M)
  K = base_ring(M)
  f = charpoly(M)
  fac = factor(f) #Should use roots! But needs to take into account
                  #multiplicities
  D = Dict{elem_type(K), Int}()
  for (g, v) in fac
    if degree(g) > 1
      continue
    end
    lambda = -coeff(g, 0)
    D[lambda] = v
  end
  return D
end

@doc Markdown.doc"""
    spectrum(M::MatElem{T}) where T <: FieldElem -> Dict{T, Int}
Returns the spectrum of a matrix over the field L, i.e. the set of eigenvalues of M with multiplicities.
"""
function spectrum(M::MatElem{T}, L) where T <: FieldElem
  @assert issquare_matrix(M)
  M1 = change_base_ring(M, L)
  return spectrum(M1)
end


function issquare_matrix(M::MatElem)
  return ncols(M) == nrows(M)
end

eigvals(M::MatElem{T}) where T <: FieldElem = spectrum(M)
eigvals(M::MatElem{T}, L) where T <: FieldElem = spectrum(M, L)

@doc Markdown.doc"""
    eigenspace(M::MatElem{T}, lambda::T) where T <: FieldElem -> Vector{MatElem{T}}
Returns a basis of the eigenspace of $M$ with respect to the eigenvalues $lambda$
"""
function eigenspace(M::MatElem{T}, lambda::T) where T <: FieldElem
  @assert issquare_matrix(M)
  N = deepcopy(M)
  for i = 1:ncols(N)
    N[i, i] -= lambda
  end
  res = Hecke.left_kernel_basis(N)
  resvect = [matrix(base_ring(M), 1, ncols(M), x) for x in res]
  return resvect
end

function closure_with_pol(v::MatElem{T}, M::MatElem{T}) where T <: FieldElem
  i = 1
  E = rref(v)[2]
  w = v*M
  res = Hecke.cleanvect(E, w)
  while !iszero(res)
    v = vcat(v, w)  
    E = vcat(E, res)
    rref!(E)
    i += 1
    w = w*M
    res = Hecke.cleanvect(E, w)
  end
  fl, c = Hecke.can_solve(v, w, side = :left)
  @assert fl
  return v, c
end

function decompose_primary(M::MatElem{T}) where T <: FieldElem
  dimsum = 0
  i = 1
  K = base_ring(M)
  Kt, t = PolynomialRing(K, "t", cached = false)
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
          #W containes some subspaces but it is independent from the others
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

function _copy_matrix_into_matrix(A::MatElem, i::Int, j::Int, B::MatElem)
  for k in 0:nrows(B) - 1
    for l in 0:ncols(B) - 1
      setindex!(A, B[k+1, l+1], i+k, j+l) 
    end
  end
  return nothing
end


@doc Markdown.doc"""
    companion_matrix(p::PolyElem) -> MatElem
Returns the companion matrix of $p = \sum_{i=0}^n a_ix^i$, i.e. the matrix


    0 1  0  $\dots$  0 
    0  0  1  $\dots$  0
    $\vdots$  $\vdots$  $\ddots$  $\vdots$  $\vdots$
    0  0  $\vdots$  0  1 
    $-a_0$  $-a_1$  $-a_2$  $\dots$  $a_{n-1}$ 
  
"""
function companion_matrix(p::PolyElem)
  K = base_ring(p)
  p1 = divexact(p, lead(p))
  M = zero_matrix(K, degree(p), degree(p))
  for i = 1:degree(p)-1
    setindex!(M, one(K), i, i+1)
  end
  for i = 1:degree(p)
    setindex!(M, -coeff(p1, i-1), degree(p), i) 
  end
  return M
end

function jordan_block(p::PolyElem, e::Int)
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
      WM1 = W*M
      fl, MW = Hecke.can_solve(W, WM1, side = :right)
      @assert fl
      #Now, MW is the restriction of M to W.
      #I compute g(MW) and then the kernels of the powers
      gMW = Hecke._subst(g, MW)
      kernels = Vector{typeof(M)}()
      push!(kernels, zero_matrix(base_ring(MW), 0, ncols(gMW)))
      d, K = kernel(gMW, side = :left)
      rref!(K)
      push!(kernels, K)
      M1 = gMW
      while true
        M1 *= gMW
        if iszero(M1)
          push!(kernels, identity_matrix(base_ring(MW), ncols(M1)))
          break
        end
        d1, K = kernel(M1, side = :left)
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


@doc Markdown.doc"""
    jordan_normal_form(M::MatElem{T}) where T <: FieldElem -> MatElem{T}, MatElem{T}
Returns matrices $J$ and $S$ such that $J = SMS^{-1}$ and $J$ is in Jordan normal form.
"""
function jordan_normal_form(M::MatElem{T}) where T <: FieldElem
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

@doc Markdown.doc"""
    jordan_decomposition(M::MatElem{T}) where T <:FieldElem -> MatElem{T}, MatElem{T}
Returns matrices $S$ and $N$ such that $N$ is nilpotent, $S$ is semisimple and $M = S+N$.
"""
function jordan_decomposition(M::MatElem{T}) where T <: FieldElem
  K = base_ring(M)
  L = decompose_primary(M)
  L = split_primary(L, M)
  S = similar(M)
  N = similar(M)
  B = similar(M)
  ind = 1
  for (g, v) in L
    d = degree(g)
    for i = 1:length(v)
      e = divexact(nrows(v[i][1]), d)
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
      for c = 1:e-1
        N[ind+c*d-1, ind+c*d] = one(K)
      end
      J1 = jordan_block(g, 1)
      for c = 1:e
        _copy_matrix_into_matrix(S, ind, ind, J1)
        ind += d
      end
    end
  end
  Binv = inv(B)
  return Binv*S*B, Binv*N*B
end

@doc Markdown.doc"""
    multiplicative_jordan_decomposition(M::MatElem{T}) where T <:FieldElem -> MatElem{T}, MatElem{T}
Returns matrices $S$ and $U$ such that $U$ is unipotent, $S$ is semisimple and $M = SU$.
"""
function multiplicative_jordan_decomposition(M::MatElem{T}) where T <:FieldElem
  S, N = jordan_decomposition(M)
  U = inv(S)*N + identity_matrix(base_ring(M), ncols(M))
  return S, U
end

@doc Markdown.doc"""
    rational_canonical_form(M::MatElem{T}) where T <: FieldElem -> MatElem{T}, MatElem{T}
Returns matrices $C$ and $S$ such that $C = SMS^{-1}$ and $C$ is in rational canonical form.
"""
function rational_canonical_form(M::MatElem{T}) where T <: FieldElem
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

@doc Markdown.doc"""
    issimilar(M::MatElem{T}, N::MatElem{T}) where T <: FieldElem -> Bool
Returns true if the matrices are similar (conjugated) and false otherwise.
"""
function issimilar(M::MatElem{T}, N::MatElem{T}) where T <: FieldElem
  CM = rational_canonical_form(M)[1]
  CN = rational_canonical_form(N)[1]
  return CM == CN
end

@doc Markdown.doc"""
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


#=
function maximal_vector(M::MatElem{T}) where T <: FieldElem
  
  K = base_ring(M)
  Kt, t = PolynomialRing(K, "t", cached = false)
  v = zero_matrix(K, 1, ncols(M))
  v[1, 1] = 1
  C, coeffs_vect = closure_with_pol(v, M)
  if nrows(C) == nrows(M)
    return v
  end
  coeffs = T[coeffs_vect[1, i] for i = 1:length(coeffs_vect)]
  push!(coeffs, K(1))
  mp = Kt(coeffs)
  rref!(C)
  for i = 2:nrows(M)
    v1 = zero_matrix(K, 1, ncols(M))
    v1[1, i] = 1
    res = Hecke.cleanvect(C, v1)
    if iszero(res)
      continue
    end
    C1, coeffs_vect2 = closure_with_pol(v1, M)
    if nrows(C1) == nrows(M)
      return true
    end
    coeffs2 = T[coeffs_vect2[1, i] for i = 1:length(coeffs_vect)]
    push!(coeffs2, K(1))
    mp2 = Kt(coeffs2)
    if isone(gcd(mp1, mp2))
      v = v + v1
      C, coeffs_vect = closure_with_pol(v, M)
      if nrows(C) == nrows(M)
        return v
      end
      coeffs = T[coeffs_vect[1, i] for i = 1:length(coeffs_vect)]
      push!(coeffs, K(1))
      mp = Kt(coeffs)
      rref!(C)
    end 
  end

end
=#
