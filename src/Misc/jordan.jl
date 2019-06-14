
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

function spectrum(M::MatElem{T}, L) where T <: FieldElem
  @assert issquare_matrix(M)
  M1 = change_base_ring(M, L)
  return spectrum(M1)
end

function issquare_matrix(M::MatElem)
  return ncols(M) == nrows(M)
end

eigenvalues(M::MatElem{T}) where T <: FieldElem = spectrum(M)
eigenvalues(M::MatElem{T}, L) where T <: FieldElem = spectrum(M, L)

function eigenspace(M::MatElem{T}, lambda::T) where T <: FieldElem
  @assert issquare_matrix(M)
  N = deepcopy(M)
  for i = 1:ncols(N)
    N[i, i] -= lambda
  end
  return Hecke.left_kernel_basis(N)
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

function companion_matrix(p::PolyElem)
  K = base_ring(p)
  M = zero_matrix(K, degree(p), degree(p))
  for i = 1:degree(p)-1
    setindex!(M, one(K), i, i+1)
  end
  for i = 1:degree(p)
    setindex!(M, -coeff(p, i-1), degree(p), i) 
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
      @show "here"
      WM1 = W*M
      fl, MW = Hecke.can_solve(W, WM1, side = :right)
      @assert fl
      gMW = Hecke._subst(g, MW)
      kernels = Vector{typeof(M)}()
      d, K = kernel(gMW, side = :left)
      push!(kernels, K)
      M1 = gMW
      while true
        M1 *= gMW
        if iszero(M1)
          break
        end
        d1, K = kernel(M1, side = :left)
        push!(kernels, K)
      end 
      #Now, I start taking vectors from the kernels till I generate the entire space
      subgen = zero_matrix(base_ring(M), 0, ncols(K))
      for i = length(kernels):-1:1
        j = 1
        while true
          ej = zero_matrix(base_ring(M), 1, ncols(K))
          ej[1, j] = 1
          res = Hecke.cleanvect(kernels[i], ej)
          res = Hecke.cleanvect(subgen, ej)
          while iszero(res) && j < ncols(K)
            ej[1, j] = 0
            j += 1
            ej[1, j] = 1
            res = Hecke.cleanvect(kernels[i], ej)
            res = Hecke.cleanvect(subgen, ej)
          end 
          if iszero(res)
            break
          end
          C = closure_with_pol(res, MW)[1]
          push!(newl, (C, res))
          subgen = vcat(subgen, C)
          rref!(subgen)
        end
      end
    end
    L[g] = newl
  end
  return L
end

function jordan_normal_form(M::MatElem{T}) where T <: FieldElem
  K = base_ring(M)
  L = decompose_primary(M)
  L = split_primary(L, M)
  J = similar(M)
  B = similar(M)
  ind = 1
  for (g, v) in L
    d = degree(g)
    @show v
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
  return Binv*N*B, Binv*S*B
end

function multiplicative_jordan_decomposition(M::MatElem{T}) where T <:FieldElem
  K = base_ring(M)
  L = decompose_primary(M)
  L = split_primary(L, M)
  U = similar(M)
  S = similar(M)
  B = similar(M)
  ind = 1
  for (g, v) in L
    d = degree(g)
    if iszero(coeff(g, 0))
      error("The matrix is not invertible")
    end
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
