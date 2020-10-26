################################################################################
#
#  Simplify
#
################################################################################

function simplify(K::NfRel{nf_elem}; cached::Bool = true, prec::Int = 100)
  Kabs, mK, mk = absolute_field(K, cached = false)
  OK = maximal_order(K)
  new_basis = Vector{nf_elem}(undef, degree(Kabs))
  B = pseudo_basis(OK)
  ideals = Dict{NfOrdIdl, Vector{nf_elem}}()
  for i = 1:length(B)
    I = B[i][2].num
    if !haskey(ideals, I)
      bas = lll_basis(I)
      ideals[I] = nf_elem[mK\(K(x)) for x in bas]
    end
  end
  ind = 1
  for i = 1:degree(OK)
    I = B[i][2]
    bI = ideals[I.num]
    el = mK\(B[i][1])
    for j = 1:length(bI)
      new_basis[ind] = divexact(el*bI[j], I.den)
      ind += 1
    end
  end
  O = NfOrd(new_basis)
  O.ismaximal = 1
  O.disc = absolute_discriminant(OK)
  if prec == 100
    OLLL = lll(O)
  else
    OLLL = lll(O, prec = prec)
  end
  el = _simplify(OLLL, mK)
  pel = mK(el)
  f = minpoly(pel)
  @assert degree(f) == degree(K)
  Ks = number_field(f, cached = cached, check = false)[1]
  mKs = hom(Ks, K, pel)
  return Ks, mKs
end

#Finds a small elements given by small combinations of the basis of O 
#that generates the extension given by mK
function _simplify(O::NfOrd, mK::NfToNfRel)
  L = nf(O)
  #First, we choose the candidates
  B = basis(O, L)
  a = gen(L)
  Bnew = nf_elem[]
  nrep = min(3, degree(L))
  for i = 1:length(B)
    push!(Bnew, B[i])
    for j = 1:nrep
      push!(Bnew, B[i]+B[j])
      push!(Bnew, B[i]-B[j])
    end
  end

  #Now, we test for primitiveness.
  Lrel = codomain(mK)
  OLrel = maximal_order(Lrel)
  K = base_field(Lrel)
  OK = maximal_order(K)

  n = degree(Lrel)

  P, d = _find_prime(Lrel)
  p = minimum(P, copy = false)
  abs_deg = degree(P)*d
  FP, mFP = ResidueField(OK, P)
  mFP1 = extend_easy(mFP, K)
  #First, we search for elements that are primitive using block systems
  F = FlintFiniteField(p, abs_deg, "w", cached = false)[1]
  emb = find_embedding(FP, F)
  rt = roots(map_coeffs(emb, map_coeffs(mFP1, Lrel.pol)))

  indices = Int[]
  for i = 1:length(Bnew)
    if isone(denominator(Bnew[i]))
      continue
    end
    if _is_primitive_via_block(mK(Bnew[i]), rt, mFP1, emb)
      push!(indices, i)
    end
  end
  #Now, we select the one of smallest T2 norm
  I = t2(a)
  for i = 1:length(indices)
    t2n = t2(Bnew[indices[i]])
    if t2n < I
      a = Bnew[indices[i]]
      I = t2n
    end
  end
  return a
end

function find_embedding(F::FqFiniteField, K::FqFiniteField)
  f = defining_polynomial(F)
  rt = roots(f, K)
  img = rt[1]
  return (x -> sum([coeff(x, i)*img^i for i = 0:degree(F)-1]))
end


function _is_primitive_via_block(a::NfRelElem{nf_elem}, rt::Vector{fq}, mF, emb)
  n = degree(parent(a))
  pol = data(a)
  polF = map_coeffs(emb, map_coeffs(mF, pol))
  nconjs = 1
  conjs = Set{fq}([evaluate(polF, rt[1])])
  for i = 2:length(rt)
    ev = evaluate(polF, rt[i])
    if ev in conjs
      return false
    end
    push!(conjs, ev)
    nconjs += 1
    if nconjs > div(n, 2)
      return true
    end
  end
  error("Something went wrong")
end


function _block(a::NfRelElem{nf_elem}, rt::Vector{fq}, mF, emb)
  pol = data(a)
  polF = map_coeffs(emb, map_coeffs(mF, pol))
  evs = fq[evaluate(polF, x) for x in rt]
  b = Vector{Int}[]
  a = BitSet()
  i = 0
  n = length(rt)
  while i < length(evs)
    i += 1
    if i in a
      continue
    end
    z = evs[i]
    push!(b, findall(x-> evs[x] == z, 1:n))
    for j in b[end]
      push!(a, j)
    end
  end
  return b
end

function _find_prime(L::NfRel{nf_elem})
  p = 2^10
  K = base_field(L)
  OK = maximal_order(K)
  OL = maximal_order(L)

  n_attempts = min(degree(L), 10)
  candidates = Vector{Tuple{NfOrdIdl, Int}}(undef, n_attempts)
  i = 1
  f = L.pol
  threshold = degree(f)^2
  while i < n_attempts+1
    p = next_prime(p)
    if isindex_divisor(OK, p)
      continue
    end
    lp = prime_decomposition(OK, p)
    P = lp[1][1]
    if isindex_divisor(OL, P)
      continue
    end
    F, mF = ResidueField(OK, P)
    mF1 = extend_easy(mF, K)
    fF = map_coeffs(mF1, f)
    if degree(fF) != degree(f) || !issquarefree(fF)
      continue
    end
    FS = factor_shape(fF)
    d = lcm(Int[x for (x, v) in FS])
    if d < threshold
      candidates[i] = (P, d)
      i += 1
    end
  end
  res =  candidates[1]
  for j = 2:n_attempts
    if candidates[j][2] < res[2]
      res = candidates[j]
    end
  end
  return res[1], res[2]
end