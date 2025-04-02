function maximal_order(K::AbsNonSimpleNumField; discriminant::ZZRingElem = ZZRingElem(-1), ramified_primes::Vector{ZZRingElem} = ZZRingElem[])
  return get_attribute!(K, :maximal_order) do
    O = maximal_order_from_components(K)
    O.is_maximal = 1
    return O
  end::AbsNumFieldOrder{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}
end



###############################################################################
#
#  Generic code for orders
#
###############################################################################

function new_maximal_order(O::AbsNumFieldOrder{<:NumField{QQFieldElem}, <:NumFieldElem{QQFieldElem}}; index_divisors::Vector{ZZRingElem} = ZZRingElem[], disc::ZZRingElem = ZZRingElem(-1), ramified_primes::Vector{ZZRingElem} = ZZRingElem[])
  return maximal_order_round_four(O, index_divisors = index_divisors, disc = disc, ramified_primes = ramified_primes)
end

function maximal_order_round_four(O::AbsNumFieldOrder{<:NumField{QQFieldElem}, <:NumFieldElem{QQFieldElem}}; index_divisors::Vector{ZZRingElem} = ZZRingElem[], disc::ZZRingElem = ZZRingElem(-1), ramified_primes::Vector{ZZRingElem} = ZZRingElem[])
  return _maximal_order_round_four(O; index_divisors = index_divisors, disc = disc, ramified_primes = ramified_primes)
end

function _maximal_order_round_four(O::AbsNumFieldOrder{<:NumField{QQFieldElem}, <:NumFieldElem{QQFieldElem}}; index_divisors::Vector{ZZRingElem} = ZZRingElem[], disc::ZZRingElem = ZZRingElem(-1), ramified_primes::Vector{ZZRingElem} = ZZRingElem[])
  OO = O
  M = trace_matrix(O)
  l = divisors(M, discriminant(O))
  if !isempty(index_divisors)
    push!(l, index_divisors)
  end
  if !isempty(ramified_primes)
    push!(l, ramified_primes)
  end
  l = coprime_base(l)
  for s in l
    if disc != -1
      u = divexact(discriminant(OO), disc)
      if isone(gcd(u, s))
        continue
      end
    end
    @vtime :AbsNumFieldOrder fac = factor(s)
    for (p, j) in fac
      @vprintln :AbsNumFieldOrder 1 "Computing p-maximal overorder for $p ..."
      O1 = pmaximal_overorder(O, p)
      if valuation(discriminant(O1), p) < valuation(discriminant(OO),p)
        OO += O1
      end
      @vprintln :AbsNumFieldOrder 1 "done"
    end
  end
  OO.is_maximal = 1
  return OO
end


function maximal_order_from_components(L::AbsNonSimpleNumField; disc::ZZRingElem = ZZRingElem(-1), ramified_primes::Vector{ZZRingElem} = ZZRingElem[])
  BKs, lp, disc_order = _maximal_order_of_components(L)
  B = _product_basis(BKs)
  OO = order(L, B, check = false, cached = false, isbasis = true)
  OO.disc = disc_order
  if disc != -1 && discriminant(OO) == disc
    OO.is_maximal = 1
    return OO
  end
  if ngens(L) == 1
    OO.is_maximal = 1
    return OO
  end
  if !isempty(ramified_primes)
    append!(lp, ramified_primes)
  end
  lp = coprime_base(lp)
  for p in lp
    if is_prime(p)
      OO = pmaximal_overorder(OO, p)
    else
      fac = factor(p)
      for (k, v) in fac
        OO = pmaximal_overorder(OO, k)
      end
    end
  end
  OO.is_maximal = 1
  return OO
end

function _product_basis(l::Vector{Vector{AbsNonSimpleNumFieldElem}})
  nelems = 1
  for i = 1:length(l)
    nelems *= length(l[i])
  end
  K = parent(l[1][1])
  B = typeof(l[1])(undef, nelems)
  ind = length(l[1])
  for i = 1:ind
    B[i] = l[1][i]
  end
  for jj = 2:length(l)
    new_deg = length(l[jj])
    for i = 2:new_deg
      for j = 1:ind
        B[(i-1)* ind + j] = K(B[j].data * l[jj][i].data, false)
      end
    end
    ind *= new_deg
  end
  return B
end

function product_basis(l::Vector{Vector{T}}) where T <: Union{AbsNumFieldOrderElem, RelNumFieldOrderElem, NumFieldElem}
  nelems = 1
  for i = 1:length(l)
    nelems *= length(l[i])
  end
  B = typeof(l[1])(undef, nelems)
  ind = length(l[1])
  for i = 1:ind
    B[i] = l[1][i]
  end
  for jj = 2:length(l)
    new_deg = length(l[jj])
    for i = 2:new_deg
      for j = 1:ind
        B[(i-1)* ind + j] = B[j] * l[jj][i]
      end
    end
    ind *= new_deg
  end
  return B
end

function product_basis(l1::Vector{T}, l2::Vector{T}) where T <: Union{AbsNumFieldOrderElem, RelNumFieldOrderElem, NumFieldElem}
  B = Vector{typeof(l1[1])}(undef, length(l1)*length(l2))
  for i = 1:length(l1)
    B[i] = l1[i]
  end
  for i = 1:length(l2)
    for j = 1:length(l1)
      B[(i-1)* length(l1) + j] = B[j] * l2[i]
    end
  end
  return B
end

function _maximal_order_of_components(L::AbsNonSimpleNumField)
  Qx, x = polynomial_ring(QQ, "x")
  fields = Vector{Tuple{AbsSimpleNumField, NumFieldHom{AbsSimpleNumField, AbsNonSimpleNumField}}}(undef, length(L.pol))
  for i = 1:length(L.pol)
    fields[i] = component(L, i)
  end
  #Now, bring the maximal order of every component in L
  B = Vector{Vector{AbsNonSimpleNumFieldElem}}(undef, length(fields))
  d = ZZRingElem(1)
  for i = 1:length(fields)
    OK = maximal_order(fields[i][1])
    d *= discriminant(OK)^(divexact(degree(L), degree(OK)))
    BOK = basis(OK, fields[i][1])
    BK = Vector{AbsNonSimpleNumFieldElem}(undef, degree(OK))
    for j = 1:length(BK)
      BK[j] = fields[i][2](BOK[j])
    end
    B[i] = BK
  end
  lp = ZZRingElem[]
  for i = 1:length(fields)
    for j = i+1:length(fields)
      push!(lp, gcd(discriminant(maximal_order(fields[i][1])), discriminant(maximal_order(fields[j][1]))))
    end
  end
  return B, lp, d
end

function pradical_trace1(O::AbsNumFieldOrder{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}, p::Union{Int, ZZRingElem})
  return pradical_trace(O, p)
end

function new_pradical_frobenius1(O::AbsNumFieldOrder{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}, p::Int)
  R = Native.GF(p, cached = false)
  d = degree(O)
  K = nf(O)
  Rx = polynomial_ring(R, "x", cached = false)[1]
  Zx = polynomial_ring(ZZ, "x")[1]
  j = clog(ZZRingElem(d), p)
  els_in_pradical = elem_type(O)[]
  M1 = zero_matrix(ZZ, 2*d, d)
  gens = elem_type(O)[O(p)]
  for i = 1:ngens(K)
    g = to_univariate(Globals.Qx, K.pol[i])
    sqf = factor_squarefree(Rx(g))
    p1 = one(Rx)
    for (x, v) in sqf
      if v > 1
        p1 = mul!(p1, p1, x)
      end
    end
    pol = lift(Zx, p1)
    elK = O(evaluate(pol, K[i]))
    push!(gens, elK)
    Mi = representation_matrix_mod(elK, ZZRingElem(p))
    _copy_matrix_into_matrix(M1, 1, 1, Mi)
    hnf_modular_eldiv!(M1, ZZRingElem(p), :lowerleft)
  end
  powers = Dict{Int, Vector{ZZRingElem}}()
  B = basis(O, copy = false)
  it = 0
  while true
    if it == j
      I = ideal(O, M1; check=false, M_in_hnf=true)
      reverse!(gens)
      I.gens = gens
      I.minimum = ZZRingElem(p)
      return I
    end
    it += 1
    indices = Int[]
    for i = 1:d
      if !isone(M1[i, i])
        push!(indices, i)
      end
    end
    nr = length(indices)
    A = zero_matrix(R, d, nr + d)
    ind = 0
    for i in 1:d
      if !(i in indices)
        continue
      end
      ind += 1
      if haskey(powers, i)
        ar = copy(powers[i])
        for k in 1:d
          A[k, ind] = ar[k]
        end
      else
        t = powermod(B[i], p, p)
        ar = coordinates(t, copy = true)
        powers[i] = copy(ar)
        if iszero(t)
          continue
        end
        for k in 1:d
          A[k, ind] = R(ar[k])
        end
      end
    end
    for s = 1:d
      for i = 1:s
        A[i, s+nr] = R(M1[s, i])
      end
    end
    X = kernel(A, side = :right)
    if is_zero(ncols(X))
      I = ideal(O, M1; check=false, M_in_hnf=true)
      reverse!(gens)
      I.gens = gens
      I.minimum = ZZRingElem(p)
      return I
    end
    #First, find the generators
    new_gens = Vector{elem_type(O)}()
    for i = 1:ncols(X)
      coords = zeros(ZZ, d)
      for j=1:nr
        coords[indices[j]] = lift(X[j, i])
      end
      if !iszero(coords)
        new_el = O(coords)
        push!(new_gens, new_el)
      end
    end
    if iszero(length(new_gens))
      I = ideal(O, M1; check=false, M_in_hnf=true)
      reverse!(gens)
      I.gens = gens
      I.minimum = ZZRingElem(p)
      return I
    end
    #Then, construct the basis matrix of the ideal
    m1 = zero_matrix(ZZ, length(new_gens) + d, d)
    for i = 1:length(new_gens)
      el = coordinates(new_gens[i], copy = true)
      for j = 1:nr
        m1[i, indices[j]] = el[indices[j]]
      end
    end
    for i = 1:d
      for s = 1:i
        m1[i+length(new_gens), s] = M1[i, s]
      end
    end
    hnf_modular_eldiv!(m1, ZZRingElem(p), :lowerleft)
    M1 = sub(m1, length(new_gens)+1:nrows(m1), 1:d)
    append!(gens, new_gens)
  end
end
