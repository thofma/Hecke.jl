add_verbose_scope(:GenRep)
add_assert_scope(:GenRep)

export genus_representatives

################################################################################
#
#  SpinorGeneraCtx
#
################################################################################

# To keep track of ray class groups
mutable struct SpinorGeneraCtx
  mR::MapRayClassGrp # ray class group map
  mQ::GrpAbFinGenMap # quotient
  rayprimes::Vector{NfAbsOrdIdl{AnticNumberField, nf_elem}}
  criticalprimes::Vector{NfAbsOrdIdl{AnticNumberField, nf_elem}}
  
  function SpinorGeneraCtx()
    return new()
  end
end

function SpinorGeneraCtx(L::QuadLat)
  R = base_ring(L)
  F = number_field(R)

  RCG, mRCG, Gens = _compute_ray_class_group(L)

  # 1) Map the generators into the class group to create the factor group.

  subgroupgens = GrpAbFinGenElem[_map_idele_into_class_group(mRCG, [g]) for g in Gens ]

  for g in gens(RCG)
    push!(subgroupgens, 2*g)
  end

  Q, mQ = quo(domain(mRCG), subgroupgens)

  @vprint :GenRep 1 "Ray class group: size = $(order(RCG))\n"
  @vprint :GenRep 1 "Ray class group quotient: size = $(order(Q))
  (this is the number of spinor + genera in Genus(L))\n"

  # 2) Find good generators (that is: generators which are not dyadic, and not
  #    in BadPrimes(L) -- so that neighbour generation is always possible),
  #    of this factor group.
  
  #   Only pick ideles of the form (1,...,1,p,1,...,1) so that:
  #   a) nothing has to be corrected before they can be mapped down into the factor group
  #   b) we can simply store the prime ideal and know that it corresponds to
  #      the (1,...,1,p,1,...,1) These prime ideals will be stored in
  #      SpinorGeneraCtx.criticalprimes.
  #
  #   the primes which generate the spinor genera in Genus(L):
  #   if L is not definite, we need one prime for each factor group element.
  #   if L is definite, we only need a generating set of primes for the factor group.

  inf_plc = defining_modulus(mRCG)[2]
  
  critical_primes = _get_critical_primes(L, mRCG, inf_plc, mQ, true) # fulllist = not isdefinite?
  @vprint :GenRep 1 "good primes over $([minimum(q) for q in critical_primes])
  (together with the squares) generate the subgroup.\n"

  res = SpinorGeneraCtx()

  res.mR = mRCG
  res.mQ = mQ
  res.criticalprimes = critical_primes
  res.rayprimes = collect(keys(mRCG.fact_mod))

  return res
end

################################################################################
#
#  Genus representatives for quadratic lattices
#
################################################################################

@doc Markdown.doc"""
    genus_representatives(L::QuadLat; max = inf, use_auto = false)

Computes representatives for the isometry classes in the genus of $L$.

At most `max` representatives are returned. The use of automorphims can be
disabled by
"""
function genus_representatives(L::QuadLat; max = inf, use_auto = false)
  @req rank(L) >= 3 "Lattice must have rank >= 3"
  # Otherwise the isomorphism to the class group fails, cf. §102 in O'Meara.
  @req max >= 1 "Must find at least one representative"

  if !isdefinite(L)
    @vprint :GenRep 1 "Genus representatives of indefinite lattice\n"
    return spinor_genera_in_genus(L, [])
  end

  res = typeof(L)[]

  p = _smallest_norm_good_prime(L)

  spinor_genera = spinor_genera_in_genus(L, typeof(p)[p])

  @vprint :GenRep 1 "Found $(length(spinor_genera)) many spinor genera in genus\n"

  for LL in spinor_genera
    @hassert :GenRep 3 all(!isisometric(X, LL)[1] for X in res)
    new_lat =  iterated_neighbours(LL, p, use_auto = use_auto, max = max - length(res))
    append!(res, new_lat)
  end

  return res
end

function spinor_genera_in_genus(L, mod_out)
#{A sequence of lattices representing the spinor genera in the genus of L}
  @req rank(L) >= 3 "(Currently) rank must be at least 3"
  # Otherwise the isomorphism to the class group fails, cf. §102 in O'Meara.

  # We have to find out whether ProperSpinorGenus == SpinorGenus.
  
  # 1) Find a nonzero element in the norm group of L.
  C = SpinorGeneraCtx(L)

  # We don't need minimal generators, to make them not too large.
  G = gram_matrix_of_generators(L, false)

  # The smaller the element, the better
  dia = map(x -> abs(norm(x)), diagonal(G))
  b, k = findmin(dia)
  if !iszero(b)
    spinornorm = G[k, k]
  else
    i = 1
    while iszero(G[1, i])
      i += 1
      if i > ncols(G)
        throw(error("Lattice is degenerated"))
      end
      @assert !iszero(G[1, i])
      spinornorm = 2 * G[1, i]
    end
  end

  # 2) At a place p where spinornorm does not generate norm(L_p)
  #    we add <p, spinornorm * normgenerator > to the idele
  
  R = base_ring(L)
  F = number_field(R)
  nor = norm(L)

  differ = ideal_type(R)[]
  for p in vcat(support(nor), support(spinornorm * R))
    if valuation(nor, p) != valuation(spinornorm, p)
      push!(differ, p)
    end
  end

  idele = Tuple{ideal_type(R), elem_type(F)}[]

  for p in unique(vcat(differ, C.rayprimes))
    if isdyadic(p)
      _,_,_,a = _genus_symbol_kirschmer(L, p).data
      norm = a[1]
    else
      GS = _genus_symbol_kirschmer(L, p)
      G = GS.data
      pi = GS.x
      norm = pi^G[1][2]
      if G[1][1] == 1 && G[1][3] == -1
        k, h = ResidueField(R, p)
        norm = norm * elem_in_nf(h\non_square(k))
      end
    end
    push!(idele, (p, spinornorm * norm))
  end

  # 3) Map the idele into the idele class group.
  #    Then h == 0 iff SpinorGenus == ProperSpinorGenus
  
  g = _map_idele_into_class_group(C.mR, idele)
  h = C.mQ(g)

  # 4) Now there are 2^#primes spinor genera, which can be reached by neighbours:

  modout = push!(elem_type(codomain(C.mQ))[ C.mQ(_map_idele_into_class_group(C.mR,  [(p, elem_in_nf(uniformizer(p)))])) for p in mod_out], h)
  primes = _spinor_generators(L, C, modout)

  res = typeof(L)[ L ]

  for p in primes
    N = neighbours(L, p, max = 1)[1]
    pN = pseudo_matrix(N)
    for i in 1:length(res)
      pM = pseudo_matrix(res[i])
      new_pm = _sum_modules(_module_scale_ideal(p, pM), pN)
      new_pm = _intersect_modules(new_pm, _module_scale_ideal(inv(p), pM))
      LL = lattice(ambient_space(L), new_pm)
      # LL = (p*M + N) \cap p^-1 * M
      push!(res, LL)
    end
  end

  return res
end
  
function _smallest_norm_good_prime(L)
  OK = base_ring(L)
  lp = [p for p in bad_primes(L, even = true) if isdyadic(p) || !ismodular(L, p)[1]]
  limit = 20
  while true
    lq = prime_ideals_up_to(OK, limit)
    for q in lq
      if !(q in lp)
        return q
      end
    end
    limt = 2 * limit
    if limit > 2^5
      throw(error("Something off"))
    end
  end
end

# The spinor norm of L at p, as calculated by C. Beli for dyadic p and by M.
# Kneser for non-dyadic p. 
#
# Returns a subspace of local_multiplicative_group_modulo_squares(p), and a
# boolean which is true iff the spinor norm is exactly the units
function spinor_norm(L, p)
  V, g, ginv = local_multiplicative_group_modulo_squares(p)
  R = base_ring(L)
  e = valuation(R(2), p)
  if !isdyadic(p)
    # cf. Satz 3 in Kneser, "Klassenzahlen indefiniter quadratischer Formen in
    # drei oder mehr Veränderlichen":
    J, G, E = jordan_decomposition(L, p)
    if any(g -> ncols(g) >= 2, G)
      @vprint(:GenRep, 1,"""Spinor norm over $(minimum(p))
  This lattice has a 2-dimensional Jordan constituent, and p is odd. Spinor norm
  is either F^* or O_F^*(F^*)^2, i.e. we will find a vector space of dimension
  $(rank(V)) or $(rank(V) - 1).\n""")
      # Which of the two is the case?
      # TODO: It is not a good idea to rely on implementation details of
      #       local_multiplicative_group_modulo_squares
      if length(unique([e % 2 for e in E])) == 1
        return basis(V)[1:dim(V) - 1], V, g, ginv, true
      else
        return basis(V), V, g, ginv, false 
      end
    end
    # This is the obscure case where p is odd and each of its Jordan components
    # has dimension 1. In this case, the units need not be contained in the
    # Spinor norm.
    #
    # Generators of the (principal) norm ideals of the Jordan components: since
    # p is odd, the norms (and the scales) are just the dimensions of the
    # Jordan components
     normgens = nf_elem[g[1,1] for g in G]

     twonormgens = nf_elem[]

     for i in 1:length(normgens)
       for j in 1:length(normgens)
         push!(twonormgens, normgens[i] * normgens[j])
       end
     end
     
     twonormvectors = [ginv(x) for x in twonormgens]
    
     @vprint :GenRep "Spinor norm odd p, norm generators of the $(length(G)) Jordan components are: $(normgens), $(twonormgens) $(twonormvectors)"
    # cf. Kneser 1956, Satz 3:
    _SN, mS = sub(V, twonormvectors)
    @assert length(rels(_SN)) == 0 # free
    SN = [ mS(s) for s in gens(_SN) ]
  else
    bong = good_bong(L, p)
    @hassert :GenRep 1 isgood_bong(bong, p)
    if !has_propertyA(L, p)
      @vprint(:GenRep, 1,"""Spinor norm over dyadic prime:
  This lattice does not have property A. Spinor norm is either F^* or
  O_F^*(F^*)^2, i.e. we will find a vector space of dimension $(rank(V)) or
  $(rank(V) - 1)\n""")
      # Using section 7, Thm. 3 in Beli 2002, one can decide which of the two
      # cases applies. This is why we needed to compute a *good* BONG:
      for i in 1:(length(bong) - 1)
        BG, mBG = G_function(bong[i + 1]//bong[i], V, g, ginv, p)
        for bg in gens(BG)
          if mBG(bg)[dim(V)] != 0
            # the whole group
            return basis(V), V, g, ginv, false
          end
        end
      end

      for i in 1:(length(bong) - 2)
        if valuation(bong[i], p) == valuation(bong[i + 2], p)
          @assert iszero(mod(valuation(bong[i + 1], p) - valuation(bong[i], p), 2))
          if mod(div(valuation(bong[i + 1], p) - valuation(bong[i], p), 2), 2) != mod(e, 2)
            # the whole group
            return basis(V), V, g, ginv, false
          end
        end
      end

      # If all checks have passed, the spinor norm is exactly the units:
      return basis(V)[1:(dim(V) - 1)], V, g, ginv, true
    end
    # cf. Beli 2003, Thm. 1
    SN = elem_type(V)[]
    for i in 2:rank(L)
      #SN = SN + G_function(bong[i]//bong[i - 1], V, g, ginv, p)
      _G, _mG = G_function(bong[i]//bong[i - 1], V, g, ginv, p)
      _SN, mS = sub(V, append!(SN, [_mG(g) for g in gens(_G)]))
      @assert length(rels(_SN)) == 0 # free
      SN = [ mS(s) for s in gens(_SN) ]
    end
    # For why we can take the Minimum in what follows here, see the remark on p. 161 in Beli 2003:
    k = findfirst(i -> mod(valuation(bong[i + 2], p) - valuation(bong[i], p), 2) == 0, 1:(rank(L) - 2))
    if k !== nothing
      alpha = minimum(div(valuation(bong[i + 2], p) - valuation(bong[i], p), 2) for i in 1:(rank(L) - 2) if mod(valuation(bong[i + 2], p) - valuation(bong[i], p), 2) == 0)
      # SN = SN + one_plus_power_of_P(alpha, V, g, ginv, P)
      _G, _mG = _one_plus_power_of_p(alpha, V, g, ginv, p)
      _SN, mS = sub(V, append!(SN, [_mG(g) for g in gens(_G)]))
      @assert length(rels(_SN)) == 0 # free
      SN = [ mS(s) for s in gens(_SN) ]
    end
  end
  # Test if S is equal to SN
  S, mS = sub(V, basis(V)[1:(dim(V) - 1)])
  @assert length(rels(S)) == 0
  W,_ = sub(V, append!(basis(V)[1:(dim(V) - 1)], SN))
  @assert length(rels(W)) == 0
  if ngens(W) == dim(V) - 1 # this means SN + V[1:dim(V) -1] == V[1:dim(V) - 1]
    fl = true
  else
    fl = false
  end

  return SN, V, g, ginv, fl
end

# Helper function to find y such that xy^2 is integral and Valuation(xy^2, p) = 0
function _square_rep_nice(x, p, piinv)
  x = x * denominator(x, order(p))^2
  v = valuation(x, p)
  @assert v >= 0 && iseven(v)
  if !iszero(v)
    x = x * piinv^v
  end
  return order(p)(x)
end

# Given a prime ideal over some number field K, this returns a vector space
# over GF(2) isomorphic to K_p^/(K_p^*)^2 and a map representing the isomorphism
#
# TODO: Proper types/maps and cache this in the dyadic case
function local_multiplicative_group_modulo_squares(p)
  R = order(p)
  @assert ismaximal(R)
  K = number_field(R)
  @assert isabsolute(K)
  if !isdyadic(p)
    pi = uniformizer(p)
    k, h = ResidueField(R, p)
    hext = extend(h, K)
    e = elem_in_nf(h\non_square(k))
    F = GF(2, cached = false)
    V = vector_space(F, 2)
    mf = function(x)
      if x[1] == 0
        y = one(K)
      else
        y = e
      end
      if x[2] == 1
        y = y * pi
      end
      return y
    end

    mg = function(y)
      v = valuation(y, p)
      if issquare(hext(y//pi^v))[1]
        fir = F(0)
      else
        fir = F(1)
      end

      return V([fir, F(v)])
    end

    return V, mf, mg
  else
    pi = uniformizer(p)
    e = ramification_index(p)
    F = GF(2, cached = false)
    dim = valuation(norm(p), 2) * e + 2
    V = vector_space(F, dim)
    I = p^(2*e + 1)
    Q, h = quo(R, I)
    U, g = unit_group(Q)
    M, i = quo(U, 2)
    S, mS = snf(M)
    @assert ngens(S) == dim - 1
    piinv = anti_uniformizer(p)
    
    mf = x -> begin
      y = elem_in_nf(h\(g(i\(mS(S([lift(x[i]) for i in 1:(dim - 1)]))))))
      if x[dim] == 1
        y = y * pi
      end
      return y
    end

    mg = y -> begin
      v = valuation(y, p)
      w = mS\(i(g\(h(_square_rep_nice(y * pi^v, p, piinv)))))
      return V(push!(elem_type(F)[F(w[i]) for i in 1:dim - 1], F(v)))
    end

    return V, mf, mg
  end
end

function non_square(F::Union{GaloisField, FqFiniteField})
  r = rand(F)
  while iszero(r) || issquare(r)[1]
    r = rand(F)
  end
  return r
end

# Return a good BONG of L at a dyadic prime p, as defined by C. Beli.
function good_bong(L, p)
# Any BONG obtained from a maximal norm splitting is good, cf. Corollary 4.2 in Beli.
# If a maximal norm splitting is calculated, a good BONG can be read off by joining
# together the BONGs of the 1- and 2-dimensional components.
  @req base_ring(L) == order(p) "Incompatible arguments"
  @req isdyadic(p) "Prime must be dyadic"
  G, JJ = maximal_norm_splitting(L, p)
  K = nf(base_ring(L))
  bong = nf_elem[]
  for i in 1:length(G)
    GG = G[i]
    if nrows(GG) == 2
      bong = append!(bong, _make_bong_dim_2(quadratic_lattice(K, identity_matrix(K, 2), gram_ambient_space = GG), p))
    elseif nrows(GG) == 1
      push!(bong, GG[1, 1])
    else
      throw(error("This should not happen"))
    end
  end
  return bong
end

# A maximal norm splitting of L at a dyadic prime p, as defined by C. Beli. 
# Returns a Jordan decomposition into 1x1 and 2x2 components, and the
# corresponding list of basis vectors.
function maximal_norm_splitting(L, p)
  # Follow Beli, "Representation of Integral Quadratic Forms over Dyadic Local Fields", section 7
  @req base_ring(L) == order(p) "Incompatible arguments"
  @req isdyadic(p) "Prime must be dyadic"

  R = base_ring(L)
  K = nf(R)
  e = ramification_index(p)
  uni = uniformizer(p)
  J, G, _ = jordan_decomposition(L, p)
  # join J into one matrix of base vectors
  JJ = reduce(vcat, J)
  # join the individual Gram matrices:
  A = diagonal_matrix(G)

  # read the finer decomposition:
  G = dense_matrix_type(elem_type(K))[]
  steps = UnitRange{Int}[]
  i = 1
  n = ncols(A)
  while i <= n
    if i != n && !iszero(A[i, i + 1])
      size = 2
    else
      size = 1
    end
    push!(G, sub(A, i:(i + size - 1), i:(i + size - 1)))
    push!(steps, i:(i + size - 1))
    i = i + size
  end

  if all(s -> length(s) == 1, steps)
    return G, JJ
  end

  # Now turn this decomposition into unary/binary components into a maximal norm splitting
  failset = Int[]
  while true
    #  Scale valuations sL, norm generators aL, norm valuations uL, weight
    #  valuations wL of the decomposition
    sL, aL, uL, wL = _scales_and_norms(G, p, uni)

    failset_old = failset
    b, i, failset = __ismaximal_norm_splitting(G, sL, aL, p)
    @assert isempty(failset_old) || length(failset_old) > length(failset)
    if b
      break
    end
    @assert i >= 0
    # If b is false and i == 0, something is wrong with our lattice

    # Here comes the interesting stuff:
    @assert length(steps[i]) == 2
    # Unary components already have maximal norm.

    # The maximal norm splitting condition is violated at index i.
    find_j = append!([valuation(aL[k], p) for k in (i+1):length(aL)], [2*(sL[i] - sL[k]) + valuation(aL[k], p) for k in 1:(i - 1)])
    @assert length(find_j) > 0
    min, j = findmin(find_j)
    if j <= length(aL) - i
      j = j + i
      # We want j to correspond to a Jordan component, not an index in find_j
      @assert j > i
      # This is case 1 in Beli.
      beli_correction!(L, G, JJ, steps, i, j, p)
    else
      j = j - (length(aL) - i)
      # We want j to correspond to a Jordan component, not an index in find_j
      @assert j < i
      # This is case 2 in Beli.
      # Switch to a basis of the dual lattice L^#: 
      for k in 1:length(steps)
        for l in 1:length(steps[k])
          for u in 1:ncols(JJ)
            JJ[steps[k][l], u] = JJ[steps[k][l], u] * uni^(-sL[k])
          end
        end
        B = sub(JJ, steps[k][1]:steps[k][length(steps[k])], 1:ncols(JJ))

        @assert valuation(scale(quadratic_lattice(K, identity_matrix(K, nrows(B)), gram_ambient_space = B * gram_matrix(ambient_space(L)) * B')), p) == -sL[k]
      end
      # Apply case 1 to the reversed orthogonal sum of the dual lattices:

      steps = reverse!(steps)
      # Update Gram matrices for the reversed, dualized lattice:
      for k in 1:length(G)
        B = sub(JJ, steps[k][1]:steps[k][length(steps[k])], 1:ncols(JJ))
        G[k] = B * gram_matrix(ambient_space(L)) * B'
        @assert nrows(G[k]) in [1, 2]
      end
      # Component i is now at position #aL-i+1
      @assert length(steps[length(aL) - i + 1]) == 2
      beli_correction!(L, G, JJ, steps, length(aL) - i + 1, length(aL) - j + 1, p)
      steps = reverse!(steps)
      G = reverse!(G)
      # Update norms/scales from the updated Gram matrices:
      sL, aL, uL, wL = _scales_and_norms(G, p, uni)
      # Dualize again
      # JJ[steps[k][l]] *:= uniformizer^(-sL[k]); 
      for k in 1:length(steps)
        for l in 1:length(steps[k])
          for u in 1:ncols(JJ)
            JJ[steps[k][l], u] = JJ[steps[k][l], u] * uni^(-sL[k])
          end
        end
      end

      # Update Gram matrices
      for k in 1:length(G)
        B = sub(JJ, steps[k][1]:steps[k][length(steps[k])], 1:ncols(JJ))
        G[k] = B * gram_matrix(ambient_space(L)) * B'
        @assert nrows(G[k]) in [1, 2]
      end
    end
  end

  @assert all(k -> nrows(G[k]) in [1,2], 1:length(G))
  return G, JJ
end

# Returns true iff BONG is a good BONG at p, as defined by C. Beli.
function isgood_bong(bong, p)
  v = all(valuation(bong[i], p) <= valuation(bong[i + 2], p) for i in 1:(length(bong)- 2))
  return v
end

function has_propertyA(L, p)
  @assert isdyadic(p)
  rL, sL, wL, aL = _genus_symbol_kirschmer(L, p).data
  nL = [valuation(aL[i], p) for i in 1:length(aL)]
  r = maximum(rL)
  if r > 2
    @vprint(:GenRep,1,"""Property A is violated over dyadic prime:
  There is a $(r)-dimensional Jordan component\n""")
  end
  
  # genus: rL, sL, wL, aL note that aL only contains valuations
  for i in 1:length(sL)
    for j in (i + 1):length(sL)
      if !((0 < nL[j] - nL[i]) && (nL[j] - nL[i] < 2*(sL[j] - sL[i])))
        @vprint(:GenRep, 1, """Property A is violated over dyadic prime:
  Violated at $(i) $(j) (norm/scale valuations do not fit)\n""")
        return false
      end
    end
  end
  return true
end

function G_function(a, V, g, ginv, p)
# Use LocalMultiplicativeGroupModSquares to calculate in F*/(O^*)^2
# (or F^*/(F^*)^2 -- the last component of the result is the p-valuation
# mod 2, and  F^*/(F^*)^2 =  F*/(O^*)^2 \times C_2.)
#
# Also we expect V, g, ginv = local_multiplicative_group_modulo_scares(p)
#
# cf. Beli 2003, Def. 4.
  O = order(p)
  K = nf(O)
  e = valuation(order(p)(2), p)
  R = valuation(a, p)
  d = relative_quadratic_defect(-a, p)
 
  if !is_in_A(a, p)
    @vprint :GenRep 2 "G_function case F\n"
    return N_function(-a, g, ginv, p)
  elseif ginv(K(-1//4)) == ginv(a)
    @vprint :GenRep 2 "G_function case G\n"
    return sub(V, basis(V)[1:dim(V) - 1])
  elseif valuation(-4 * a, p) == 0 && islocal_square(-4 * a, p)
    @vprint :GenRep 2 "G_function case G\n"
    return sub(V, basis(V)[1:dim(V) - 1])
  elseif R > 4 * e
    @vprint :GenRep 2 "G_function case H\n"
    return sub(V, [ginv(a)])
  elseif 2*e < R && R <= 4 * e
    if d <= 2 * e - R//2
      @vprint :GenRep 2 "G_function case A\n"
      I = _intersect(N_function(-a, g, ginv, p), sub(V, [ginv(a)]))
      O = _one_plus_power_of_p(R + d - 2*e, V, g, ginv, p)
      return _sum(I, O)
    else
      @vprint :GenRep 2 "G_function case B\n"
      @assert R % 2 == 0
      W, mW = _one_plus_power_of_p(div(R, 2), V, g, ginv, p)
      @assert length(rels(W)) == 0
      return sub(V, append!([ginv(a)], mW(w) for w in gens(W)))
    end
  elseif R <= 2 * e
    if d  <= e - R//2
      @vprint :GenRep 2 "G_function case C\n"
      return N_function(-a, g, ginv, p)
    elseif (e - R//2 < d) && (d <= 3 * e//2 - R//4)
      @assert R % 2 == 0
      @vprint :GenRep 2 "G_function case D\n"
      return _intersect(N_function(-a, g, ginv, p),
                        _one_plus_power_of_p(div(R, 2) + d - e, V, g, ginv, p))
    else
      @vprint :GenRep 2 "G_function case E\n"
      # Attention! Use the floor function wherever Beli writes stuff in square
      # brackets. This is due to his citing Hsia's papers, which have this
      # convention.
      return _one_plus_power_of_p(e - floor(Int, e//2 - R//4), V, g, ginv, p)
    end
  else
    throw(error("This should never happen"))
  end
end

# Returns the valuation of the relative quadratic defect of a at the prime
# ideal p, as defined by C. Beli
function relative_quadratic_defect(a, p)
  q = quadratic_defect(a, p)
  if q isa PosInf
    return inf
  else
    return q - valuation(a, p)
  end
end

# cf. Lemma 3.5 in Beli: A is the set of all a \in F^* for which either
# (-a\not\in (F^*)^2 and D(-a) \subseteq O_p) or (-a\in (F^*)^2 and ord(a)\geq
# -2e).
function is_in_A(a, p)
  e = valuation(order(p)(2), p)
  q = quadratic_defect(-a, p)
  if q isa Int
    if q >= 0
      return true
    end
  end

  if q isa PosInf
    if valuation(a, p) >= -2 * e
      return true
    end
  end

  return false
end

function N_function(a, g, ginv, p)
  #  g, ginv is the mapping obtained by local_multiplicative_group_modulo_squares(p).
  b = ginv(a)

  V = parent(b)

  q = quadratic_defect(a, p)

  # project a into F^*/(O^*)^2:

  if q isa PosInf
    # treat the squares separately:
    return sub(V, basis(V))
  end

  B = basis(V)
  
  # cf. paragraph before 1.2 in Beli 2003:
  # N(a) := N(F(\sqrt(a))/F), i.e. the values of the norm mapping of the quadratic extension
  # and N(a) is the orthogonal complement of (<a>(F^*)^2). 
  preimages = Vector{Int}(undef, length(B))
  for i in 1:length(B)
    b = B[i]
    preim = g(b)
    # convert the Hasse symbol (as an element of the multiplicative group C_2)
    # to an element of the additive group F_2:
    preimages[i] = hilbert_symbol(a, preim, p) == 1 ? 0 : 1
  end
  kernel_gen = elem_type(V)[ B[i] for i in 1:length(B) if preimages[i] == 0 ]
  # this fails if a is a square
  j = minimum(i for i in 1:length(B) if preimages[i] == 1)
  for i in 1:length(B)
    if preimages[i] == 1 && i != j
      push!(kernel_gen, B[i] + B[j])
    end
  end

  S, mS = sub(V, kernel_gen)
  @assert length(rels(S)) == 0 # free
  return S, mS
end

# Map an idele into the ray class group associated to L. The parameter idele
# must be a list of tuples <p, a_p>, where p is a prime of base_ring(L), and a_p
# is an element of K^* (interpreted as an element of the completion K^*_p). The
# parameter atinfinity can be a list of tuples <v, +1 or -1>, where v is an
# element of real_places(nf(base_ring(L))). All places, finite or infinite, which
# are unspecified are interpreted as 1.}
function _map_idele_into_class_group(mRCG, idele, atinfinity::Vector{Tuple{InfPlc, Int}} = Tuple{InfPlc, Int}[])
  R = order(base_ring(codomain(mRCG)))
  F = nf(R)
  IP = defining_modulus(mRCG)[2]
  the_idele_inf = [1 for i in IP]
  if length(atinfinity) != 0
    for pl in atinfinity
      if pl[1] in IP
        the_idele_inf = pl[2]
      end
    end
  end
  M = defining_modulus(mRCG)[1]
  
  # The finite places we need to make congruent to 1 in order to be able to map into the class group:
  rayprimes = collect(keys(mRCG.fact_mod))
  exponents = Int[mRCG.fact_mod[p] for p in rayprimes]
  factors = ideal_type(R)[rayprimes[i]^exponents[i] for i in 1:length(rayprimes)]
  the_idele = [ one(F) for p in rayprimes ]
  for i in idele
    j = findfirst(isequal(i[1]), rayprimes)
    if j isa Int # found
      the_idele[j] = i[2]
    else
      #throw(error("Impossible?"))
      # ignore this
    end
  end
  # So, only the ideals D that are coprime to the ray lie in the codomain of mRCG and can be mapped 
  #
  # The ideles we are considering here are considered to be representatives of
  # classes of ideles (modulo (F^*_S)*J^L, where F^*_S is the set of principal
  # ideles which are totally positive at the infinite places where the
  # envelopping space V of L is anisotropic, and where J^L is the set of ideles
  # which lie in the spinor norm of L at all finite places.  So, we may modify
  # the ideles in the following two ways without changing their class:
  # 1 multiply every component by an element of F^*
  # 2 multiply any individual component (at p) by an element of the spinor
  #   norms of L_p. In particular, any component is only relevant modulo
  #   squares.
  #
  # Thus we can achieve that the idele in question is congruent to 1 modulo the
  # ray M that defines the RCG
  #
  # The idele is then interpreted as the ideal \prod_p{p^Valuation(idele_p, p)}, which can be mapped into the class group.
  #
  # first, we need to be able to invert modulo the divisor of RCG
  #
  if any(valuation(the_idele[i], rayprimes[i]) != 0 for i in 1:length(the_idele))
    # We need to correct with an element of F^* which is positive at the relevant infinite places.
  # We will first correct only the finite places ...
    s = approximate([-valuation(the_idele[i], rayprimes[i]) for i in 1:length(the_idele)], rayprimes)
  else
    s = one(F)
  end

  # Now s * Idele is a unit at the RayPrimes
  # Now rescale once more with some t in F^* such that t*s*Idele = 1 mod MM and has the correct signs.

  sidele = Vector{elem_type(R)}(undef, length(rayprimes))
  for i in 1:length(the_idele)
    Q, mQ = quo(R, rayprimes[i]^exponents[i])
    sidele[i] = mQ\mQ(FacElem(s * the_idele[i]))
    # The quotient map can be applied on factored elements
  end

  if length(rayprimes) == 0
    x = one(R)
  else
    x = crt(sidele, factors)
    Q, mQ = quo(R, M)
    x = mQ\inv(mQ(x)) # x = invmod(x, M)
  end

  sgns = [ sign(s, IP[j]) * the_idele_inf[j] for j in 1:length(IP)]

  A, _exp, _log = infinite_primes_map(R, IP, M)
  t = x * (1 + _exp(A([ sgns[j] == sign(x, IP[j]) ? 0 : 1 for j in 1:length(IP)])))
  @assert x - t in M
  @assert all(sign(t, IP[j]) == sgns[j] for j in 1:length(IP))
  #t = crt(M, IP, x, sgns)

  s = s * t

  # Check if everything is ok.
  @hassert :GenRep 1 all(isone(quo(R, factors[k])[2](FacElem(s * the_idele[k]))) for k in 1:length(the_idele))
  @hassert :GenRep 1 all(sign(s * the_idele_inf[j], IP[j]) == 1 for j in 1:length(IP))


  # We first interpret it as the ideal which will actually have to be mapped:
  # i.e., we just collect the p-valuations at the noncritical places (p notin RayPrimes):

  _temp1 = [ idele[j][1] for j in 1:length(idele)]
  _temp2 = fmpz[ valuation(idele[j][2], idele[j][1]) for j in 1:length(idele)]
  ide = s * R
  _to_map = FacElem(Dict(numerator(ide) => fmpz(1), (denominator(ide) * R) => fmpz(-1)))
  if length(_temp1) != 0
    _to_map = _to_map * FacElem(_temp1, _temp2)
  end

  return g = mRCG\_to_map
end

function _compute_ray_class_group(L)
  R = base_ring(L)
  F = number_field(R)

  Gens = Tuple{ideal_type(R), elem_type(F)}[]

  rayprimes = ideal_type(R)[]
  M = 1 * R
  MM = ideal_type(R)[]
  Mfact = Dict{ideal_type(R), Int}()

  for p in bad_primes(L, even = true)
    spinors, V, g, ginv, exactlytheunits = spinor_norm(L, p)
    # we only need to carry around those finite places where the Spinor norm is
    # not exactly the units:
    if !exactlytheunits
      @vprint :GenRep 2 """Found a prime over $(minimum(p)) where the spinor
                           norm is not exactly the units of the order.
                             dim(spinors)=$(length(spinors)),
                             dim(LocalMultGrpModSq)=$(rank(V))"""
      push!(rayprimes, p)
      # A basis of the spinor norm of L at p, when viewed (modulo squares) as an F_2-vector space
      b = spinors
      Gens = append!(Gens, [(p, g(a)) for a in b])
      @assert all(valuation(g(a), p) in [0, 1] for a in b)
      # We rely on local_multiplicative_group_modulo_squares (g) mapping to 0-
      # and 1-valued elements, and on the last base vector of V to represent a
      # uniformizer of p.
      I = p^(1 + 2 * valuation(R(2), p))
      M = M * I
      Mfact[p] = 1 + 2 * valuation(R(2), p)
      push!(MM, I)
    end
  end
  @assert issetequal(support(M), rayprimes)
  
  # Now M contains a ray M and MM is the support of this ray.
  # We now compute the indefinite real places of L
  inf_plc = [v for v in real_places(F) if !isisotropic(L, v)]
  # Now get the ray class group of M, inf_plc.
  return ray_class_group(M, inf_plc, lp = Mfact)..., Gens
end

function _get_critical_primes(L, mRCG, inf_plc, mQ, full = true)
  # Set full = true to calculate one prime for every element of
  # domain(mQ), instead of just one prime for every generator.
  # This is needed for indefinite lattices.

  R = base_ring(L)
  F = nf(R)
  critical_primes = ideal_type(R)[]
  Q = codomain(mQ)

  bad = prod(bad_primes(L, even = true))

  maxnorm = 50
  goodprimes = [ p for p in prime_ideals_up_to(R, maxnorm) if iscoprime(p, bad)]
  p_ind = 1

  grp_elements_to_primes = Dict{ideal_type(R), elem_type(Q)}()

  if full
    cur_list = elem_type(Q)[id(Q)]
    while length(cur_list) < length(Q)
      while p_ind > length(goodprimes)
        maxnorm = floor(Int, maxnorm * 1.2)
        goodprimes = ideal_type(R)[ p for p in prime_ideals_up_to(R, maxnorm) if iscoprime(p, bad)]
      end
      p = goodprimes[p_ind]
      h = mQ(_map_idele_into_class_group(mRCG, [(p, F(uniformizer(p)))]))
      if !haskey(grp_elements_to_primes, h)
        grp_elements_to_primes[p]= h
      end
      oldsize = length(cur_list)
      if !(h in cur_list)
        push!(cur_list, h)
      end
      push!(critical_primes, p)
      p_ind = p_ind + 1
    end
  else
    throw(NotImplemented())
  end

  return critical_primes
end

function _spinor_generators(L, C, mod_out = elem_type(codomain(C.mQ))[])
  bad = [ p for p in bad_primes(L) if !ismodular(L, p)[1] ]
  S, mS = sub(codomain(C.mQ), mod_out)
  n = order(codomain(C.mQ))
  gens = []
  tmp_gens = copy(mod_out)
  R = base_ring(L)
  p = 2
  while order(S) != n
    p = next_prime(p)
    lp = [ p[1] for p in prime_decomposition(R, p) if !(p[1] in bad) ]
    for P in lp
      g = _map_idele_into_class_group(C.mR, [(P, uniformizer(P))])
      h = C.mQ(g)
      if !haspreimage(mS, h)[1]
        push!(gens, P)
        push!(tmp_gens, h)
        S, mS = sub(codomain(C.mQ), tmp_gens)
      end
      if order(S) == n
        break
      end
    end
  end
  return gens
end

# TODO: Enable use_auto
function neighbours(L::QuadLat, p; call = stdcallback, use_auto = false, max = inf)
  R = base_ring(L)
  F = nf(R)
  @req R == order(p) "Incompatible arguments"
  @req isprime(p) "Ideal must be prime"
  ok, rescale = ismodular(L, p)
  @req ok "The lattice must be locally modular"
  @req isisotropic(L, p) "The lattice must be locally isotropic"
  e = valuation(R(2), p)
  @req e == 0 || valuation(norm(L), p) >= e "The lattice must be even"
  B = local_basis_matrix(L, p, type = :submodule)
  n = nrows(B)
  k, h = ResidueField(R, p)
  hext = extend(h, F)
  pi = uniformizer(p)
  piinv = anti_uniformizer(p)
  form = gram_matrix(ambient_space(L), B)
  if rescale != 0
    form = piinv^rescale * form
  end
  pform = map_entries(hext, form)

  if use_auto
    G = automorphism_group_generators(L)
    @hassert :GenRep 1 all(g -> g * gram_matrix(ambient_space(L)) * transpose(g) == gram_matrix(ambient_space(L)), G)
    Binv = inv(B)
    adjust_gens = eltype(G)[B * g * Binv for g in G]
    @hassert :GenRep 1 all(g -> g * form * transpose(g) == form, adjust_gens)
    adjust_gens_mod_p = dense_matrix_type(k)[map_entries(hext, g) for g in adjust_gens]
    adjust_gens_mod_p = dense_matrix_type(k)[x for x in adjust_gens_mod_p if !isdiagonal(x)]
    @hassert :GenRep 1 all(g -> g * pform * transpose(g) == pform, adjust_gens_mod_p)
    if length(adjust_gens_mod_p) > 0
      _LO = line_orbits(adjust_gens_mod_p)
      LO = Vector{eltype(k)}[[x[1][1, i] for i in 1:length(x[1])] for x in _LO]
      @vprint :GenRep 1 "Checking $(length(LO)) representatives (instead of $(div(order(k)^n - 1, order(k) - 1)))\n"
    else
      @vprint :GenRep 1 "Enumerating lines over $k of length $n\n"
      LO = enumerate_lines(k, n)
    end
  else
    @vprint :GenRep 1 "Enumerating lines over $k of length $n\n"
    LO = enumerate_lines(k, n)
  end
 
  result = typeof(L)[]

  pMmat = _module_scale_ideal(p, pseudo_matrix(L))

  # TODO: This is too slow
  _dotk(u, v) = (matrix(k, 1, n, u) * pform * matrix(k, n, 1, v))[1, 1]

  _dotF(u, v) = (matrix(F, 1, n, u) * form * matrix(F, n, 1, v))[1, 1]

  keep = true
  cont = true
  found = false

  for w in LO
    dotww = _dotk(w, w)
    if dotww != 0
      continue
    end
    if iszero(matrix(k, 1, n, w) * pform)
      continue
    end

    x = [ hext\e for e in w]

    nrm = _dotF(x, x)
    val = valuation(nrm, p)
    @assert val > 0
    if val <= e
      continue # can only happen if p is even
    elseif val == e + 1
      # make val > e + 1
      bas = [zero(k) for i in 1:n]
      r = 0
      for i in 1:n
        bas[i] = one(k)
        if _dotk(w, bas) != 0
          r = i
          break
        end
        bas[i] = zero(k)
      end
      @assert r != 0
      u = [zero(F) for i in 1:n]
      u[r] = one(F)
      a = (h\(hext((nrm//(2 * pi * _dotF(x, u))))))
      @. x = x - a * pi * u
      @assert valuation(_dotF(x, x), p) >= e + 2
    end
    found = true
    
    # normalize x

    kk = 0
    for i in 1:n
      if hext(x[i]) != 0
        kk = i
        break
      end
    end
    @assert kk != 0
    x = Ref(h\(inv(hext(x[kk])))) .* x
    if e != 0
      x = Ref(1 + h\(hext((x[kk] - 1)//pi)) * pi) .* x
      @assert valuation(x[kk] - 1, p) >= 2
    end

    xF = matrix(F, 1, n, x) * form
    mm = 0
    for r in 1:n
      if r != kk && !iszero(xF[1, r]) && valuation(xF[1, r], p) == 0
        mm = r
        break
      end
    end
    @assert mm != 0 

    _U = [zero(F) for i in 1:n]
    _U[mm] = one(F)

    _tt = [ Ref(piinv) .* x, Ref(0 * pi) .* _U]
    for i in 1:n
      if i != kk && i != mm
        _t = [zero(F) for i in 1:n]
        _t[i] = one(F)
        push!(_tt, _t .- (Ref(h\hext(xF[1, i]//xF[mm])) .* _U))
      end
    end
    VV = matrix(F, n, n, reduce(vcat, _tt))
    V = VV * B
    LL = lattice(ambient_space(L), _sum_modules(pMmat, pseudo_matrix(V)))

    @hassert :GenRep 1 islocally_isometric(LL, L, p)

    if !(call isa Bool)
      keep, cont = call(result, LL)
    end
    if keep
      push!(result, LL)
    end

    if !cont || length(result) >= max
      break
    end
  end
  if !found
    @warn "L_p/pL_p has no suitable isotropic vector!"
  end
  return result
end

function iterated_neighbours(L::QuadLat, p; use_auto = false, max = inf)
  @req isdefinite(L) "Lattice must be definite"
  result = typeof(L)[ L ]
  i = 1
  while (i <= length(result)) && (length(result) < max)
    # keep if not isometric, continue until the whole graph has been exhausted.
    callback = function(res, M)
      keep = all(LL -> !isisometric(LL, M)[1], vcat(res, result))
      return keep, true;
    end
    N = neighbours(result[i], p, call = callback, use_auto = use_auto, max = max - length(result))
    append!(result, N)
    i = i + 1
  end
  return result
end

function _scales_and_norms(G, p, uni)
  R = order(p)
  K = nf(R)
  e = ramification_index(p)
  aL = elem_type(K)[]
  uL = Int[]
  wL = Int[]
  sL = Int[ minimum(valuation(x, p) for x in g) for g in G ]
  for i in 1:length(G)
    # similar, but not equal to, the code for obtaining a genus symbol
    # (for the genus symbol, we consider a scaling L^(s(L_i)) in O'Meara's notation)

    GG = G[i]
    D = diagonal(GG)
    if e + sL[i] <= minimum(valuation(d, p) for d in D)
      push!(aL, elem_in_nf(uni^(e + sL[i])))
    else
      _, b = findmin([valuation(x, p) for x in D])
      push!(aL, D[b])
    end
    push!(uL, valuation(aL[i], p))
    @assert uL[i] == valuation(norm(quadratic_lattice(nf(R), identity_matrix(K, nrows(G[i])), gram_ambient_space = GG)), p)
    push!(wL, min(e + sL[i], minimum(uL[i] + quadratic_defect(d//aL[i], p) for d in D)))
  end
  return sL, aL, uL, wL 
  # scales, norm generators, norm valuations, weight valuations of a (Jordan) decomposition of L
end

function __ismaximal_norm_splitting(gram_matrices, scales, norms, p)
  #  Scales: list of valuations of scales
  #  Norms: list of generators of norms
  #  occurring in a Genus symbol of L at p, as calculated by GenusSymbol(L, p). 
  normsval = Int[valuation(norms[i], p) for i in 1:length(norms) ]
  # test if each component is either unary or binary:
  k = findfirst(i -> !(ncols(gram_matrices[i]) in [1, 2]), 1:length(gram_matrices))
  if k !== nothing
    @vprint :GenRep 2 "not maximal norm splitting: components are not all unary or binary\n";
    return false, -k, []
  end
  # test if binary components are modular:
  for i in 1:length(gram_matrices)
    if ncols(gram_matrices[i]) != 1 && valuation(det(gram_matrices[i]), p) != 2*scales[i]
      @vprint :GenRep 2 "not maximal norm splitting: at least one of the binary components is not modular\n"
      return false, -i, []
    end
  end
  # test if sL[1] \supseteq sL[2] \supseteq ... \supseteq sL[#sL]:
  for i in 1:length(scales) - 1
    if scales[i] > scales[i + 1]
      throw(Error("Your lattice is weird"))
      return fail, 0, []
    end
  end

  NU, _ = _norm_upscaled(gram_matrices, p)
  # test if nL[i] = n(L^{sL[i]}):
  fail = []
  for i in 1:length(scales)
    @assert NU[i] <= normsval[i]
    if NU[i] < normsval[i]
      @vprint :GenRep 2 "not maximal norm splitting: norm condition at $i\n"
      push!(fail, i)
    end
  end

  if length(fail) > 0
    return false, fail[1], fail
  end
  return true, 0, []
end

function _ismaximal_norm_splitting(G, p)
  sL, aL, _, _ = scales_and_norms(G, p, uniformizer(p))
  return __is_maximal_norm_splitting(G, sL, aL, p)
end

function _norm_upscaled(G, p)
  # calculate Norm(L^{scale(L_i)}), for all i.
  # for the definition of L^{a}, cf. § 82 I, p.237, in O'Meara
  #
  # G is a splitting of a LatticeModule L into Gram matrices,
  # which can e.g. be calculated by JordanDecomposition(), but need not
  # be a Jordan decomposition.
  t = length(G)
  sL = [ minimum(valuation(g[i, j], p) for j in 1:ncols(g) for i in 1:j) for g in G]
  e = ramification_index(p)
  uni = elem_in_nf(uniformizer(p))
  aL = []
  uL = []
  wL = []
  for i in 1:t
    GG = diagonal_matrix([ j < i ? uni^(2*(sL[i] - sL[j])) * G[j] : G[j] for j in 1:t])
    # the norm is 2*Scale + <ideals generated by the diagonals>, cf. § 94 O'Meara.
    D = diagonal(GG)
    # Is 2*s(L_i) eq n_i? (We always have scale \supseteq norm \supseteq 2*scale)
    # To find norm generator, pick a generator of 2*Scale or <diagonal elements>
    if e + sL[i] <= minimum(valuation(d, p) for d in D)
      # 2*scale is the bigger ideal
      push!(aL, uni^(e + sL[i]))
    else
      # diagonal elements for the bigger ideal
      _, b = findmin([valuation(x, p) for x in D])
      push!(aL, D[b])
    end
    push!(uL, valuation(aL[i], p))
  end 
 # uL: the valuations of the upscaled norms
 # aL: the generators of the upscaled norms
 return uL, aL
end 


function _make_bong_dim_2(L, p)
  # cf. Beli, Lemma 3.3
  # return a BONG of a 2-dimensional lattice.

  ismod, r = ismodular(L, p)
  @assert ismod && rank(L) == 2
  pi = uniformizer(p)
  R = order(p)
  K = nf(R)
  A = gram_matrix(ambient_space(L))
  # is the (1,1) entry a norm generator?
  if valuation(A[1, 1], p) != valuation(norm(L), p)
    # swap stuff around so that the (1,1) entry will be a norm generator
    b = 0
    for i in 1:rank(A)
      if valuation(A[i, i], p) == valuation(norm(L), p)
        b = i
        break
      end
    end

    if b != 0
      S = local_basis_matrix(L, p)
      swap_rows!(S, 1, 2)
    else
      S = local_basis_matrix(L, p)
      for j in 1:ncols(S)
        S[1, j] = S[1, j] + S[2, j]
      end
    end
    A = S * gram_matrix(ambient_space(L)) * transpose(S)
    Lold = L
    L = quadratic_lattice(K, identity_matrix(K, nrows(A)), gram_ambient_space = A)
    @assert valuation(A[1, 1], p) == valuation(norm(L), p)
  end
  n = A[1, 1]
  # Some final checks:
  disc = A[1, 1] * A[2, 2] - A[2, 1] * A[1, 2]
  val = valuation(disc, p)
  @assert iseven(val)
  @assert valuation(disc, p) == 2*r
  bong = [n, disc//n]
end

function _one_plus_power_of_p(k, V, g, ginv, p)
  # See Beli 2003, Def. 1. 
  # We expect V, g, ginv = local_multiplicative_group_modulo_squares(p)
  r = rank(V)
  F = base_ring(V)
  it = Iterators.product([collect(F) for i in 1:r]...)
  S = [ g(V(collect(v))) for v in it ]
  SS = [ s for s in S if relative_quadratic_defect(s, p) >= k ]
  return sub(V, [ginv(s) for s in SS])
end

function _intersect(_V, _W)
  V, mV = _V
  bigspace = codomain(mV)
  W, mW = _W
  I, mI = intersect(V, W)
  return sub(bigspace, [mV(mI(g)) for g in gens(I)])
end

function _sum(_V, _W)
  V, mV = _V
  W, mW = _W
  bigspace = codomain(mV)
  return sub(bigspace, append!([mV(g) for g in gens(V)], (mW(g) for g in gens(W))))
end

function beli_correction!(L, G, JJ, steps, i, j, p)
  # this is helper procedure for GoodBONG().
  # Correct the Jordan components with number i and j of L from the Jordan
  # decomposition given in G and JJ, in such a way that the new component with
  # number i has maximal norm. 
  @assert length(steps[i]) == 2
  NU = _norm_upscaled(G, p)
  if nrows(G[j]) == 2
    # assert orthogonality of the vectors in JJ[Steps[i]] and those in
    # JJ[Steps[j]], i.e. those that make up G[i] and G[j]:
    B = sub(JJ, steps[i][1]:(steps[i][1] + steps[i][2] - 1), 1:ncols(JJ))
    C = sub(JJ, 1:steps[j][2], 1:ncols(JJ))
    @assert iszero(C * gram_matrix(ambient_space(L)) * B')
  end

  K = nf(base_ring(L))

  # assert NU[i] lt Valuation(Norm(LatticeModule(G[i])), p); // otherwise, the norm condition is violated
  # assert NU[j] le Valuation(Norm(LatticeModule(G[j])), p); // "<=" must always hold, otherwise something about the lattice is broken
#  */
#
  #  We will need the original Gram matrix for re-orthogonalization:
  GI = inv(G[i])
  @assert length(steps[j]) in [1, 2]
  # if G[j] is two-dimensional, make sure that a norm generator is on the [1,1]
  # position:
  if ncols(G[j]) == 2 && valuation(G[j][1, 1], p) > valuation(G[j][2, 2], p)
    temp = JJ[steps[j][1]]
    swap_rows!(JJ, steps[j][1], steps[j][2])
    B = zero_matrix(base_ring(JJ), 2, ncols(JJ))
    for u in 1:ncols(JJ)
      B[1, u] = JJ[steps[j][1], u]
      B[2, u] = JJ[steps[j][2], u]
    end
    G[j] = B * gram_matrix(ambient_space(L)) * B'
  end

  for u in 1:ncols(JJ)
    JJ[steps[i][1], u] = JJ[steps[i][1], u] + JJ[steps[j][1], u]
  end
  # update Gram matrix for component #i:
  B = zero_matrix(base_ring(JJ), 2, ncols(JJ))
  for u in 1:ncols(JJ)
    B[1, u] = JJ[steps[i][1], u]
    B[2, u] = JJ[steps[i][2], u]
  end

  G[i] = B * gram_matrix(ambient_space(L)) * B'
  x = sub(JJ, steps[i][1]:steps[i][1], 1:ncols(JJ))
  y = sub(JJ, steps[i][2]:steps[i][2], 1:ncols(JJ))

  # Ansatz: v = JJ[Steps[j][1]] + lambda*x + mu*y
  #  
  # re-orthogonalize the first basis vector of G[j]:
  v = matrix(K, 1, 2, [-G[j][1, 1], 0]) * GI
  # G[j][1,1] is always non-zero (the lattice is definite)
  # assert integrality at p:
  @assert all(k -> valuation(v[k], p) >= 0, 1:ncols(v))
  
  # JJ[steps[j][1]] +:= v[1]*JJ[steps[i][1]] + v[2]*JJ[steps[i][2]];
  for u in 1:ncols(JJ)
    JJ[steps[j][1], u] = JJ[steps[j][1], u] + v[1] * JJ[steps[i][1],u] + v[2] * JJ[steps[i][2], u]
  end

  # if applicable, re-orthogonalize the second basis vector of G[j]:
  if ncols(G[j]) == 2
    w = matrix(K, 1, 2, [-G[j][1, 2], 0]) * GI
    # G[j][1,2] is always non-zero (or else the lattice would have been further
    # decomposed into two 1x1-lattices here)

    @assert all(k -> valuation(w[k], p) >= 0, 1:ncols(w))
    for u in 1:ncols(u)
      JJ[steps[j][1], u] = JJ[steps[j][1], u] + w[1] * JJ[steps[i][1],u] + w[2] * JJ[stepps[i][2], u]
    end
  end

  B = sub(JJ, steps[j][1]:steps[j][length(steps[j])], 1:ncols(JJ))
  G[j] = B * gram_matrix(ambient_space(L)) * B'
end
