# Genus representatives for quadratic lattices,
#
# With permission ported from Magma package of Markus Kirschmer:
# http://www.math.rwth-aachen.de/~Markus.Kirschmer/magma/lat.html

add_verbosity_scope(:GenRep)
add_assertion_scope(:GenRep)

################################################################################
#
#  SpinorGeneraCtx
#
################################################################################

function SpinorGeneraCtx(L::QuadLat)
  R = base_ring(L)
  F = number_field(R)

  RCG, mRCG, Gens = _compute_ray_class_group(L)

  # 1) Map the generators into the class group to create the factor group.
  subgroupgens = FinGenAbGroupElem[_map_idele_into_class_group(mRCG, [g]) for g in Gens ]

  for g in gens(RCG)
    push!(subgroupgens, 2*g)
  end

  Q, mQ = quo(domain(mRCG), subgroupgens)

  @vprintln :GenRep 1 "Ray class group: size = $(order(RCG))"
  @vprintln :GenRep 1 """Ray class group quotient: size = $(order(Q))
  (this is the number of spinor + genera in Genus(L))"""

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

  critical_primes = _get_critical_primes(L, mRCG, inf_plc, mQ, true) # fulllist = not is_definite?
  @vprintln :GenRep 1 """good primes over $([minimum(q) for q in critical_primes])
  (together with the squares) generate the subgroup."""

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

@doc raw"""
    genus_representatives(L::QuadLat; max = inf, use_auto = true)
                                                        -> Vector{QuadLat}

Computes representatives for the isometry classes in the genus of $L$.

At most `max` representatives are returned. The use of automorphims can be
disabled by setting `use_auto = false`.
"""
function genus_representatives(L::QuadLat; max = inf, use_auto = true, use_mass = true)
  # Otherwise the isomorphism to the class group fails, cf. §102 in O'Meara.
  @req max >= 1 "Must find at least one representative"

  if rank(L) == 1
    return typeof(L)[L]
  end

  if rank(L) == 2
    if is_definite(L)
      return _genus_representatives_binary_quadratic_definite(L; max, use_auto = true, use_mass = true)
    else
      @req degree(base_ring(L)) == 1 "Binary indefinite quadratic lattices must be only over the rationals"
      return _genus_representatives_binary_quadratic_indefinite_rationals(L)
    end
  end

  if !is_definite(L)
    @vprintln :GenRep 1 "Genus representatives of indefinite lattice"
    return spinor_genera_in_genus(L, ideal_type(base_ring(L))[])
  end

  res = typeof(L)[]

  p = _smallest_norm_good_prime(L)

  spinor_genera = spinor_genera_in_genus(L, typeof(p)[p])

  if use_mass
    @vprintln :GenRep 1 "Computing mass exactly ..."
    _mass = mass(L)
    @vprintln :GenRep 1 "... $(_mass)"
  else
    _mass = -one(FlintQQ)
  end

  @vprintln :GenRep 1 "Found $(length(spinor_genera)) many spinor genera in genus"

  for LL in spinor_genera
    @hassert :GenRep 3 all(!is_isometric_with_isometry(X, LL)[1] for X in res)
    new_lat =  iterated_neighbours(LL, p; use_auto,
                                          max = max - length(res),
                                          mass = _mass//length(spinor_genera))
    append!(res, new_lat)
  end

  if max > length(res) && use_mass
    if sum(1//automorphism_group_order(LL) for LL in res; init = QQ(0)) != _mass
      error("Something very wrong")
    end
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
  Gr = gram_matrix_of_generators(L; minimal = false)

  R = base_ring(L)
  F = nf(R)

  spinornorm = zero(F)

  # The smaller the element, the better
  for d in diagonal(Gr)
    if (iszero(spinornorm) && !iszero(d)) || (!iszero(d) && abs(norm(d)) < abs(norm(spinornorm)))
      spinornorm = d
    end
  end
  if iszero(spinornorm)
    i = 1
    while iszero(Gr[1, i])
      i += 1
      if i > ncols(Gr)
        error("Lattice is degenerated")
      end
    end
    @assert !iszero(Gr[1, i])
    spinornorm = 2 * Gr[1, i]
  end

  # 2) At a place p where spinornorm does not generate norm(L_p)
  #    we add <p, spinornorm * normgenerator > to the idele

  nor = norm(L)

  differ = ideal_type(R)[]
  for p in vcat(support(nor), support(spinornorm * R))
    if valuation(nor, p) != valuation(spinornorm, p)
      push!(differ, p)
    end
  end

  idele = Tuple{ideal_type(R), elem_type(F)}[]

  for p in unique(vcat(differ, C.rayprimes))
    local _norm::elem_type(F)
    if is_dyadic(p)
      _,_,_,a = _genus_symbol_kirschmer(L, p).data
      _norm = a[1]::elem_type(F)
    else
      GS = _genus_symbol_kirschmer(L, p)
      G = GS.data
      pi = GS.x::elem_type(F)
      _norm = pi^(G[1][2]::Int)
      if G[1][1]::Int == 1 && G[1][3]::Int == -1
        k, h = residue_field(R, p)
        _norm = _norm * elem_in_nf(h\non_square(k))
      end
    end
    push!(idele, (p, spinornorm * _norm))
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
    N = only(neighbours(L, p; max = 1))
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
  lp = ideal_type(OK)[p for p in bad_primes(L; even = true) if is_dyadic(p) || !is_modular(L, p)[1]]
  limit = 20
  while true
    lq = prime_ideals_up_to(OK, limit)
    sort!(lq; by = norm)
    for q in lq
      if !(q in lp)
        return q
      end
    end
    limit = 2 * limit
    if limit > 2^8
      error("Something off")
    end
  end
end

# The spinor norm of L at p, as calculated by C. Beli for dyadic p and by M.
# Kneser for non-dyadic p.
#
# Returns a subspace of local_multiplicative_group_modulo_squares(p), and a
# boolean which is true iff the spinor norm is exactly the units
function spinor_norm(L, p)
  V, g = local_multiplicative_group_modulo_squares(p)
  R = base_ring(L)
  e = valuation(R(2), p)
  if !is_dyadic(p)
    # cf. Satz 3 in Kneser, "Klassenzahlen indefiniter quadratischer Formen in
    # drei oder mehr Veränderlichen":
    J, G, E = jordan_decomposition(L, p)
    if any(g -> ncols(g) >= 2, G)
      @vprintln :GenRep 1 """Spinor norm over $(minimum(p))
      This lattice has a 2-dimensional Jordan constituent, and p is odd. Spinor norm
      is either F^* or O_F^*(F^*)^2, i.e. we will find a vector space of dimension
      $(gens(V)) or $(ngens(V) - 1)."""
      # Which of the two is the case?
      # TODO: It is not a good idea to rely on implementation details of
      #       local_multiplicative_group_modulo_squares
      if length(unique!([e % 2 for e in E])) == 1
        return gens(V)[1:ngens(V) - 1], V, g, true
      else
        return gens(V), V, g, false
      end
    end
    # This is the obscure case where p is odd and each of its Jordan components
    # has dimension 1. In this case, the units need not be contained in the
    # Spinor norm.
    #
    # Generators of the (principal) norm ideals of the Jordan components: since
    # p is odd, the norms (and the scales) are just the dimensions of the
    # Jordan components
     normgens = AbsSimpleNumFieldElem[g[1,1] for g in G]

     twonormgens = AbsSimpleNumFieldElem[]

     for i in 1:length(normgens)
       for j in 1:length(normgens)
         push!(twonormgens, normgens[i] * normgens[j])
       end
     end

     twonormvectors = [g\(x) for x in twonormgens]

     @vprintln :GenRep "Spinor norm odd p, norm generators of the $(length(G)) Jordan components are: $(normgens), $(twonormgens) $(twonormvectors)"
    # cf. Kneser 1956, Satz 3:
    _SN, mS = sub(V, twonormvectors)
    #@assert length(rels(_SN)) == 0 # free
    SN = elem_type(V)[ mS(s) for s in gens(_SN) ]
  else
    bong = good_bong(L, p)
    @hassert :GenRep 1 is_good_bong(bong, p)
    if !has_propertyA(L, p)
      @vprintln :GenRep 1 """Spinor norm over dyadic prime:
      This lattice does not have property A. Spinor norm is either F^* or
      O_F^*(F^*)^2, i.e. we will find a vector space of dimension $(ngens(V)) or
      $(ngens(V) - 1)"""
      # Using section 7, Thm. 3 in Beli 2002, one can decide which of the two
      # cases applies. This is why we needed to compute a *good* BONG:
      for i in 1:(length(bong) - 1)
        BG, mBG = G_function(bong[i + 1]//bong[i], V, g, p)
        for bg in gens(BG)
          if mBG(bg)[ngens(V)] != 0
            # the whole group
            return gens(V), V, g, false
          end
        end
      end

      for i in 1:(length(bong) - 2)
        if valuation(bong[i], p) == valuation(bong[i + 2], p)
          @assert iszero(mod(valuation(bong[i + 1], p) - valuation(bong[i], p), 2))
          if mod(div(valuation(bong[i + 1], p) - valuation(bong[i], p), 2), 2) != mod(e, 2)
            # the whole group
            return gens(V), V, g, false
          end
        end
      end

      # If all checks have passed, the spinor norm is exactly the units:
      return gens(V)[1:(ngens(V) - 1)], V, g, true
    end
    # cf. Beli 2003, Thm. 1
    SN = elem_type(V)[]::Vector{elem_type(V)}
    for i in 2:rank(L)
      #SN = SN + G_function(bong[i]//bong[i - 1], V, g, p)
      _G, _mG = G_function(bong[i]//bong[i - 1], V, g, p)
      new_gens = append!(SN, elem_type(V)[_mG(g) for g in gens(_G)])
      _SN, mS = sub(V, new_gens)
      SN = elem_type(V)[ mS(s) for s in gens(_SN) ]
    end

    # For why we can take the Minimum in what follows here, see the remark on p. 161 in Beli 2003:
    k = findfirst(i -> mod(valuation(bong[i + 2], p) - valuation(bong[i], p), 2) == 0, 1:(rank(L) - 2))
    if k !== nothing
      alpha = minimum(div(valuation(bong[i + 2], p) - valuation(bong[i], p), 2) for i in 1:(rank(L) - 2) if mod(valuation(bong[i + 2], p) - valuation(bong[i], p), 2) == 0)
      # SN = SN + one_plus_power_of_P(alpha, V, g, P)
      _G, _mG = _one_plus_power_of_p(alpha, V, g, p)
      _SN, mS = sub(V, append!(SN, eltype(SN)[_mG(g) for g in gens(_G)]))
      #@assert length(rels(_SN)) == 0 # free
      SN = elem_type(V)[ mS(s) for s in gens(_SN) ]
    end
  end
  # Test if S is equal to SN
  S, mS = sub(V, gens(V)[1:(ngens(V) - 1)])
  #@assert length(rels(S)) == 0
  W,_ = sub(V, append!(gens(V)[1:(ngens(V) - 1)], SN))
  #@assert length(rels(W)) == 0
  if length(SN) == ngens(S) && ngens(W) == ngens(V) - 1 # this means SN + V[1:dim(V) -1] == V[1:dim(V) - 1]
    fl = true
  else
    fl = false
  end

  return SN, V, g, fl
end

# Return a good BONG of L at a dyadic prime p, as defined by C. Beli.
function good_bong(L, p)
# Any BONG obtained from a maximal norm splitting is good, cf. Corollary 4.2 in Beli.
# If a maximal norm splitting is calculated, a good BONG can be read off by joining
# together the BONGs of the 1- and 2-dimensional components.
  @req base_ring(L) == order(p) "Incompatible arguments"
  @req is_dyadic(p) "Prime must be dyadic"
  G, JJ = maximal_norm_splitting(L, p)
  K = nf(base_ring(L))
  bong = AbsSimpleNumFieldElem[]
  for i in 1:length(G)
    GG = G[i]
    if nrows(GG) == 2
      bong = append!(bong, _make_bong_dim_2(quadratic_lattice(K, identity_matrix(K, 2); gram = GG), p))
    elseif nrows(GG) == 1
      push!(bong, GG[1, 1])
    else
      error("This should not happen")
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
  @req is_dyadic(p) "Prime must be dyadic"

  R = base_ring(L)
  K = nf(R)
  e = ramification_index(p)
  uni = uniformizer(p)
  J, _G, _ = jordan_decomposition(L, p)
  # join J into one matrix of base vectors
  JJ = reduce(vcat, J)
  # join the individual Gram matrices:
  A = diagonal_matrix(_G)

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
    b, i, failset = __is_maximal_norm_splitting(G, sL, aL, p)
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
    find_j = append!(ZZRingElem[valuation(aL[k], p) for k in (i+1):length(aL)], ZZRingElem[2*(sL[i] - sL[k]) + valuation(aL[k], p) for k in 1:(i - 1)])
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
            JJ[steps[k][l], u] = JJ[steps[k][l], u] * elem_in_nf(uni)^(-sL[k])
          end
        end
        B = sub(JJ, steps[k][1]:steps[k][length(steps[k])], 1:ncols(JJ))

        @assert valuation(scale(quadratic_lattice(K, identity_matrix(K, nrows(B)); gram = B * gram_matrix(ambient_space(L)) * transpose(B))), p) == -sL[k]
      end
      # Apply case 1 to the reversed orthogonal sum of the dual lattices:

      reverse!(steps)
      # Update Gram matrices for the reversed, dualized lattice:
      for k in 1:length(G)
        B = sub(JJ, steps[k][1]:steps[k][length(steps[k])], 1:ncols(JJ))
        G[k] = B * gram_matrix(ambient_space(L)) * transpose(B)
        @assert nrows(G[k]) in [1, 2]
      end
      # Component i is now at position #aL-i+1
      @assert length(steps[length(aL) - i + 1]) == 2
      beli_correction!(L, G, JJ, steps, length(aL) - i + 1, length(aL) - j + 1, p)
      reverse!(steps)
      reverse!(G)
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
        G[k] = B * gram_matrix(ambient_space(L)) * transpose(B)
        @assert nrows(G[k]) in [1, 2]
      end
    end
  end
  # We use the `let bla = bla; ...; end` due to type stability; see the
  # JuliaLang issue 15276
  @assert all(let G = G; k -> nrows(G[k]) in [1,2]; end, 1:length(G))
  return G, JJ
end

# Returns true iff BONG is a good BONG at p, as defined by C. Beli.
function is_good_bong(bong, p)
  v = all(valuation(bong[i], p) <= valuation(bong[i + 2], p) for i in 1:(length(bong)- 2))
  return v
end

function has_propertyA(L, p)
  @assert is_dyadic(p)
  rL, sL::Vector{Int}, wL, aL = _genus_symbol_kirschmer(L, p).data
  nL = ZZRingElem[valuation(aL[i], p) for i in 1:length(aL)]
  r = maximum(rL)
  if r > 2
    @vprintln :GenRep 1 """Property A is violated over dyadic prime:
    There is a $(r)-dimensional Jordan component"""
  end

  # genus: rL, sL, wL, aL note that aL only contains valuations
  for i in 1:length(sL)
    for j in (i + 1):length(sL)
      if !((0 < nL[j] - nL[i]) && (nL[j] - nL[i] < 2*(sL[j] - sL[i])))
        @vprintln :GenRep 1 """Property A is violated over dyadic prime:
        Violated at $(i) $(j) (norm/scale valuations do not fit)"""
        return false
      end
    end
  end
  return true
end

function G_function(a, V, g, p)
# Use LocalMultiplicativeGroupModSquares to calculate in F*/(O^*)^2
# (or F^*/(F^*)^2 -- the last component of the result is the p-valuation
# mod 2, and  F^*/(F^*)^2 =  F*/(O^*)^2 \times C_2.)
#
# Also we expect V, g = local_multiplicative_group_modulo_scares(p)
#
# cf. Beli 2003, Def. 4.
  O = order(p)
  K = nf(O)
  e = valuation(order(p)(2), p)
  R = valuation(a, p)
  d = relative_quadratic_defect(-a, p)

  if !is_in_A(a, p)
    @vprintln :GenRep 2 "G_function case F"
    return N_function(-a, g, p)
  elseif valuation(-4 * a, p) == 0 && g\(K(-1//4)) == g\(a)
    @vprintln :GenRep 2 "G_function case G"
    return sub(V, gens(V)[1:ngens(V) - 1])
  elseif valuation(-4 * a, p) == 0 && is_local_square(-4 * a, p)
    @vprintln :GenRep 2 "G_function case G"
    return sub(V, gens(V)[1:ngens(V) - 1])
  elseif R > 4 * e
    @vprintln :GenRep 2 "G_function case H"
    return sub(V, [g\(a)])
  elseif 2*e < R && R <= 4 * e
    if d <= 2 * e - R//2
      @vprintln :GenRep 2 "G_function case A"
      OO = _one_plus_power_of_p(R + d - 2*e, V, g, p)
      return _intersect(N_function(-a, g, p), _sum(OO, sub(V, [g\(a)])))
    else
      @vprintln :GenRep 2 "G_function case B"
      @assert R % 2 == 0
      W, mW = _one_plus_power_of_p(div(R, 2), V, g, p)
      #@assert length(rels(W)) == 0
      return sub(V, append!([g\(a)], mW(w) for w in gens(W)))
    end
  elseif R <= 2 * e
    if d  <= e - R//2
      @vprintln :GenRep 2 "G_function case C"
      return N_function(-a, g, p)
    elseif (e - R//2 < d) && (d <= 3 * e//2 - R//4)
      @assert R % 2 == 0
      @vprintln :GenRep 2 "G_function case D"
      return _intersect(N_function(-a, g, p),
                        _one_plus_power_of_p(div(R, 2) + d - e, V, g, p))
    else
      @vprintln :GenRep 2 "G_function case E"
      # Attention! Use the floor function wherever Beli writes stuff in square
      # brackets. This is due to his citing Hsia's papers, which have this
      # convention.
      return _one_plus_power_of_p(e - floor(Int, e//2 - R//4), V, g, p)
    end
  else
    error("This should never happen")
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

function N_function(a, g, p)
  #  g, ginv is the mapping obtained by local_multiplicative_group_modulo_squares(p).
  b = g\(a)

  V = parent(b)

  q = quadratic_defect(a, p)

  # project a into F^*/(O^*)^2:

  if q isa PosInf
    # treat the squares separately:
    return sub(V, gens(V))
  end

  B = gens(V)

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
  #@assert length(rels(S)) == 0 # free
  return S, mS
end

# Map an idele into the ray class group associated to L. The parameter idele
# must be a list of tuples <p, a_p>, where p is a prime of base_ring(L), and a_p
# is an element of K^* (interpreted as an element of the completion K^*_p). The
# parameter atinfinity can be a list of tuples <v, +1 or -1>, where v is an
# element of real_places(nf(base_ring(L))). All places, finite or infinite, which
# are unspecified are interpreted as 1.}
function _map_idele_into_class_group(mRCG, idele, atinfinity::Vector{Tuple{T, Int}} = Tuple{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}, Int}[]) where {T}
  #local s::AbsSimpleNumFieldElem
  R = order(base_ring(codomain(mRCG)))
  F = nf(R)
  IP = defining_modulus(mRCG)[2]
  the_idele_inf = Int[1 for i in IP]
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
  the_idele = elem_type(F)[ one(F) for p in rayprimes ]
  for i in idele
    j = findfirst(isequal(i[1]), rayprimes)
    if j isa Int # found
      the_idele[j] = i[2]
    else
      #error("Impossible?")
      # ignore this
    end
  end
  # So, only the ideals D that are coprime to the ray lie in the codomain of mRCG and can be mapped
  #
  # The ideles we are considering here are considered to be representatives of
  # classes of ideles (modulo (F^*_S)*J^L, where F^*_S is the set of principal
  # ideles which are totally positive at the infinite places where the
  # enveloping space V of L is anisotropic, and where J^L is the set of ideles
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

  sgns = Int[ sign(s, IP[j]) * the_idele_inf[j] for j in 1:length(IP)]

  A, _exp, _log = sign_map(R, _embedding.(IP), M)
  t = x * (1 + _exp(A(Int[ sgns[j] == sign(x, IP[j]) ? 0 : 1 for j in 1:length(IP)])))
  @assert x - t in M
  @assert all(sign(t, IP[j]) == sgns[j] for j in 1:length(IP))
  #t = crt(M, IP, x, sgns)

  s = s * t

  # We use the `let bla = bla; ...; end` due to type stability; see the
  # JuliaLang issue 15276
  # Check if everything is ok.
  @hassert :GenRep 1 all(let s = s; k -> isone(quo(R, factors[k])[2](FacElem(s * the_idele[k]))); end, 1:length(the_idele))
  @hassert :GenRep 1 all(let s = s, the_idele_inf = the_idele_inf; j -> sign(s * the_idele_inf[j], IP[j]) == 1; end, 1:length(IP))
  # We first interpret it as the ideal which will actually have to be mapped:
  # i.e., we just collect the p-valuations at the noncritical places (p notin RayPrimes):

  _temp1 = [ idele[j][1] for j in 1:length(idele)]
  _temp2 = ZZRingElem[ valuation(idele[j][2], idele[j][1]) for j in 1:length(idele)]
  ide = s * R
  _to_map = FacElem(Dict(numerator(ide) => ZZRingElem(1), (denominator(ide) * R) => ZZRingElem(-1)))
  if length(_temp1) != 0
    _to_map = _to_map * FacElem(_temp1, _temp2)
  end

  _to_map = FacElem(factor_coprime(_to_map))

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

  for p in bad_primes(L; even = true)
    spinors, V, g, exactlytheunits = spinor_norm(L, p)
    # we only need to carry around those finite places where the Spinor norm is
    # not exactly the units:
    if !exactlytheunits
      @vprintln :GenRep 2 """Found a prime over $(minimum(p)) where the spinor
                             norm is not exactly the units of the order.
                               dim(spinors)=$(length(spinors)),
                               dim(LocalMultGrpModSq)=$(ngens(V))"""
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
  inf_plc = [v for v in real_places(F) if !is_isotropic(L, v)]
  # Now get the ray class group of M, inf_plc
  _C, _mC = ray_class_group(M, inf_plc, lp = Mfact)
  return _C, _mC, Gens
end

function _get_critical_primes(L, mRCG, inf_plc, mQ, full = true)
  # Set full = true to calculate one prime for every element of
  # domain(mQ), instead of just one prime for every generator.
  # This is needed for indefinite lattices.

  R = base_ring(L)
  F = nf(R)
  critical_primes = ideal_type(R)[]
  Q = codomain(mQ)

  bad = prod(bad_primes(L; even = true))

  maxnorm = 50
  goodprimes = [ p for p in prime_ideals_up_to(R, maxnorm) if is_coprime(p, bad)]
  p_ind = 1

  grp_elements_to_primes = Dict{ideal_type(R), elem_type(Q)}()

  if full
    cur_list = elem_type(Q)[id(Q)]
    while length(cur_list) < length(Q)
      while p_ind > length(goodprimes)
        maxnorm = floor(Int, maxnorm * 1.2)
        goodprimes = ideal_type(R)[ p for p in prime_ideals_up_to(R, maxnorm) if is_coprime(p, bad)]
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
  R = base_ring(L)
  bad = ideal_type(R)[ p for p in bad_primes(L) if !is_modular(L, p)[1] ]
  S, mS = sub(codomain(C.mQ), mod_out)
  n = order(codomain(C.mQ))
  gens = ideal_type(R)[]
  tmp_gens = copy(mod_out)
  R = base_ring(L)
  p = 2
  while order(S) != n
    p = next_prime(p)
    lp = ideal_type(R)[ p[1] for p in prime_decomposition(R, p) if !(p[1] in bad) ]
    for P in lp
      g = _map_idele_into_class_group(C.mR, [(P, uniformizer(P))])
      h = C.mQ(g)
      if !has_preimage_with_preimage(mS, h)[1]
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

function neighbours(L::QuadLat, p; call = stdcallback, use_auto = true, max = inf)
  R = base_ring(L)
  F = nf(R)
  @req R == order(p) "Incompatible arguments"
  @req is_prime(p) "Ideal must be prime"
  ok, rescale = is_modular(L, p)
  @req ok "The lattice must be locally modular"
  @req is_isotropic(L, p) "The lattice must be locally isotropic"
  e = valuation(R(2), p)
  @req e == 0 || valuation(norm(L), p) >= e "The lattice must be even"
  B = local_basis_matrix(L, p, type = :submodule)
  n = nrows(B)
  if F isa AbsSimpleNumField
    @assert nbits(minimum(p)) < 60
    k, h = ResidueFieldSmall(R, p)
  else
    k, h = residue_field(R, p)
  end
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
    adjust_gens = eltype(G)[solve(B, B*g; side = :left) for g in G]
    @hassert :GenRep 1 all(let form = form; g -> g * form * transpose(g) == form; end, adjust_gens)
    adjust_gens_mod_p = dense_matrix_type(k)[map_entries(hext, g) for g in adjust_gens]
    adjust_gens_mod_p = dense_matrix_type(k)[x for x in adjust_gens_mod_p if !is_diagonal(x)]
    @hassert :GenRep 1 all(let form = form; g -> g * pform * transpose(g) == pform; end, adjust_gens_mod_p)
    q = order(k)
    if length(adjust_gens_mod_p) > 0
      _LO = line_orbits(adjust_gens_mod_p)
      LO = Vector{eltype(k)}[x[1] for x in _LO]
      @vprintln :GenRep 2 "Checking $(length(LO)) representatives (instead of $(div(order(k)^n - 1, order(k) - 1)))"
    else
      @vprintln :GenRep 2 "Enumerating lines over $k of length $n"
      LO = enumerate_lines(k, n)
    end
  else
    @vprintln :GenRep 2 "Enumerating lines over $k of length $n"
    LO = enumerate_lines(k, n)
  end

  result = typeof(L)[]

  pMmat = _module_scale_ideal(p, pseudo_matrix(L))

  # TODO: This is too slow
  _dotk = let k = k; (u, v) -> (matrix(k, 1, n, u) * pform * matrix(k, n, 1, v))[1, 1]; end

  _dotF = let form = form; (u, v) -> (matrix(F, 1, n, u) * form * matrix(F, n, 1, v))[1, 1]; end

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
      bas = elem_type(k)[zero(k) for i in 1:n]
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
      u = elem_type(F)[zero(F) for i in 1:n]
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

    @hassert :GenRep 1 is_locally_isometric(LL, L, p)

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

function iterated_neighbours(L::QuadLat, p; use_auto = true, max = inf, mass = -one(FlintQQ))
  @req is_definite(L) "Lattice must be definite"
  result = typeof(L)[ L ]
  i = 1

  use_mass = mass > 0

  local found::QQFieldElem

  if mass >= 0
    found = 1//automorphism_group_order(L)
  end

  while (i <= length(result)) && (length(result) < max) && (!use_mass || found < mass)
    # keep if not isometric, continue until the whole graph has been exhausted.
    callback = function(res, M)
      keep = all(LL -> !is_isometric_with_isometry(LL, M)[1], vcat(res, result))
      return keep, true;
    end
    N = neighbours(result[i], p, call = callback, use_auto = use_auto, max = max - length(result))
    if use_mass && !isempty(N)
      found = found + sum(QQFieldElem[1//automorphism_group_order(LL) for LL in N])
      perc = Printf.@sprintf("%2.1f", Float64(found//mass) * 100)
      @vprintln :GenRep 1 "#Lattices: $(length(result)), Target mass: $mass. Found so far: $found ($perc%)"
    end
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
  sL = Int[ minimum(Union{Int, PosInf}[iszero(x) ? inf : valuation(x, p) for x in g]) for g in G ]
  for i in 1:length(G)
    # similar, but not equal to, the code for obtaining a genus symbol
    # (for the genus symbol, we consider a scaling L^(s(L_i)) in O'Meara's notation)

    GG = G[i]
    D = diagonal(GG)
    if e + sL[i] <= minimum(Union{PosInf, Int}[iszero(d) ? inf : valuation(d, p) for d in D])
      push!(aL, elem_in_nf(uni)^(e + sL[i]))
    else
      _, b = findmin([iszero(x) ? inf : valuation(x, p) for x in D])
      push!(aL, D[b])
    end
    push!(uL, valuation(aL[i], p))
    @assert uL[i] == valuation(norm(quadratic_lattice(nf(R), identity_matrix(K, nrows(G[i])), gram = GG)), p)
    push!(wL, min(e + sL[i], minimum(uL[i] + quadratic_defect(d//aL[i], p) for d in D)))
  end
  return sL, aL, uL, wL
  # scales, norm generators, norm valuations, weight valuations of a (Jordan) decomposition of L
end

function __is_maximal_norm_splitting(gram_matrices, scales, norms, p)
  #  Scales: list of valuations of scales
  #  Norms: list of generators of norms
  #  occurring in a Genus symbol of L at p, as calculated by GenusSymbol(L, p).
  normsval = Int[valuation(norms[i], p) for i in 1:length(norms) ]
  # test if each component is either unary or binary:
  k = findfirst(i -> !(ncols(gram_matrices[i]) in [1, 2]), 1:length(gram_matrices))
  if k !== nothing
    @vprintln :GenRep 2 "not maximal norm splitting: components are not all unary or binary";
    return false, -something(k), []
  end
  # test if binary components are modular:
  for i in 1:length(gram_matrices)
    if ncols(gram_matrices[i]) != 1 && valuation(det(gram_matrices[i]), p) != 2*scales[i]
      @vprintln :GenRep 2 "not maximal norm splitting: at least one of the binary components is not modular"
      return false, -i, []
    end
  end
  # test if sL[1] \supseteq sL[2] \supseteq ... \supseteq sL[#sL]:
  for i in 1:length(scales) - 1
    if scales[i] > scales[i + 1]
      error("Your lattice is weird")
    end
  end

  NU, _ = _norm_upscaled(gram_matrices, p)
  # test if nL[i] = n(L^{sL[i]}):
  fail = Int[]
  for i in 1:length(scales)
    @assert NU[i] <= normsval[i]
    if NU[i] < normsval[i]
      @vprintln :GenRep 2 "not maximal norm splitting: norm condition at $i"
      push!(fail, i)
    end
  end

  if length(fail) > 0
    return false, fail[1], fail
  end
  return true, 0, Int[]
end

function _is_maximal_norm_splitting(G, p)
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
  sL = Int[ minimum(Union{Int, PosInf}[iszero(g[i, j]) ? inf : valuation(g[i, j], p) for j in 1:ncols(g) for i in 1:j]) for g in G]
  e = ramification_index(p)
  uni = elem_in_nf(uniformizer(p))
  aL = typeof(uni)[]
  uL = ZZRingElem[]
  for i in 1:t
    GG = diagonal_matrix([ j < i ? uni^(2*(sL[i] - sL[j])) * G[j] : G[j] for j in 1:t])
    # the norm is 2*Scale + <ideals generated by the diagonals>, cf. § 94 O'Meara.
    D = diagonal(GG)
    # Is 2*s(L_i) eq n_i? (We always have scale \supseteq norm \supseteq 2*scale)
    # To find norm generator, pick a generator of 2*Scale or <diagonal elements>
    if e + sL[i] <= minimum(iszero(d) ? inf : valuation(d, p) for d in D)
      # 2*scale is the bigger ideal
      push!(aL, uni^(e + sL[i]))
    else
      # diagonal elements for the bigger ideal
      _, b = findmin([iszero(x) ? inf : valuation(x, p) for x in D])
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

  ismod, r = is_modular(L, p)
  @assert ismod && rank(L) == 2
  pi = uniformizer(p)
  R = order(p)
  K = nf(R)
  A = gram_matrix(ambient_space(L))
  # is the (1,1) entry a norm generator?
  if iszero(A[1, 1]) || (valuation(A[1, 1], p) != valuation(norm(L), p))
    # swap stuff around so that the (1,1) entry will be a norm generator
    b = 0
    for i in 1:rank(A)
      if !iszero(A[i, i]) && (valuation(A[i, i], p) == valuation(norm(L), p))
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
    L = quadratic_lattice(K, identity_matrix(K, nrows(A)), gram = A)
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

function _one_plus_power_of_p(k, V, g, p)
  # See Beli 2003, Def. 1.
  # We expect V, g = local_multiplicative_group_modulo_squares(p)
  r = ngens(V)
  it = cartesian_product_iterator([0, 1], r, inplace = false)#Iterators.product([collect(0:1) for i in 1:r]...)
  S = [ g(V(collect(v))) for v in it ]
  SS = [ s for s in S if relative_quadratic_defect(s, p) >= k ]
  return sub(V, elem_type(V)[g\(s) for s in SS])
end

function _intersect(_V, _W)
  V, mV = _V
  W, mW = _W
  return intersect(mV, mW)
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
    #B = sub(JJ, steps[i][1]:(steps[i][1] + steps[i][2] - 1), 1:ncols(JJ))
    B = zero_matrix(base_ring(JJ), 2, ncols(JJ))
    for k in 1:ncols(JJ)
      B[1, k] = JJ[steps[i][1], k]
      B[2, k] = JJ[steps[i][2], k]
    end
    C = sub(JJ, steps[j][2]:steps[j][2], 1:ncols(JJ))
    @assert iszero(C * gram_matrix(ambient_space(L)) * transpose(B))
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
    G[j] = B * gram_matrix(ambient_space(L)) * transpose(B)
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

  G[i] = B * gram_matrix(ambient_space(L)) * transpose(B)
  x = sub(JJ, steps[i][1]:steps[i][1], 1:ncols(JJ))
  y = sub(JJ, steps[i][2]:steps[i][2], 1:ncols(JJ))

  # Ansatz: v = JJ[Steps[j][1]] + lambda*x + mu*y

  # re-orthogonalize the first basis vector of G[j]:
  v = matrix(K, 1, 2, [-G[j][1, 1], 0]) * GI
  # G[j][1,1] is always non-zero (the lattice is definite)
  # assert integrality at p:
  @assert all(k -> (iszero(v[k]) ? inf : valuation(v[k], p)) >= 0, 1:ncols(v))

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
    for u in 1:ncols(JJ)
      JJ[steps[j][1], u] = JJ[steps[j][1], u] + w[1] * JJ[steps[i][1],u] + w[2] * JJ[steps[i][2], u]
    end
  end

  B = sub(JJ, steps[j][1]:steps[j][length(steps[j])], 1:ncols(JJ))
  G[j] = B * gram_matrix(ambient_space(L)) * transpose(B)
end

################################################################################
#
#  Local multiplicative modulo squares
#
################################################################################

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

domain(f::LocMultGrpModSquMap) = f.domain

codomain(f::LocMultGrpModSquMap) = f.codomain

function show(io::IO, ::MIME"text/plain", f::LocMultGrpModSquMap)
  io = pretty(io)
  println(io, "Map for local unit group modulo squares")
  println(io, Indent(), "from ", f.domain)
  println(io, "to ", Lowercase(),  f.codomain)
  print(io, Dedent())
  print(io, "at the prime ideal ")
  print(IOContext(io, :compact => true), f.p)
end

function show(io::IO, f::LocMultGrpModSquMap)
  if is_terse(io)
    print(io, "Map for local unit group modulo squares")
  else
    print(io, "Map for local unit group modulo squares at the prime ideal ")
    print(IOContext(io, :compact => true), f.p)
  end
end

function image(f::LocMultGrpModSquMap, x::FinGenAbGroupElem)
  @assert parent(x) == f.domain
  K = f.codomain
  if !f.is_dyadic
    if iszero(x.coeff[1])
      y = one(K)
    else
      y = f.e
    end
    if isone(x.coeff[2])
      y = y * f.pi
    end
    return y
  else
    S = codomain(f.mS)
    G = domain(f)
    y = elem_in_nf(f.h\(f.g(f.i\(f.mS(S(ZZRingElem[x.coeff[i] for i in 1:(ngens(G) - 1)]))))))
    if x.coeff[ngens(G)] == 1
      y = y * f.pi
    end
    return y
  end
end

function preimage(f::LocMultGrpModSquMap, y::AbsSimpleNumFieldElem)
  @assert parent(y) == f.codomain
  if !f.is_dyadic
    v = valuation(y, f.p)
    if is_square(f.hext(y//f.pi^v))[1]
      fir = 0
    else
      fir = 1
    end
    return f.domain([fir, v])
  else
    v = valuation(y, f.p)
    w = f.mS\(f.i(f.g\(f.h(_square_rep_nice(y * f.pi^v, f.p, f.piinv)))))
    G = domain(f)
    return G(push!(ZZRingElem[w.coeff[i] for i in 1:(ngens(domain(f)) - 1)], v))
  end
end

## Given a prime ideal over some number field K, this returns a vector space
## over GF(2) isomorphic to K_p^/(K_p^*)^2 and a map representing the isomorphism
##
function local_multiplicative_group_modulo_squares(p)
  K = nf(order(p))
  f = LocMultGrpModSquMap(K, p)
  return domain(f), f
end

function non_square(F::FinField)
  order(F)> 2 || error("every element in $F is a square")
  r = rand(F)
  while iszero(r) || is_square(r)[1]
    r = rand(F)
  end
  return r
end

function inv(f::Hecke.LocMultGrpModSquMap)
  return MapFromFunc(codomain(f), domain(f), x -> preimage(f, x))
end

################################################################################
#
#  Binary quadratic forms
#
################################################################################

function __colon_raw(K, a, b)
  d = degree(K)
  bb = b
  B = inv(basis_matrix(a)) #QQMatrix(basis_mat_inv(a, copy = false))
  M = zero_matrix(FlintQQ, d^2, d)
  for i = 1:d
    N = representation_matrix(bb[i])*B
    for s = 1:d
      for t = 1:d
        M[t + (i - 1)*d, s] = N[s, t]
      end
    end
  end
  M = sub(hnf(FakeFmpqMat(M), :upperright), 1:d, 1:d)
  N = inv(transpose(M))
  return N
end

function _genus_representatives_binary_quadratic_definite(L::QuadLat; max = inf, use_auto = true, use_mass = true)
  # The internal functions wants 1 in Q(K \otimes L)
  # So we rescale a bit

  V = rational_span(L)
  D = diagonal(V)
  _, i = findmin(abs.(norm.(D)))
  d = D[i]
  # Do G -> d * G
  _L = rescale(L, d)
  lat = _genus_representatives_binary_quadratic_definite_helper(_L; max = max, use_auto = use_auto, use_mass = use_mass)
  G = genus(L)
  res = typeof(L)[]
  for M in lat
    Mre = rescale(M, inv(d))
    @assert genus(Mre) == G
    push!(res, Mre)
  end
  return res
end

function _genus_representatives_binary_quadratic_definite_helper(L::QuadLat; max = inf, use_auto = true, use_mass = true)
  # The strategy is to pass to the discriminant field F (which is a CM field)
  # and use that KL \cong (F, Tr/2)
  # Then in (F, Tr/2) we use Kirschmer, Pfeuffer and Körrner.

  K = base_field(L)
  L = lattice(quadratic_space(base_field(L), gram_matrix_of_rational_span(L)),
                              pseudo_matrix(identity_matrix(K, 2), coefficient_ideals(L)))

  @assert is_definite(L)
  @assert rank(L) == 2

  #V = rational_span(_L)
  ## 0. Scale to have 1 in Q(V)
  #@show V

  #D = diagonal(V)
  #_, i = findmin(abs.(norm.(D)))
  #d = D[i]

  ## so G -> G/d

  #L = lattice(quadratic_space(base_ring(V), 1//d * gram_matrix(ambient_space(_L))), pseudo_matrix(_L))

  V = rational_span(L)

  # 1. Find the isometry with (F, Tr/2)
  @vprintln :GenRep 1 "Determining isometry with CM field ..."
  K = base_ring(V)
  d = discriminant(V)
  de = denominator(d)
  @assert !is_square(de * d)[1]
  Kt, t = polynomial_ring(K, "t", cached = false)
  F, z = number_field(t^2 - de^2 * d, "z", cached = false)
  # TODO: Use automorphism_group (once implemented for relative extensions)
  a1, a2 = automorphism_list(F)
  local sigma::morphism_type(F)
  if a1(z) == z
    sigma = a2
  else
    sigma = a1
  end

  B = basis(F)
  phi = let K = K;
    (x, y) -> K((x * sigma(y) + y * sigma(x))//2)
  end
  G = matrix(K, 2, 2, [phi(B[1], B[1]), phi(B[1], B[2]), phi(B[2], B[1]), phi(B[2], B[2])])
  W = quadratic_space(K, G)
  fl, T = is_isometric_with_isometry(V, W)
  # Note that this is an isometry of KL with W
  @assert fl
  Tinv = inv(T)

  # Compute the absolute field, since this is where we do most of the work.

  Fabs, FabstoF = absolute_simple_field(F)

  KtoFabs = restrict(inv(FabstoF), base_field(F))

  sigmaabs = hom(Fabs, Fabs, FabstoF\(sigma(FabstoF(gen(Fabs)))))

  # 2. Transpose L to lattice of F.

  pb = pseudo_basis(L)
  # KL has basis a[1] for a in pb
  # So we only need to map the Z-basis of the coefficient ideals
  image_of_first = FabstoF\(T[1, 1] * B[1] + T[1, 2] * B[2])
  image_of_second = FabstoF\(T[2, 1] * B[1] + T[2, 2] * B[2])

  #@show [phi(FabstoF(a), FabstoF(b)) for a in [image_of_first, image_of_second] for b in [image_of_first, image_of_second]]

  basisofLinFabs = elem_type(Fabs)[]

  B = absolute_basis(pb[1][2])
  for b in B
    push!(basisofLinFabs, FabstoF\(F(b)) * image_of_first)
  end

  B = absolute_basis(pb[2][2])
  for b in B
    push!(basisofLinFabs, FabstoF\(F(b)) * image_of_second)
  end

  # Let M = <basisofLinFabs>_Z, this is a lattice in Fabs and we need to compute
  # its (left/right) order. We use __colon_raw on the basis matrix for this.

  EFabs = equation_order(Fabs)

  scaled_basisofLinFabs = elem_type(EFabs)[]

  O = Order(Fabs, __colon_raw(Fabs, basisofLinFabs, basisofLinFabs))

  z = zero_matrix(K, degree(O), degree(F))
  for i in 1:degree(O)
    elem_to_mat_row!(z, i, FabstoF(elem_in_nf(basis(O)[i])))
  end
  pm = pseudo_hnf(pseudo_matrix(z), :lowerleft)
  i = 1
  while is_zero_row(pm.matrix, i)
    i += 1
  end
  pm = sub(pm, i:nrows(pm), 1:ncols(pm))

  OinF = Order(F, pm)

  LinFabs = fractional_ideal(O, basisofLinFabs)

  # O is the ring of multipliers/right oder of M
  # Now we compute CL_F/{ambiguous ideals of O_F with respect to F/K}

  @vprintln :GenRep 1 "Compute representatives modulo ambiguous ideal classes ..."
  OFabs = maximal_order(O)
  amb_ideals = _ambigous_ideals_quotient_basis(OFabs, F, KtoFabs, FabstoF)
  @assert all(sigmaabs(I) == I for I in amb_ideals)
  OK = maximal_order(K)
  CK, mCK = class_group(OK)
  ideals_from_K = ideal_type(OFabs)[ KtoFabs(mCK(c)) for c in gens(CK)]
  CF, mCF = class_group(OFabs)
  Q, mQ = quo(CF, append!(elem_type(CF)[mCF\I for I in amb_ideals], elem_type(CF)[mCF\I for I in ideals_from_K]))
  repr = ideal_type(OFabs)[mCF(mQ\q) for q in Q]

  # There is a formula for the number of ambiguous ideal classes, this checks this:
  # UK, mUK = unit_group(OK)
  # UFabs, mUFabs = unit_group(OFabs)
  #@show order(quo(UFabs, append!([ mUFabs\OFabs(KtoFabs(elem_in_nf(mUK(u)))) for u in gens(UK) ], [mUFabs\OFabs(torsion_units_generator(Fabs))]))[1])
  #@show order(CF)
  #@show order(CK)
  #@show length(support(discriminant(maximal_order(F))))

  # repr are representatives for CL_F/{ambiguous ideals of O_F with respect to F/K}
  # This is isomorphic to gen(OFabs)/cls+(OFabs) via a -> b = a/\sigma(a).
  # But I also want to compute x = (x_p)_p with b_p = x_p O_p and
  # x_p \in F_p^1
  #
  # This is done in _translate_ideal
  #
  # _intersect_lattice_down computes a preimage under gen(O) -> gen(CL_F)
  #
  # The map gen(O) -> gen(CL_F) is not injective, but we can compute a set containing
  # representatives of the kernel elements.

  OF = maximal_order(F)
  repr_in_OF = ideal_type(OF)[ reduce(+, (OF(FabstoF(elem_in_nf(b))) * OF for b in basis(repr[i])), init = OF(0) * OF) for i in 1:length(repr)]

  c = conductor(O, OFabs) * OFabs
  _xps = Vector{elem_type(F)}[]
  _ps = ideal_type(OK)[]
  @vprintln :GenRep 1 "Computing local units ..."
  for (p, _) in factor(minimum(image(FabstoF, c)))
    lQ = prime_decomposition(OF, p)
    lQ = [ (preimage(FabstoF, Q), e) for (Q, e) in lQ ]
    cppart = reduce(*, (Q^valuation(c, Q) for (Q, _) in lQ), init = 1 * OFabs)
    Rq, mq = quo(OFabs, cppart)
    Mu, f = multiplicative_group(Rq)
    elts = elem_type(F)[ FabstoF(elem_in_nf(mq\(f(m)))) for m in Mu]
    if length(elts) > 1
      push!(_ps, p)
      push!(_xps, elts)
    end
  end

  kernel_rep = fractional_ideal_type(O)[]

  if length(_xps) > 0
    IT = Iterators.product(_xps...)
    @vprintln :GenRep 1 "There are $(length(IT)) potential kernel elements."

    for it in IT
      LL = _intersect_lattice_down(collect(it)::Vector{elem_type(F)}, _ps, OinF)
      LLinabs = fractional_ideal(O, [FabstoF\(b) for b in absolute_basis(LL)])
      push!(kernel_rep, LLinabs)
    end
  end

  almost_res = fractional_ideal_type(O)[]

  index_divs = support(QQFieldElem(index(O, OFabs)))

  for i in 1:length(repr_in_OF)
    I = repr_in_OF[i]
    Iabs = repr[i]
    N, xps, ps = _translate_ideal(I, Iabs, FabstoF, sigma, sigmaabs)
    @assert norm(N) == 1 * OK
    M = _intersect_lattice_down(xps, ps, OinF)

    Minabs = fractional_ideal(O, [FabstoF\(b) for b in absolute_basis(M)])
    if length(kernel_rep) > 0
      for K in kernel_rep
        push!(almost_res, K * Minabs * LinFabs)
      end
    else
      push!(almost_res, Minabs * LinFabs)
    end
  end

  @vprintln :GenRep 1 "Now sieving the $(length(almost_res)) many candidates ..."
  # At the end we have to translate this relative ideals again and then back to
  # V. The things we want have the underscore _, but for assertion purposes we
  # do both.

  gram_ambient_space = gram_matrix(V)

  V = ambient_space(L)

  G = genus(L)

  res = typeof(L)[]

  cur_mass = zero(QQFieldElem)

  if use_mass
    _mass = mass(L)
    @vprintln :GenRep 1 "Using mass, which is $(_mass)"
  else
    _mass = one(QQFieldElem)
    @vprintln :GenRep 1 "Not using mass"
  end

  for N in almost_res
    generators = []
    for b in basis(N)
      binF = FabstoF(b)
      push!(generators, [Tinv[1, 1] * coeff(binF, 0) + Tinv[2, 1] * coeff(binF, 1),
                         Tinv[1, 2] * coeff(binF, 0) + Tinv[2, 2] * coeff(binF, 1)])
    end

    z = zero_matrix(K, length(generators), dim(V))
    for i in 1:length(generators)
      for j in 1:ncols(gram_ambient_space)
        z[i, j] = generators[i][j]
      end
    end
    pm = pseudo_hnf(pseudo_matrix(z), :lowerleft)
    i = 1
    while is_zero_row(pm.matrix, i)
      i += 1
    end
    pm = sub(pm, i:nrows(pm), 1:ncols(pm))

    _pm = pseudo_matrix(matrix(pm), coefficient_ideals(pm))

    _new_cand = lattice(V, pm)

    if genus(_new_cand) != G
      continue
    end

    if any(T -> is_isometric_with_isometry(T, _new_cand)[1], res)
      continue
    else
      push!(res, _new_cand)
      if length(res) >= max
        break
      end
      if use_mass
        cur_mass += QQFieldElem(1, automorphism_group_order(_new_cand))
        if cur_mass > _mass
          error("Something very wrong in genus_representatives (mass mismatch")
        end
        if cur_mass == _mass
          break
        end
      end
    end
  end

  if max < inf && use_mass
    @assert _mass == cur_mass
  end

  return res
end

function _translate_ideal(I, Iabs, FtoFabs, sigma, sigmaabs)
  O = order(I)
  crit_primes = support(minimum(I))
  F = nf(O)
  xps = elem_type(F)[]
  sigmaI = sum(ideal(order(I), order(I)(FtoFabs(elem_in_nf(x)))) for x in basis(sigmaabs(Iabs)))
  M = I * inv(sigmaI)
  for p in crit_primes
    lQ = prime_decomposition(O, p)
    lQ_ = ideal_type(O)[ Q for (Q, _) in lQ]
    pvals = Int[]
    for Q in lQ_
      push!(pvals, valuation(I, Q))
    end

    zp = approximate(pvals, lQ_)
    xp = zp//sigma(zp)
    @assert _padic_index(I, zp * O, p) == (0, 0)
    @assert _padic_index(M, xp * O, p) == (0, 0)
    push!(xps, xp)
  end
  return M, xps, crit_primes
end

function _fractional_ideal_from_base_ring_generators(OE, v)
  # v are elements of the field
  return fractional_ideal(OE, basis_matrix(v) * basis_mat_inv(OE))
end

function _intersect(I::RelNumFieldOrderFractionalIdeal, J::RelNumFieldOrderFractionalIdeal)
  pm = _intersect_modules(basis_pmatrix(I), basis_pmatrix(J))
  return fractional_ideal(order(I), pm)
end

function _intersect_lattice_down_contained(xps, _ps, Lambda)
  _ps_orig = deepcopy(_ps)
  xps_orig = deepcopy(xps)
  if length(_ps) == 0
    return one(nf(Lambda)) * Lambda
  end
  for x in xps
    @assert x in Lambda
  end

  LL = nf(Lambda)(1) * Lambda

  for i in 1:length(xps)
    I = xps[i] * Lambda
    n = norm(I)
    for (p, e) in factor(n)
      if p == _ps[i]
        continue
      end
      if e > 0
        I = inv(p)^(e) * I
      end
    end
    LL = _intersect(LL, I)
  end

  for i in 1:length(xps)
    @assert _padic_index(xps[i] * Lambda, LL, _ps[i]) == (0, 0)
    @assert _padic_index(LL, xps[i] * Lambda, _ps[i]) == (0, 0)
  end

  for q in support(norm(LL))
    if !(q in _ps)
      @assert _padic_index(LL, d * Lambda, q) == (0, 0)
    end
  end

  return LL
end

# Given (x_p)_p, find a fractional ideal I such that I_p = x_p Lambda_p
# for all p and I_q = Lambda_q for all other prime ideals.
#
# The idea is to change Jp = x_p such that (Jp)_p \subseteq Lambda_p
# and Lambda_q \subseteq (Jp)_q for q != p. Then we can just intersect
# the Jp with Lambda.
#
# We first reduce to the case x_p in Lambda for all p by multiplying
# with a common denominator.
function _intersect_lattice_down(xps, _ps, Lambda)
  _ps_orig = copy(_ps)
  xps_orig = copy(xps)

  if length(_ps) == 0
    return one(nf(Lambda)) * Lambda
  end
  d = lcm([denominator(x, Lambda) for x in xps])

  for x in xps
    @assert d*x in Lambda
  end

  _xps = [d * x for x in xps]
  _ps = copy(_ps)

  for p in support(norm(Lambda(d)) * base_ring(Lambda))
    if !(p in _ps)
      push!(_ps, p)
      push!(_xps, nf(Lambda)(d))
    end
  end
  LL = _intersect_lattice_down_contained(_xps, _ps, Lambda)
  pm = deepcopy(basis_pmatrix(LL))
  pm.matrix = divexact(pm.matrix, base_field(nf(Lambda))(d))
  LLL = fractional_ideal(Lambda, pm)

  for q in support(norm(LLL))
    if !(q in _ps)
    end
  end

  for i in 1:length(xps)
    @assert _padic_index(xps_orig[i] * Lambda, LLL, _ps_orig[i]) == (0, 0)
    @assert _padic_index(LLL, xps_orig[i] * Lambda, _ps_orig[i]) == (0, 0)
  end

  for q in support(norm(numerator(LLL)))
    if !(q in _ps_orig)
      @assert _padic_index(LLL, Lambda, q) == (0, 0)
    end
  end

  for q in support(denominator(LLL) * base_ring(Lambda))
    if !(q in _ps_orig)
      @assert _padic_index(LLL, Lambda, q) == (0, 0)
    end
  end

  return LLL
end

function _fractional_ideal_from_base_ring_generators(OE, v, id)
  # v are elements of the field
  return fractional_ideal(OE, pseudo_matrix(basis_matrix(v) * basis_mat_inv(OE), id))
end

function absolute_norm(A::Hecke.AlgAssRelOrdIdl)
  return absolute_norm(norm(A))
end

function absolute_norm(A::Hecke.AlgAssAbsOrdIdl)
  return norm(A)
end

function absolute_norm(A::AbsNumFieldOrderFractionalIdeal)
  return norm(A)
end

function *(a::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem}, b::AlgAssRelOrdIdl{AbsSimpleNumFieldElem,Hecke.AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},StructureConstantAlgebra{AbsSimpleNumFieldElem}})
  pm = basis_pmatrix(b)
  pmnew = pseudo_matrix(matrix(pm), map(z -> a * z, coefficient_ideals(pm)))
  return ideal(algebra(order(b)), pmnew)
end

function _padic_index(N, M, p)
  Npb = pseudo_basis(N)
  Mpb = pseudo_basis(M)
  BN = basis_matrix(N)
  BM = basis_matrix(M)
  T = BN * inv(BM)
  n = nrows(BN)
  mini = 0
  for i in 1:n
    for j in 1:n
      if !(T[i, j] == 0)
           mini = min(mini, valuation(T[i, j], p) + valuation(Npb[i][2], p) - valuation(Mpb[i][2], p))
      end
    end
  end
  TT = deepcopy(T)
  pi = elem_in_nf(uniformizer(p))
  for i in 1:n
    for j in 1:n
      TT[i, j] = TT[i, j] * pi^(valuation(Npb[i][2], p) - valuation(Mpb[i][2], p))
    end
  end

  dM = det(basis_pmatrix(M))
  dN = det(basis_pmatrix(N))
  d = dN * inv(dM)
  @assert valuation(d, p) == valuation(det(TT), p)
  return mini, valuation(d, p)
end


function _ambigous_ideals_quotient_basis(OFabs, F, KtoFabs, FabstoF)
  # Given a maximal order OF of an absolute field and K -> F such that F/K is normal, return
  # a basis for {ambiguous ideals of OF with respect to Gal(F/K)}/{ideals of OK}
  res = ideal_type(OFabs)[]
  OF = maximal_order(F)
  dis = discriminant(OF)
  for (p, _) in factor(dis)
    lp = prime_decomposition(maximal_order(F), p)
    c = length(lp)
    @assert length(lp) == 1 && lp[1][2] == 2
    #@show length(c)
    lpabs = prime_decomposition(OFabs, minimum(p))
    phip = 1 * OFabs
    phipp = lp[1][1]
    cc = 0
    for (P, _) in lpabs
      pi = FabstoF(elem_in_nf(p_uniformizer(P)))
      for (Q, _) in lp
        v = valuation(pi, Q)
        @assert 0 <= v <= 1
        if v == 1
          cc += 1
          phip = phip * P
          break
        end
      end
    end
    @assert c == cc
    @assert norm(phip) == absolute_norm(phipp)
    push!(res, phip)
  end
  #@show length(res)
  return res
end

################################################################################
#
#  Indefinite binary case over number fields
#
################################################################################

# TODO: unfinished & to be completed
function _genus_representatives_binary_quadratic_indefinite(_L::QuadLat)
  @assert !is_definite(_L)
  @assert rank(_L) == 2

  V = ambient_space(_L)
  # 0. Scale to have 1 in Q(V)

  D = diagonal(V)
  _, i = findmin(abs.(norm.(D)))
  d = D[i]

  # so G -> G/d

  L = lattice(quadratic_space(base_ring(V), 1//d * gram_matrix(ambient_space(_L))), pseudo_matrix(_L))

  V = rational_span(L)

  # 1. Find the isometry with (K + K, Tr/2)
  @vprintln :GenRep 1 "Determining isometry with CM field ..."
  K = base_ring(V)

  mult_tb = Array{elem_type(K), 3}(undef, 2, 2, 2)
  for i in 1:2
    for j in 1:2
      if i != j
        mult_tb[i, j, :] = elem_type(K)[zero(K), zero(K)]
      else
        z = elem_type(K)[zero(K), zero(K)]
        z[i] = one(K)
        mult_tb[i, j, :] = z
      end
    end
  end

  A = StructureConstantAlgebra(K, mult_tb)
  B = basis(A)
  sigma(a) = A([a.coeffs[2], a.coeffs[1]])
  inv2 = inv(A(2))
  phi(x, y) = (x * sigma(y) + y * sigma(x)) * inv2
  G = matrix(K, 2, 2, [phi(B[1], B[1]), phi(B[1], B[2]), phi(B[2], B[1]), phi(B[2], B[2])])
  W = quadratic_space(K, G)
  fl, T = is_isometric_with_isometry(V, W)
  @assert fl

  Tinv = inv(T)

  # 2. Transport L to lattice of A.

  pb = pseudo_basis(L)
  # KL has basis a[1] for a in pb
  # So we only need to map the Z-basis of the coefficient ideals
  image_of_first = (T[1, 1] * B[1] + T[1, 2] * B[2])
  image_of_second = (T[2, 1] * B[1] + T[2, 2] * B[2])

  basisofLinA = elem_type(A)[]

  B = absolute_basis(pb[1][2])
  for b in B
    push!(basisofLinA, b * image_of_first)
  end

  B = absolute_basis(pb[2][2])
  for b in B
    push!(basisofLinA, b * image_of_second)
  end

  LinA = ideal_from_lattice_gens(A, basisofLinA)

  Lambda = right_order(LinA)

  OK = maximal_order(K)
  C, mC = class_group(OK)
  cur_class = elem_type(C)[]
  ideal_repr = ideal_type(OK)[]
  p_and_xps = Vector{Tuple{ideal_type(OK), elem_type(A)}}[]
  # We try to find prime ideal representatives
  push!(cur_class, id(C))
  push!(ideal_repr, 1 * OK)
  push!(p_and_xps, Tuple{ideal_type(OK), elem_type(A)}[])
  for p in PrimeIdealsSet(OK, 1, -1)
    if length(cur_class) == order(C)
      break
    end
    c = mC\p
    if !(c in cur_class)
      push!(cur_class, c)
      push!(ideal_repr, p)
      pi = elem_in_nf(uniformizer(p))
      push!(p_and_xps, [(p, A([pi, inv(pi)]))])
    end
  end

  # I have p_and_xps
  _intersect_lattice_down([ p[2] for p in p_and_xps[1]], [ p[1] for p in p_and_xps[1]] , Lambda)

  return Lambda, LinA
end

################################################################################
#
#  Indefinite binary quadratic over the integers
#
################################################################################

# case that base_ring(L) is rationals_as_number_field()
function _genus_representatives_binary_quadratic_indefinite_rationals(L::QuadLat)
  @req degree(base_ring(L)) == 1 "Number field must be of degree 1"
  @req rank(L) == 2 "Lattice must be of rank 2"
  K = nf(base_ring(L))
  f, e = _lattice_to_binary_quadratic_form(L) # e is the scaling factor
  d = discriminant(f)
  @assert d > 0
  cls = _equivalence_classes_binary_quadratic_indefinite(d, proper = false, primitive = false)
  res = typeof(f)[f]
  K, = rationals_as_number_field()
  G = genus(_binary_quadratic_form_to_lattice(f, K, e))
  lat = typeof(L)[]

  for g in cls
    LL = _binary_quadratic_form_to_lattice(g, K, e)
    GG = genus(LL)
    if GG == G
      push!(lat, LL)
    end
  end
  return lat
end

function _lattice_to_binary_quadratic_form(L::QuadLat)
  M = absolute_basis_matrix(L) # This corresponds to a basis of L
  @assert nrows(M) == 2 && ncols(M) == 2
  G = gram_matrix(ambient_space(L), M)
  GG = change_base_ring(FlintQQ, G)
  d = denominator(GG)
  f = binary_quadratic_form(FlintZZ(d * GG[1, 1]), FlintZZ(2 * d * GG[1, 2]), FlintZZ(d * GG[2, 2]))
  return f, d
end

function _equivalence_classes_binary_quadratic_indefinite(d::ZZRingElem; proper::Bool = false, primitive::Bool = true)
  if is_square(d)[1]
    b = sqrt(d)
    c = ZZRingElem(0)
    res = QuadBin{ZZRingElem}[]
    for a in (round(ZZRingElem, -b//2, RoundDown) + 1):(round(ZZRingElem, b//2, RoundDown))
      if !primitive || isone(gcd(a, b, c))
        f = binary_quadratic_form(a, b, c)
        if proper || all(h -> !is_equivalent(h, f, proper = false), res)
          push!(res, f)
        end
      end
    end
    return res
  end
  if primitive
    return _equivalence_classes_binary_quadratic_indefinite_primitive(d, proper = proper)
  else
    res = QuadBin{ZZRingElem}[]
    for n in Divisors(d, units = false, power = 2) # n^2 | d
      # There are no forms with discriminant mod 4 equal to 2, 3
      if mod(divexact(d, n^2), 4) in [2, 3]
        continue
      end
      cls = _equivalence_classes_binary_quadratic_indefinite_primitive(divexact(d, n^2), proper = proper)
      for f in cls
        push!(res, n*f)
      end
    end
    return res
  end
end

function _equivalence_classes_binary_quadratic_indefinite_primitive(d::ZZRingElem; proper::Bool = false)
  @assert d > 0
  Qx = Hecke.Globals.Qx
  x = gen(Qx)
  ff = x^2 - d * x + (d^2 - d)//4
  @assert isone(denominator(ff))
  K, a = number_field(ff, "a", cached = false) # a is (d + \sqrt(d))//2
  O = equation_order(K)
  C, _dlog, _exp = narrow_picard_group(O)
  res = QuadBin{ZZRingElem}[]
  # C gives me all proper classes of definite forms
  # So if proper = true, we don't have to do anything
  # and if proper = false, we have to sieve using is_equivalent
  for c in C
    I::AbsSimpleNumFieldOrderFractionalIdeal = _exp(c)
    J = numerator(I)
    f = _ideal_to_form(J, d)
    if proper || all(h -> !is_equivalent(h, f, proper = false), res)
      push!(res, reduction(f))
    end
  end
  return res
end

function _binary_quadratic_form_to_lattice(f::QuadBin{ZZRingElem}, K, e::ZZRingElem = ZZRingElem(1))
  a = f[1]
  b = f[2]
  c = f[3]
  G = matrix(K, 2, 2, [a//(e), b//(2*e), b//(2*e), c//e])
  L = lattice(quadratic_space(K, G), identity_matrix(K, 2))
end

function _form_to_ideal(f::QuadBin{ZZRingElem}, O, a)
  # a must be d + sqrt(d)//2 and O = ZZ[a]
  deltasqrt = O(2 * a - discriminant(f))
  # deltasqrt^2 == delta
  @assert deltasqrt^2 == discriminant(f)
  _a = f[1]
  _b = f[2]
  _c = f[3]
  return ideal(O, [O(_a), divexact(O(-_b + deltasqrt), 2)])
end

# This is from Kani
function _ideal_to_form(I::AbsNumFieldOrderIdeal, delta)
  # first make primitive
  M = _hnf(basis_matrix(I), :lowerleft)
  g = reduce(gcd, [M[1, 1], M[1, 2], M[2, 2]])
  M = divexact(M, g)
  B = M[2, 1]
  C = M[2, 2]
  a = M[1, 1]
  @assert isone(C)
  b = -(2 * B + delta)
  c = -divexact(divexact(delta - b^2, 4), a)
  @assert -4 * a * c == delta - b^2
  f = binary_quadratic_form(a, b, c)
  @assert discriminant(f) == delta
  return f
end

function primitive_form(g::QuadBin{ZZRingElem})
  d = content(g)
  if isone(d)
    return g
  end
  a = divexact(g.a, d)
  b = divexact(g.b, d)
  c = divexact(g.c, d)
  return binary_quadratic_form(ZZ,a,b,c)
end

function automorphism_group_generators(g::QuadBin{ZZRingElem})
  gens = dense_matrix_type(FlintZZ)[]
  g = primitive_form(g)
  d = discriminant(g)
  @assert d > 0
  if is_square(d)
    g = primitive_form(g)
    gred, t = reduction_with_transformation(g)
    push!(gens, matrix(FlintZZ, 2, 2, [-1, 0, 0, -1]))
    a = gred.a
    b = gred.b
    c = gred.c
    @assert a == 0 || c == 0
    if a == c == 0
      push!(gens, t * matrix(FlintZZ, 2, 2, [0, 1, 1, 0]) * inv(t))
    elseif a == 0 && c != 0
      a = gred.c
      c = gred.a
      t = t * matrix(ZZ, 2, 2, [0, 1, 1, 0])
    elseif a != 0 && c ==0 && b % (2*a) == 0
      n = b//(2*a)
      t = t * matrix(ZZ, 2, 2, [1, -n, 0, 1])
      push!(gens, t * matrix(FlintZZ, 2, 2, [1,0,0,-1]) * inv(t) )
    end
    for T in gens
      @assert _action(g, T) == g
    end
    return gens
  end
  Qx = Hecke.Globals.Qx
  x = gen(Qx)
  f = x^2 - d * x + (d^2 - d)//4
  @assert isone(denominator(f))
  K, _a = number_field(f, "a", cached = false) # a is (d + \sqrt(d))//2
  O = equation_order(K)
  deltasqrt = O(2 * _a - discriminant(f))
  @assert deltasqrt^2 == d

  U, mU = unit_group(O)
  A = abelian_group([2])
  h = hom(U, A, [norm(mU(U[1])) == -1 ? A([1]) : A([0]), norm(mU(U[2])) == -1 ? A([1]) : A([0])])
  k, mk = kernel(h, false)
  @assert ngens(k) == 2
  norm_one_gens = elem_type(O)[mU((mk(k[1]))), mU((mk(k[2])))]
  # We need to write the elements in the basis 1//2, deltasqrt//2
  # O has basis 1, (d + sqrt(d)//2)
  for i in 1:2
    a, b = coordinates(norm_one_gens[i])
    _x, _y = (2*a + b * d, b)
    @assert norm_one_gens[i] == divexact(_x + _y * deltasqrt, 2)
    @assert iseven(_x + g.b * _y)
    @assert iseven(_x + d * _y)
    T = zero_matrix(FlintZZ, 2, 2)
    T[1, 1] = divexact(_x + _y * g.b, 2)
    T[1, 2] = g.c * _y
    T[2, 1] = -g.a * _y
    T[2, 2] = divexact(_x - _y * g.b, 2)
    push!(gens, T)
  end
  for T in gens
    @assert _action(g, T) == g
  end
  # Now test if g is ambiguous or not
  gg = binary_quadratic_form(g.a, -g.b, g.c)
  fl = is_equivalent(g, gg, proper = true)
  gorig = g
  if fl
    g, t = reduction_with_transformation(g)
    # We compute the "cycle"? of g and find
    # a form of the form [a, 0, c] or [a, a, 0]
    # then we are done, since for those forms
    # we know an improper equivalence

    if g.a < 0
      # we have to make sure that g.a > 0
      g = binary_quadratic_form(g.c, g.b, g.a)
      t = t * matrix(ZZ, 2, 2, [0, 1, 1, 0])
    end
    #@assert det(T) == 1
    @assert g.a > 0
    k = 0
    sgn = 1
    T = identity_matrix(ZZ, 2)
    while true
      k += 1
      #@show g
      a = g.a
      b = g.b
      c = g.c

      #@show (iszero(b) || divides(b, c)[1])

      #good = false

      #if (iszero(b) || divides(b, c)[1])
      #  if det(T) == -1
      #    S = matrix(ZZ, 2, 2, [0, 1, 1, 0])
      #  else
      #    S = matrix(ZZ, 2, 2, [0, -1, 1, 0])
      #  end
      #  T = T * S
      #  gg = _action(gg, S)
      #  @show gg
      #  a = gg.a
      #  b = gg.b
      #  c = gg.c
      #  @show "asdsd"
      #end

      if ((iszero(b) || divides(b, a)[1]))
        # OK, so gg = g * T, det(T) = 1
        # and gg has the form I am looking for
        fl, n = divides(b, 2 * a)
        if fl
          # Turn this into [a, 0, c]
          S = matrix(ZZ, 2, 2, [1, -n, 0, 1])
          SS = matrix(ZZ, 2, 2, [1, 0, 0, -1])
          # g * T * S * SS = g * T * S
          improperT = t * T * S * SS * inv(S) * inv(T) * inv(t)
          @assert _action(gorig, improperT) == gorig
          @assert det(improperT) == -1
          push!(gens, improperT)
        else
          # Turn this into [a, a, c]
          n, r = divrem(b, 2 * a)
          @assert r == a
          S = matrix(ZZ, 2, 2, [1, -n, 0, 1])
          SS = matrix(ZZ, 2, 2, [1, 1, 0, -1])
          # OK, so ggg = g * T * S is invariant under SS, which is
          # improper
          # g * T * S * SS = g * T * S
          improperT = t * T * S * SS * inv(S) * inv(T) * inv(t)
          @assert _action(gorig, improperT) == gorig
          @assert det(improperT) == -1
          push!(gens, improperT)
        end
        break
      end

      s = floor(ZZRingElem, (b + isqrt(discriminant(g)))//(2 * abs(c)))
      g = binary_quadratic_form(abs(c), -b + 2*s*abs(c), -(a + b * s + c * s* s))

      T = T * matrix(ZZ, 2, 2, [0, 1, 1, s])
    end
  end

  for T in gens
    @assert _action(gorig, T) == gorig
  end

  return gens
end
