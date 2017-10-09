################################################################################
#
#  Saturation
#
################################################################################

# TH:
# Let U = <u_1,...,u_n,z> with z a generator for Tor(U)
# For a prime p the group U/U^p is F_p-vector space of dimension
# rank(U) or rank(U) + 1 (depending on the order of z).
# if p divides N(P) - 1 = #F_P*, then F_P*/F_P*^p is a one-dimensional
# F_p-vector space. Thus the canonical map F_p-linear
#               U/U^p -> F_P*/F_P*^p
# can be described by a 1 x (rank(U)) or 1 x (rank(U) + 1) matrix over F_p,
# and can be computed by solving discrete logarithms in F_P
#
function _is_saturated(U::UnitGrpCtx, p::Int, B::Int = 2^30 - 1, proof::Bool = false)
  if proof
    error("Not yet implemented")
  end

  N = 3*unit_rank(order(U))

  @vprint :UnitGroup 1 "Computing $N prime ideals for saturation ...\n"

  primes =  _find_primes_for_saturation(order(U), p, N, B)

  m = _matrix_for_saturation(U, primes[1], p)

  for i in 2:N
    m = vcat(m, _matrix_for_saturation(U, primes[i], p))
  end

  @vprint :UnitGroup 1 "Computing kernel of p-th power map ...\n"
  (K, k) = _right_kernel(m)

  K = transpose(K)
  L = lift(K)
  T = typeof(L[1,1])

  nonzerorows = Array{Int, 1}()

  for j in 1:rows(L)
    if !iszero_row(L, j)
      push!(nonzerorows, j)
    end
  end

  if k == 0 
    return (true, zero(nf(order(U))))
  elseif k == 1 && sum(T[ L[nonzerorows[1], i]::T for i in 1:cols(L)-1]) == 0
    # Only one root, which is torsion.
    # We assume that the torsion group is the full torsion group
    return (true, zero(nf(order(U))))
  else
    for j in nonzerorows
      a = U.units[1]^(L[j, 1])
      for i in 2:length(U.units)
        a = a*U.units[i]^L[j, i]
      end

      if gcd(p, U.torsion_units_order) != 1
        a = a*elem_in_nf(U.torsion_units_gen)^L[j, length(U.units) + 1]
      end

      b = evaluate(a)

      @vprint :UnitGroup 1 "Testing/computing root ... \n"

      @vprint :UnitGroup 1 "Bitsize of coefficient $([nbits(elem_in_basis(U.order(b))[i]) for i in 1:degree(U.order)])"

      #has_root, roota = root(b, p)
      has_root, _roota = ispower(U.order(b), p)
      roota = elem_in_nf(_roota)


      if !has_root
        continue
      end

      return (false, roota)
    end
  end

  # try some random linear combination of kernel vectors

  MAX = 10

  for i in 1:MAX

    ra = rand(0:p-1, rows(K))
    v = zero_matrix(base_ring(K), 1, cols(K))
    for j in 1:cols(K)
      for l in 1:rows(K)
        v[1, j] = v[1, j] + ra[l]*K[l,j]
      end
    end

    if v == parent(v)(0)# || sum([v[1, j] for j in 1:rows(K)-1]) == 0
      continue
    end

    v = lift(v)

    a = U.units[1]^(v[1, 1])
    for j in 2:length(U.units)
      a = a*U.units[j]^v[1, j]
    end

    if gcd(p, U.torsion_units_order) != 1
      a = a*elem_in_nf(U.torsion_units_gen)^v[1, length(U.units) + 1]
    end

    b = evaluate(a)

    #has_root, roota = root(b, p)
    has_root, _roota = ispower(U.order(b), p)
    roota = elem_in_nf(_roota)


    if has_root
      return (false, roota)
    end
  end

  return (true, zero(nf(order(U))))
end

# The output will be of type
# elem_type(MatrixSpace(ResidueRing(FlintZZ, p), 1, rank(U) ( + 1))), so
# nmod_mat or fmpz_mod_mat
# THIS FUNCTION IS NOT TYPE STABLE
function _matrix_for_saturation(U::UnitGrpCtx, P::NfOrdIdl, p::Int)
  O = order(U)
  K = nf(O)
  F, mF = ResidueField(O, P)
  mK = extend(mF, K)
  g = _primitive_element(F)

  # We have to add the generator of the torsion group
  if gcd(p, U.torsion_units_order) != 1
    res = zero_matrix(ResidueRing(FlintZZ, p), 1, unit_rank(O) + 1)
  else
    res = zero_matrix(ResidueRing(FlintZZ, p), 1, unit_rank(O))
  end

  t = K()

  for i in 1:length(U.units)
    u = U.units[i]
    y = one(F)

    # P.gen_two should be P-unformizer
    #println("$(P.gen_one), $b, $(P.gen_two)")

    for b in base(u)
      t = b*anti_uniformizer(P.gen_two)^(valuation(b, P))

      #if mod(den(t), minimum(P)) == 0
      #  l = valuation(den(t), P)
      #  y = y*(mK(t*elem_in_nf(P.anti_uniformizer)^l)*mF(P.anti_uniformizer)^(-l))^u.fac[b]
      #else
        y = y*mK(t)^u.fac[b]
      #end
    end

    res[1, i] = disc_log(y, g, p)
  end

  if gcd(p, U.torsion_units_order) != 1
    res[1, unit_rank(O) + 1] = disc_log(mF(U.torsion_units_gen), g, p)
  end

  return res
end

# TH:
# This function finds n prime ideals P of O such that p divides N(P) - 1
# Moreover the prime ideals are unramified and min(P) does not divide
# the index of O in the equation order.
#
# The function loops through all prime ideals ordered by the minimum,
# starting at next_prime(st)
function _find_primes_for_saturation(O::NfOrd, p::Int, n::Int,
                                     st::Int = 0)
  res = Array{NfOrdIdl}(n)
  i = 0

  q = st
  while i < n
    q = next_prime(q)

    if mod(index(O), q) == 0 || isramified(O, q)
      continue
    end

    lp = prime_decomposition(O, q)

    j = 1

    while j <= length(lp) && i < n
      Q = lp[j]
      if mod(norm(Q[1]) - 1, p) == 0
        i = i + 1
        res[i] = Q[1]
      end
      j = j + 1
    end
  end

  return res
end

function _refine_with_saturation(c::ClassGrpCtx, u::UnitGrpCtx)
  @vprint :UnitGroup "Enlarging unit group using saturation ... \n"

  b = _validate_class_unit_group(c, u)

  p = 2

  while b > 1
    @vprint :UnitGroup 1 "Saturating at $p ... \n"

    @v_do :UnitGroup 1 pushindent()
    issat, new_unit = _is_saturated(u, p)
    @v_do :UnitGroup 1 popindent()

    while !issat
      #println("I have found a new unit: $new_unit")
      _add_dependent_unit(u, FacElem(new_unit))
      #println("$(u.tentative_regulator)")

      @v_do :UnitGroup 1 pushindent()
      b = _validate_class_unit_group(c, u)
      @v_do :UnitGroup 1 popindent()

      if b == 1
        break
      end

      @v_do :UnitGroup 1 pushindent()
      issat, new_unit = _is_saturated(u, p)
      @v_do :UnitGroup 1 popindent()
    end

    @v_do :UnitGroup 1 pushindent()
    b = _validate_class_unit_group(c, u)
    @v_do :UnitGroup 1 popindent()

    p = next_prime(p)
    if p > b
      break
    end
  end
  return b
end

