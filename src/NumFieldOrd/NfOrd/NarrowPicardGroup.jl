#mutable struct MapNarrowPicardGrp{S, T} <: Map{S, T, HeckeMap, MapNarrowPicardGrp}
#  header::MapHeader{S, T}
#
#  picard_group # picard group map of order
#  right_transform::ZZMatrix
#  betas # Vector of factorized algebra elements
#  gammas # the same type as betas
#
#  function MapNarrowPicardGrp{S, T}() where {S, T}
#    return new{S, T}()
#  end
#end
#
#function show(io::IO, mP::MapNarrowPicardGrp)
#  @show_name(io, mP)
#  println(io, "Narrow Picard group map of ")
#  show(IOContext(io, :compact => true), codomain(mP))
#end

################################################################################
#
#  High level functions
#
################################################################################

@doc raw"""
      picard_group(O::AbsSimpleNumFieldOrder) -> FinGenAbGroup, MapClassGrp

Returns the Picard group of O and a map from the group in the set of
(invertible) ideals of O.
"""
function narrow_picard_group(O::AbsSimpleNumFieldOrder)
  U, mU = unit_group(O)

  # determine the totally positive units

  Q, Q_to_elem, elem_to_Q = _principal_ideals_modulo_totally_positive_principal_ideals(O, mU)

  C, mC = picard_group(O)

  @assert is_snf(C)

  new_ngens = ngens(Q) + ngens(C)

  R = zero_matrix(FlintZZ, new_ngens, new_ngens)
  for i in 1:ngens(Q)
    R[i, i] = 2
  end

  idealgens = ideal_type(O)[]

  Crels = rels(C)

  for i in 1:ngens(C)
    I0 = mC(C[i])
    I = I0^(order(C[i]))
    push!(idealgens, I0)
    # I is principal
    fl, a = is_principal_with_data(I)
    @assert fl
    q = elem_to_Q(elem_in_nf(a))
    R[[ngens(Q) + i],:] = hcat(-q.coeff, Crels[i:i, :])
  end


  B = abelian_group(R)
  BS, BStoB = snf(B)
  BtoBS = inv(BStoB)

  # If given an element of B, I have to write it in the
  # standard generators [1,...,0], [0,...,1]

  im_Q_gens = elem_type(B)[]
  for i in 1:ngens(Q)
    v = ZZRingElem[0 for j in 1:ngens(B)]
    v[i] = 1
    push!(im_Q_gens, B(v))
  end

  Q_to_B = hom(Q, B, im_Q_gens)

  disclog = function(J)
    d = denominator(J)
    JJ = numerator(J)
    c = mC\(JJ)
    for i in 1:ngens(C)
      JJ = JJ * idealgens[i]^(-c.coeff[i] + order(C[i]))
    end
    fl, b = is_principal_with_data(JJ)
    @assert fl
    @assert b * O == JJ
    q = elem_to_Q(elem_in_nf(b)//d)
    return BtoBS(B(hcat(-q.coeff, c.coeff)))
  end

  _exp = function(el)
    @assert parent(el) == BS
    _el = BStoB(el)
    _elC = C([_el.coeff[1, ngens(Q) + i] for i in 1:ngens(C)])
    JJ = mC(_elC)
    _ell = _el - BStoB(disclog(fractional_ideal(JJ)))
    fl, b = has_preimage_with_preimage(Q_to_B, _ell)
    @assert fl
    J = Q_to_elem(b) * mC(_elC)
    return J
  end

   # A test

   _Q, = units_modulo_totally_positive_units(O)
   r, s = signature(nf(O))
   @assert order(BS) == divexact(order(C) * 2^r, order(_Q))

  return BS, disclog, _exp
end

function _principal_ideals_modulo_totally_positive_principal_ideals(O, mU)
  S, mS, h, rlp = units_modulo_totally_positive_units(O, mU)
  OK = maximal_order(O)
  R, f, g = sign_map(OK, _embedding.(rlp), 1 * OK)
  # First take the quotient of R by the totally positive units
  RR, mRR = quo(R, elem_type(R)[R(Int[1 for i in 1:ngens(R)])], false)
  SinRR_gen = elem_type(RR)[]
  for i in 1:ngens(S)
    push!(SinRR_gen, mRR(g(elem_in_nf(mU(mS\(S[i]))))))
  end

  Q, mQ = quo(RR, SinRR_gen, false)
  QQ, QQtoQ = snf(Q)
  gg = x -> QQtoQ\(mQ(mRR(g(x))))
  ff = y -> elem_in_nf(f(mRR\(mQ\(QQtoQ(y)))))
  return QQ, ff, gg
end

function units_modulo_totally_positive_units(O::AbsSimpleNumFieldOrder)
  U, mU = unit_group(O)
  return units_modulo_totally_positive_units(O, mU)
end

function units_modulo_totally_positive_units(O::AbsSimpleNumFieldOrder, mU)
  OK = maximal_order(O) # Will be computed anyway
  U = domain(mU)
  K = nf(O)
  r, = signature(K)
  rlp = real_places(K)

  A = abelian_group([2 for i in 1:r])
  imag = elem_type(A)[]
  for i in 1:ngens(U)
    v = A(Int[ sign(mU(U[i]), s) == -1 ? 1 : 0 for s in rlp])
    push!(imag, v)
  end

  h = hom(U, A, imag)

  K, mK = kernel(h, false)

  Q, mQ = quo(U, mK, false)
  S, StoQ = snf(Q)
  return S, mQ * inv(StoQ), h, rlp
end

