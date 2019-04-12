export ResidueField

################################################################################
#
#  Residue field construction for arbitrary prime ideals
#
################################################################################

# Assume that m is a surjective morphism pi: O -> A, where A is a simple algebra
# over the prime field Z/pZ.
# This functions returns - a in O, such that pi(a) is a primitive element
#                        - f in Z[X], such that f is the minimal polynomial of
#                          pi(a) 
#                        - a vector of fmpz_mat B, such that
#                          pi(basis(O)[i]) = sum_j B[i][1, j] * pi(a)^j
function compute_residue_field_data(m)
  O = domain(m)
  basisO = basis(O, copy = false)
  B = codomain(m)
  primB, minprimB, getcoordpowerbasis = _as_field(B)
  f = degree(minprimB)
  prim_elem = m\(primB)
  min_poly_prim_elem = fmpz_poly(fmpz[lift(coeff(minprimB, i)) for i in 0:degree(minprimB)])
  min_poly_prim_elem.parent = FmpzPolyRing(:$, false)
  basis_in_prim = Vector{fmpz_mat}(undef, degree(O))
  for i in 1:degree(O)
    basis_in_prim[i] = zero_matrix(FlintZZ, 1, f)
    t = getcoordpowerbasis(m(basisO[i]))
    for j in 1:f
      basis_in_prim[i][1, j] = lift(t[1, j])
    end
  end
  return prim_elem, min_poly_prim_elem, basis_in_prim
end

# Compute the residue field data and store it in the prime P given the map m
function compute_residue_field_data!(P, m)
  P.prim_elem, P.min_poly_prim_elem, P.basis_in_prim = compute_residue_field_data(m)
  return nothing
end

# Compute the residue field data given the prime P
function compute_residue_field_data!(P)
  p = minimum(P)
  if nbits(p) < 64
    smallp = Int(p)
    A, m = AlgAss(order(P), P, smallp)
    compute_residue_field_data!(P, m)
  else
    AA, mm = AlgAss(order(P), P, p)
    compute_residue_field_data!(P, mm)
  end
  return nothing
end

# Get the residue field data. This is the function one should use, since the
# data is often cached.
function get_residue_field_data(P)
  if isdefined(P, :prim_elem)
    return P.prim_elem, P.min_poly_prim_elem, P.basis_in_prim
  else
    compute_residue_field_data!(P)
    get_residue_field_data(P)
  end
end

################################################################################
#
#  Residue field construction for nonindex divisors
#
################################################################################

# It is assumed that p is not an index divisor
function _residue_field_nonindex_divisor_helper(f::fmpq_poly, g::fmpq_poly, p)
  R = GF(p, cached = false)

  Zy, y = PolynomialRing(FlintZZ, "y", cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)

  gmodp = Rx(g)
  fmodp = Rx(f)

  h = gcd(gmodp,fmodp)

  if typeof(p) == Int
    F = FqNmodFiniteField(h, :$, false)
  elseif typeof(p) == fmpz
    F = FqFiniteField(h, :$, false)
  end

  return F, h
end

function _residue_field_nonindex_divisor(O, P, small::Type{Val{T}} = Val{false}) where {T}
  # This code assumes that P comes from prime_decomposition
  @assert has_2_elem(P) && isprime_known(P) && isprime(P)

  gtwo = P.gen_two

  f = nf(O).pol
  g = parent(f)(elem_in_nf(gtwo))

  if small == Val{true}
    @assert nbits(minimum(P)) < 64
    F, h = _residue_field_nonindex_divisor_helper(f, g, Int(minimum(P)))

    #return F, Mor(O, F, gen(F))
    mF = Mor(O, F, h)
    mF.P = P
    return F, mF
  elseif small == Val{false}
    F, h = _residue_field_nonindex_divisor_helper(f, g, minimum(P))

    #return F, Mor(O, F, gen(F))
    mF = Mor(O, F, h)
    mF.P = P
    return F, mF
  end
end

################################################################################
#
#  Residue field construction for index divisors
#
################################################################################

function _residue_field_generic(O, P, small::Type{Val{T}} = Val{false}) where {T}
  if small == Val{true}
    @assert nbits(minimum(P)) < 64
    f = NfOrdToFqNmodMor(O, P)
    return codomain(f), f
  elseif small == Val{false}
    f = NfOrdToFqMor(O, P)
    return codomain(f), f
  end
end

################################################################################
#
#  High level functions
#
################################################################################
@doc Markdown.doc"""
    ResidueField(O::NfOrd, P::NfOrdIdl, check::Bool = true) -> Field, Map
Returns the residue field of the prime ideal $P$ together with th
projection map. If ```check``` is true, the ideal is checked for 
being prime.
"""
function ResidueField(O::NfOrd, P::NfOrdIdl, check::Bool = true)
  if check
    !isprime(P) && error("Ideal must be prime")
  end
  if !ismaximal_known(O) || !ismaximal(O)
    return _residue_field_generic(O, P)
  end
  if !isindex_divisor(O, minimum(P)) && has_2_elem(P)
    return _residue_field_nonindex_divisor(O, P)
  else
    return _residue_field_generic(O, P)
  end
end

function ResidueFieldSmall(O::NfOrd, P::NfOrdIdl)
  p = minimum(P)
  nbits(p) > 64 && error("Minimum of prime ideal must be small (< 64 bits)")
  if !ismaximal_known(O) || !ismaximal(O) || !isdefining_polynomial_nice(nf(O))
    return _residue_field_generic(O, P, Val{true})
  end
  if !isindex_divisor(O, minimum(P))
    return _residue_field_nonindex_divisor(O, P, Val{true})
  else
    return _residue_field_generic(O, P, Val{true})
  end
end
