export ResidueField, relative_residue_field

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
  min_poly_prim_elem.parent = FmpzPolyRing(FlintZZ, :$, false)
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
  if fits(Int, p)
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
function _residue_field_nonindex_divisor_helper(f::fmpq_poly, g::fmpq_poly, p, degree_one::Type{Val{S}} = Val{false}) where S
  R = GF(p, cached = false)

  Zy, y = PolynomialRing(FlintZZ, "y", cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)

  gmodp = Rx(g)
  fmodp = Rx(f)

  h = gcd(gmodp,fmodp)

	if degree_one === Val{true}
    return R, h
	else
  	if isa(p, Int)
    	F3 = FqNmodFiniteField(h, :$, false)
      return F3, h
  	elseif isa(p, fmpz)
    	F4 = FqFiniteField(h, :$, false)
      return F4, h
  	end
	end
end

function _residue_field_nonindex_divisor(O, P, small::Type{Val{T}} = Val{false}, degree_one::Type{Val{S}} = Val{false}) where {S, T}
  # This code assumes that P comes from prime_decomposition
  @assert has_2_elem(P) && is_prime_known(P) && is_prime(P)

  gtwo = P.gen_two

  f = nf(O).pol
  g = parent(f)(elem_in_nf(gtwo))

  if small === Val{true}
    @assert fits(Int, minimum(P, copy = false))
    F, h = _residue_field_nonindex_divisor_helper(f, g, Int(minimum(P)), degree_one)
    mF = Mor(O, F, h)
    mF.P = P
    return F, mF
  elseif small === Val{false}
    F, h = _residue_field_nonindex_divisor_helper(f, g, minimum(P), degree_one)
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

function _residue_field_generic(O, P, small::Type{Val{T}} = Val{false}, degree_one::Type{Val{S}} = Val{false}) where {S, T}
  if small == Val{true}
    @assert fits(Int, minimum(P, copy = false))
    if degree_one === Val{true}
			f1 = NfOrdToGFMor(O, P)
      return codomain(f1), f1
		else
    	f = NfOrdToFqNmodMor(O, P)
    	return codomain(f), f
    end
  elseif small === Val{false}
    if degree_one === Val{true}
    	f3 = NfOrdToGFFmpzMor(O, P)
      return codomain(f3), f3
		else
			f2 = NfOrdToFqMor(O, P)
    	return codomain(f2), f2
		end
  end
end

################################################################################
#
#  High level functions
#
################################################################################
@doc Markdown.doc"""
    ResidueField(O::NfOrd, P::NfOrdIdl, check::Bool = true) -> Field, Map

Returns the residue field of the prime ideal $P$ together with the
projection map. If ```check``` is true, the ideal is checked for
being prime.
"""
function ResidueField(O::NfOrd, P::NfOrdIdl, check::Bool = true)
  if check
    !is_prime(P) && error("Ideal must be prime")
  end
  if !is_maximal_known(O) || !is_maximal(O)
    return _residue_field_generic(O, P)
  end
  if !is_index_divisor(O, minimum(P)) && has_2_elem(P)
    return _residue_field_nonindex_divisor(O, P)
  else
    return _residue_field_generic(O, P)
  end
end

function ResidueFieldSmall(O::NfOrd, P::NfOrdIdl)
  p = minimum(P)
  !fits(Int, p) && error("Minimum of prime ideal must be small (< 64 bits)")
  if !is_maximal_known(O) || !is_maximal(O) || !is_defining_polynomial_nice(nf(O))
    return _residue_field_generic(O, P, Val{true})
  end
  if !is_index_divisor(O, minimum(P))
    return _residue_field_nonindex_divisor(O, P, Val{true})
  else
    return _residue_field_generic(O, P, Val{true})
  end
end

function ResidueFieldDegree1(O::NfOrd, P::NfOrdIdl)
  @assert degree(P) == 1
  if !is_maximal_known(O) || !is_maximal(O)
    return _residue_field_generic(O, P, Val{false}, Val{true})
  end
  if !is_index_divisor(O, minimum(P)) && has_2_elem(P)
    return _residue_field_nonindex_divisor(O, P, Val{false}, Val{true})
  else
    return _residue_field_generic(O, P, Val{false}, Val{true})
  end
end


function ResidueFieldSmallDegree1(O::NfOrd, P::NfOrdIdl)
  p = minimum(P)
  !fits(Int, p) && error("Minimum of prime ideal must be small (< 64 bits)")
  @assert degree(P) == 1
  if !is_maximal_known(O) || !is_maximal(O) || !is_defining_polynomial_nice(nf(O))
    return _residue_field_generic(O, P, Val{true}, Val{true})
  end
  if !is_index_divisor(O, minimum(P))
    return _residue_field_nonindex_divisor(O, P, Val{true}, Val{true})
  else
    return _residue_field_generic(O, P, Val{true}, Val{true})
  end
end

@doc Markdown.doc"""
    relative_residue_field(O::NfRelOrd, P::NfRelOrdIdl) -> RelFinField, Map

Given a maximal order `O` in a relative number field $E/K$ and a prime ideal 
`P` of `O`, return the residue field $O/P$ seen as an extension of the (relative) 
residue field of a maximal order in `K` at $minimum(P)$.

Note that if `K` is a relative number field, the latter will also be seen as a 
relative residue field.
"""
function relative_residue_field(O::NfRelOrd{S, T, U}, P::NfRelOrdIdl{S, T, U}) where {S, T, U}
  @req is_maximal(O) "O must be maximal"
  @req order(P) === O "P must be an ideal of O"
  E = nf(O)
  K = base_field(E)
  p = minimum(P)
  projK = get_attribute(p, :rel_residue_field_map)
  if projK === nothing
    OK = maximal_order(K)
    if !(K isa Hecke.NfRel)
      _, projK = ResidueField(OK, p)
      set_attribute!(p, :rel_residue_field_map, projK)
    else
      _, projK = relative_residue_field(OK, p)
      set_attribute!(p, :rel_residue_field_map, projK)
    end
  end
  FK = codomain(projK)
  if base_field(K) isa FlintRationalField
    projE = NfRelOrdToRelFinFieldMor{typeof(O), fq}(O, P, projK)
  else
    projE = NfRelOrdToRelFinFieldMor{typeof(O), Hecke.RelFinFieldElem{typeof(FK), typeof(FK.defining_polynomial)}}(O, P, projK)
  end
  set_attribute!(P, :rel_residue_field_map, projE)
  return codomain(projE), projE
end

