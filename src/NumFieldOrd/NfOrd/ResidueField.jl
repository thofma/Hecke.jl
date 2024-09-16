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
#                        - a vector of ZZMatrix B, such that
#                          pi(basis(O)[i]) = sum_j B[i][1, j] * pi(a)^j
function compute_residue_field_data(m, phi)
  O = domain(m)
  basisO = basis(O, copy = false)
  B = codomain(m)
  primB, minprimB, getcoordpowerbasis = _as_field(B)
  f = degree(minprimB)
  F = domain(phi)
  @assert F === base_ring(O)
  prim_elem = m\(primB)
  min_poly_prim_elem = (polynomial_ring(F, :$, cached = false)[1])(elem_type(F)[preimage(phi, coeff(minprimB, i)) for i in 0:degree(minprimB)])
  basis_in_prim = Vector{dense_matrix_type(F)}(undef, degree(O))
  for i in 1:degree(O)
    basis_in_prim[i] = zero_matrix(F, 1, f)
    t = getcoordpowerbasis(m(basisO[i]))
    for j in 1:f
      basis_in_prim[i][1, j] = preimage(phi, t[1, j])
    end
  end
  return prim_elem, min_poly_prim_elem, basis_in_prim, phi
end

# Compute the residue field data and store it in the prime P given the map m
function compute_residue_field_data!(P::AbsNumFieldOrderIdeal, m)
  F = base_ring(codomain(m))
  phi = MapFromFunc(ZZ, F, x -> F(x), y -> lift(ZZ, y))
  return compute_residue_field_data!(P, m, phi)
end

function compute_residue_field_data!(P, m, phi)
  P.prim_elem, P.min_poly_prim_elem, P.basis_in_prim, P.phi = compute_residue_field_data(m, phi)
  return nothing
end

# Compute the residue field data given the prime P
function compute_residue_field_data!(P)
  p = minimum(P)
  if isa(p, IntegerUnion) && fits(Int, p)
    smallp = Int(p)
    A, m = StructureConstantAlgebra(order(P), P, smallp)
    compute_residue_field_data!(P, m)
  else
    _, phi = residue_field(base_ring(order(P)), p)
    AA, mm = StructureConstantAlgebra(order(P), P, p, phi)
    compute_residue_field_data!(P, mm, phi)
  end
  return nothing
end

# Get the residue field data. This is the function one should use, since the
# data is often cached.
function get_residue_field_data(P)
  if isdefined(P, :prim_elem)
    return P.prim_elem, P.min_poly_prim_elem, P.basis_in_prim, P.phi
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

function _residue_field_nonindex_divisor_helper_fq_default(f::QQPolyRingElem, g::QQPolyRingElem, p)
  R = finite_field(p, 1, :o, cached = false, check = false)[1]

  Zy, y = polynomial_ring(ZZ, "y", cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)

  gmodp = Rx(g)
  fmodp = Rx(f)

  h = gcd(gmodp, fmodp)

  return Nemo._residue_field(h, check = false)[1], h
end

# It is assumed that p is not an index divisor
function _residue_field_nonindex_divisor_helper(f::QQPolyRingElem, g::QQPolyRingElem, p, ::Val{degree_one} = Val(false)) where degree_one
  R = Native.GF(p, cached = false, check = false)

  Zy, y = polynomial_ring(FlintZZ, "y", cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)

  gmodp = Rx(g)
  fmodp = Rx(f)

  h = gcd(gmodp,fmodp)

  if degree_one
    return R, h
  else
    if isa(p, Int)
      F3 = fqPolyRepField(h, :$, false)
      return F3, h
    elseif isa(p, ZZRingElem)
      F4 = FqPolyRepField(h, :$, false)
      return F4, h
    end
  end
end

function _residue_field_nonindex_divisor_fq_default(O, P)
  @assert has_2_elem(P) && is_prime_known(P) && is_prime(P)

  gtwo = P.gen_two

  f = nf(O).pol
  g = parent(f)(elem_in_nf(gtwo))

  F, h = _residue_field_nonindex_divisor_helper_fq_default(f, g, minimum(P))
  mF = Mor(O, F, h)
  mF.P = P
end

function _residue_field_nonindex_divisor(O, P, ::Val{small} = Val(false), degree_one_val::Val{degree_one} = Val(false)) where {small, degree_one}
  # This code assumes that P comes from prime_decomposition
  @assert has_2_elem(P) && is_prime_known(P) && is_prime(P)

  gtwo = P.gen_two

  f = nf(O).pol
  g = parent(f)(elem_in_nf(gtwo))

  if small
    @assert fits(Int, minimum(P, copy = false))
    F, h = _residue_field_nonindex_divisor_helper(f, g, Int(minimum(P)), degree_one_val)
    mF = Mor(O, F, h)
    mF.P = P
    return F, mF
  else
    F, h = _residue_field_nonindex_divisor_helper_fq_default(f, g, minimum(P))
    mF = Mor(O, F, h)
    mF.P = P
    return F, mF
    #F, h = _residue_field_nonindex_divisor_helper(f, g, minimum(P), degree_one_val)
    #mF = Mor(O, F, h)
    #mF.P = P
    #return F, mF
  end
end

################################################################################
#
#  Residue field construction for index divisors
#
################################################################################

function _residue_field_generic_fq_default(O, P)
	f = NfOrdToFqFieldMor(O, P)
 	return codomain(f), f
end

function _residue_field_generic(O, P, ::Val{small} = Val(false), ::Val{degree_one} = Val(false)) where {small, degree_one}
  if small
    @assert fits(Int, minimum(P, copy = false))
    if degree_one
			f1 = NfOrdToGFMor(O, P)
      return codomain(f1), f1
		else
    	f = NfOrdToFqNmodMor(O, P)
    	return codomain(f), f
    end
  else
    if degree_one
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

@doc raw"""
    residue_field(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, check::Bool = true) -> Field, Map

Returns the residue field of the prime ideal $P$ together with the
projection map. If ```check``` is true, the ideal is checked for
being prime.
"""
function residue_field(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, check::Bool = true)
  if check
    !is_prime(P) && error("Ideal must be prime")
  end
  if !is_maximal_known(O) || !is_maximal(O) || !is_defining_polynomial_nice(nf(O))
    return _residue_field_generic_fq_default(O, P)
  end
  if !is_index_divisor(O, minimum(P)) && has_2_elem(P)
    return _residue_field_nonindex_divisor(O, P)
  else
    return _residue_field_generic_fq_default(O, P)
  end
end

function ResidueFieldSmall(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  p = minimum(P)
  !fits(Int, p) && error("Minimum of prime ideal must be small (< 64 bits)")
  if !is_maximal_known(O) || !is_maximal(O) || !is_defining_polynomial_nice(nf(O))
    return _residue_field_generic(O, P, Val(true))
  end
  if !is_index_divisor(O, minimum(P))
    return _residue_field_nonindex_divisor(O, P, Val(true))
  else
    return _residue_field_generic(O, P, Val(true))
  end
end

function ResidueFieldDegree1(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  @assert degree(P) == 1
  if !is_maximal_known(O) || !is_maximal(O)
    return _residue_field_generic(O, P, Val(false), Val(true))
  end
  if !is_index_divisor(O, minimum(P)) && has_2_elem(P)
    return _residue_field_nonindex_divisor(O, P, Val(false), Val(true))
  else
    return _residue_field_generic(O, P, Val(false), Val(true))
  end
end


function ResidueFieldSmallDegree1(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  p = minimum(P)
  !fits(Int, p) && error("Minimum of prime ideal must be small (< 64 bits)")
  @assert degree(P) == 1
  if !is_maximal_known(O) || !is_maximal(O) || !is_defining_polynomial_nice(nf(O))
    return _residue_field_generic(O, P, Val(true), Val(true))
  end
  if !is_index_divisor(O, minimum(P))
    return _residue_field_nonindex_divisor(O, P, Val(true), Val(true))
  else
    return _residue_field_generic(O, P, Val(true), Val(true))
  end
end

@doc raw"""
    relative_residue_field(O::RelNumFieldOrder, P::RelNumFieldOrderIdeal) -> RelFinField, Map

Given a maximal order `O` in a relative number field $E/K$ and a prime ideal
`P` of `O`, return the residue field $O/P$ seen as an extension of the (relative)
residue field of a maximal order in `K` at $minimum(P)$.

Note that if `K` is a relative number field, the latter will also be seen as a
relative residue field.
"""
function relative_residue_field(O::RelNumFieldOrder{S, T, U}, P::RelNumFieldOrderIdeal{S, T, U}) where {S, T, U}
  @req is_maximal(O) "O must be maximal"
  @req order(P) === O "P must be an ideal of O"
  E = nf(O)
  K = base_field(E)
  p = minimum(P)
  projK = get_attribute(p, :rel_residue_field_map)
  if projK === nothing
    OK = maximal_order(K)
    if !(K isa Hecke.RelSimpleNumField)
      _, projK = residue_field(OK, p)
      set_attribute!(p, :rel_residue_field_map, projK)
    else
      _, projK = relative_residue_field(OK, p)
      set_attribute!(p, :rel_residue_field_map, projK)
    end
  end
  FK = codomain(projK)
  projE = NfRelOrdToFqFieldRelMor{typeof(O)}(O, P, projK)
  #if base_field(K) isa QQField
  #  projE = NfRelOrdToRelFinFieldMor{typeof(O), FqFieldElem}(O, P, projK)
  #else
  #  projE = NfRelOrdToRelFinFieldMor{typeof(O), Hecke.RelFinFieldElem{typeof(FK), typeof(FK.defining_polynomial)}}(O, P, projK)
  #end
  set_attribute!(P, :rel_residue_field_map, projE)
  return codomain(projE), projE
end

