################################################################################
#
#   Endomorphism ring
#
################################################################################

function _basis_of_hom(L::ModAlgAssLat, M::ModAlgAssLat)
  x = action_of_basis(L)
  y = action_of_basis(M)
end

@doc raw"""
    endomorphism_ring(f::EndAlgMap, L::ModAlgAssLat) -> Order

Given an lattice $L$ of a module $V$ and $f : E \to \mathrm{End}(V)$
the endomorphism algebra map, return $\mathrm{End}(L)$ as an order
of $E$.
"""
function endomorphism_ring(f::EndAlgMap, L::ModAlgAssLat)
  @req L.V === f.V "Module of lattice must be module of the endomorphism algebra"
  data = get_attribute(L, :endomorphism_ring)
  if data !== nothing
    O, ff = data
    if ff !== f
      error("Something odd in the caching")
    end
    return O
  end
  @show "endomorphism_ring computation: $(objectid(L))"

  Bm = basis_matrix(L)
  Bminv = basis_matrix_inverse(L)
  E = domain(f)

  BE = basis(E)
  BEL = [matrix(Bm * b * Bminv) for b in BE]
  BELint = [ change_base_ring(ZZ, denominator(x) * x) for x in BEL ]
  n = nrows(BELint[1])
  r = length(BELint)
  Z = zero_matrix(ZZ, r, n^2)
  cartesiantolinear = LinearIndices((n, n))
  lineartocartesian = CartesianIndices((n, n))
  for i in 1:r
    for j in 1:n^2
      tup = lineartocartesian[j]
      Z[i, j] = BELint[i][tup[1], tup[2]]
    end
  end
  ZS = saturate(Z)
  for i in 1:r
    for j in 1:n^2
      tup = lineartocartesian[j]
      BELint[i][tup[1], tup[2]] = ZS[i, j]
    end
  end
  bas = [Bminv * b * Bm for b in BELint]
  O = Order(E, E.(bas), isbasis = true, check = false)
  set_attribute!(L, :endomorphism_ring => (O, f))
  return O
end

################################################################################
#
#  Restriction
#
################################################################################

function restricts_to_morphism(f::ModAlgHom, L::ModAlgAssLat, M::ModAlgAssLat)
  return issubset(image(f, L), M)
end

function restricts_to_isomorphism(f::ModAlgHom, L::ModAlgAssLat, M::ModAlgAssLat)
  Lf = image(f, L)
  return issubset(LF, M) && isone(index(Lf, M))
end

################################################################################
#
#  Image of a lattice under a morphism
#
################################################################################

function image(f::ModAlgHom, L::ModAlgAssLat)
  @req L.V === f.domain "Lattice must be a lattice of the domain"
  return lattice(codomain(f), L.base_ring, basis_matrix(L) * f.matrix)
end

################################################################################
#
#  Hom module
#
################################################################################

# The following is the construction of Hom_Lambda(L, M)
# as a right End_Lambda(M)-ideal of End_A(KM)
#
# The return value is
# E = endomorphism algebra End_A(KM)
# f = the map from E to endomorphisms of KM
# O = End_Lambda(M) is an order of End_A(KM)
# I = Hom_Lmabda(L, M) as a right End_Lambda(M)-ideal
function _hom_space_as_ideal(L::ModAlgAssLat, M::ModAlgAssLat)
  @req L.V === M.V "Lattices must have equal ambient module"
  @req L.base_ring === M.base_ring "Lattices must have equal order"

  E, f = endomorphism_algebra(L.V)
  O = endomorphism_ring(f, M) # this is End_Lambda(M) in E = End_A(V)

  # write the basis of E with respect to the basis of L and M respectively
  B = [ basis_matrix(L) * matrix(b) * basis_matrix_inverse(M) for b in basis(E)]
  Bint = [ map_entries(ZZ, denominator(x) * x) for x in B]
  # no write into big matrix, saturate and convert back
  n = nrows(Bint[1])
  r = length(Bint)
  Z = zero_matrix(ZZ, r, n^2)
  cartesiantolinear = LinearIndices((n, n))
  lineartocartesian = CartesianIndices((n, n))
  for i in 1:r
    for j in 1:n^2
      tup = lineartocartesian[j]
      Z[i, j] = Bint[i][tup[1], tup[2]]
    end
  end
  ZS = saturate(Z)
  # just overwrite Bint, we don't need it
  for i in 1:r
    for j in 1:n^2
      tup = lineartocartesian[j]
      Bint[i][tup[1], tup[2]] = ZS[i, j]
    end
  end
  bas = [basis_matrix_inverse(L) * b * basis_matrix(M) for b in Bint]
  Ibas = E.(bas) # this is Hom_Lambda(L, M) in E = End_A(V)
  I = ideal(E, O, FakeFmpqMat(basis_matrix(Ibas)); side=:right)

  return E, f, O, I
end

################################################################################
#
#  Local isomorphism
#
################################################################################

function is_locally_isomorphic(L::ModAlgAssLat, M::ModAlgAssLat)
  fl, iso = is_isomorphic_with_isomorphism(M.V, L.V)
  if !fl
    return false, zero_map(L.V, M.V)
  end
  MM = iso(M)
  return _is_locally_isomorphic_same_ambient_module(L, MM)
end

function _is_locally_isomorphic_same_ambient_module(L::ModAlgAssLat, M::ModAlgAssLat)
  T = basis_matrix(L) * inv(basis_matrix(M))
  d = denominator(T)
  dd = det(T)
  ps = union(prime_divisors(d), prime_divisors(numerator(dd)), prime_divisors(denominator(dd)))
  for p in ps
    if !is_locally_isomorphic(L, M, p)
      return false
    end
  end
  return true
end

function is_locally_isomorphic_with_isomophism(L::ModAlgAssLat, M::ModAlgAssLat, p::IntegerUnion)
  @req L.base_ring === M.base_ring "Orders of lattices must agree"
  @req base_ring(L.base_ring) isa ZZRing "Order must be a Z-order"

  if is_absolutely_irreducible_known(L.V) && is_absolutely_irreducible(L.V)
    fl, t = _is_locl_iso_abs_irred(L, M, p, Val{true})
  else
    fl, t =  _is_loc_iso_gen(L, M, p, Val{true})
  end

  if fl
    @assert is_equal_locally(image(t, L), M, p)
  end
  return fl, t
end

function is_locally_isomorphic(L::ModAlgAssLat, M::ModAlgAssLat, p::IntegerUnion)
  @req L.base_ring === M.base_ring "Orders of lattices must agree"
  @req base_ring(L.base_ring) isa ZZRing "Order must be a Z-order"
  if is_absolutely_irreducible_known(L.V) && is_absolutely_irreducible(L.V)
    fl = _is_loc_iso_abs_irred(L, M, p, Val{false})
  else
    fl = _is_loc_iso_gen(L, M, p, Val{false})
    if is_absolutely_irreducible_known(L.V) && is_absolutely_irreducible(L.V)
      @assert _is_loc_iso_gen(L, M, p, Val{false}) == _is_loc_iso_abs_irred(L, M, p, Val{false})
    end
  end
  return fl
end

function _is_loc_iso_gen(L::ModAlgAssLat,
                         M::ModAlgAssLat,
                         p::IntegerUnion,
                         with_iso::Type{Val{S}} = Val{true}) where {S}
  E, f, O, I = _hom_space_as_ideal(L, M)
  fl, alpha = is_locally_free(I, p, side = :right)
  imal = image(f, alpha)
  if !fl
    return fl, imal
  end
  mat = matrix(imal)
  # I need to test whether M is a (p-)local isomorphism L -> M
  newbasmat = basis_matrix(L) * mat * basis_matrix_inverse(M) # this is the basis of L * mat, represented in M
  for i in 1:nrows(newbasmat)
    for j in 1:ncols(newbasmat)
      if !iszero(newbasmat[i, j]) && valuation(newbasmat[i, j], p) < 0
        if with_iso === Val{true}
          return false, imal
        else
          return false
        end
      end
    end
  end
  # This means (L * mat)_p \subseteq M_p
  # This is an equality if and only if the base change matrix is invertible modulo p.
  if with_iso === Val{true}
    return valuation(det(newbasmat), p) == 0, imal
  else
    return valuation(det(newbasmat), p) == 0
  end
end

function _is_loc_iso_abs_irred(L::ModAlgAssLat,
                               M::ModAlgAssLat,
                               p::IntegerUnion,
                               with_iso::Type{Val{S}} = Val{true}) where {S}
  # We are assuming that L.V === M.V is absolutely irreducible
  # I will not even check this.
  T = basis_matrix(L) * basis_matrix_inverse(M)
  d = denominator(T)
  T = d * T
  if with_iso === Val{true}
    fl = iszero(valuation(det(T), p))
    if fl
      error("Tell the developers to finally do it!")
    else
      return false, T
    end
  else
    return iszero(valuation(det(T), p))
  end
end

################################################################################
#
#  Isomorphism
#
################################################################################

function _is_isomorphic_with_isomorphism_same_ambient_module(L::ModAlgAssLat, M::ModAlgAssLat, with_iso::Type{Val{T}} = Val{true}) where {T}
  E, f, O, I = _hom_space_as_ideal(L, M)
  # This is BHJ, 2022, Prop. 3.3
  # Need to check that L and M are locally isomorphic
  if with_iso === Val{true}
    fl, beta = is_principal_with_data(I, O, side = :right)
    if !fl
      return false, zero_map(L.V, M.V)
    end
    isom = f(beta)
    # test something
    @assert isom(L) == M
    return true, isom
  else
    return is_principal(I, O, side = :right)
  end
end

function is_isomorphic_with_isomorphism(L::ModAlgAssLat, M::ModAlgAssLat)
  return _is_isomorphic(L, M, Val{true})
end

function is_isomorphic(L::ModAlgAssLat, M::ModAlgAssLat)
  return _is_isomorphic(L, M, Val{false})
end

function _is_isomorphic(L::ModAlgAssLat, M::ModAlgAssLat, with_iso::Type{Val{T}}) where {T}
  # the hom_space function wants L and M sitting inside the same ambient space
  # there is some choice we can make
  # we try to choose the order, where we already computed the endomorphism
  # algebra

  endoMVknown = get_attribute(M.V, :endomorphism_algebra) !== nothing && isdefined(domain(get_attribute(M.V, :endomorphism_algebra)), :decomposition)
  endoLVknown = get_attribute(L.V, :endomorphism_algebra) !== nothing && isdefined(domain(get_attribute(L.V, :endomorphism_algebra)), :decomposition)

  # We always prefer to do things in M
  if endoMVknown || (!endoMVknown && !endoLVknown)
    fl, iso = is_isomorphic_with_isomorphism(L.V, M.V)
    if !fl
      if with_iso === Val{false}
        return false
      else
        return false, zero_map(L.V, M.V)
      end
    end
    LL = iso(L)
    if with_iso === Val{false}
      return _is_isomorphic_with_isomorphism_same_ambient_module(LL, M, with_iso)
    else
      fl, LLtoM = _is_isomorphic_with_isomorphism_same_ambient_module(LL, M, with_iso)
      if fl
        _iso = iso * LLtoM
        @assert _iso(L) == M
        return true, _iso
      else
        return false, zero_map(L.V, M.V)
      end
    end
  else
    fl, iso = is_isomorphic_with_isomorphism(M.V, L.V)
    if !fl
      if with_iso === Val{false}
        return false
      else
        return false, zero_map(L.V, M.V)
      end
    end
    MM = iso(M)
    if with_iso === Val{false}
      return _is_isomorphic_with_isomorphism_same_ambient_module(L, MM, with_iso)
    else
      fl, LtoMM = _is_isomorphic_with_isomorphism_same_ambient_module(L, MM, with_iso)
      if fl
        _iso = LtoMM * inv(iso)
        @assert _iso(L) == M
        return true, _iso
      else
        return false, zero_map(L.V, M.V)
      end
    end
  end
end

################################################################################
#
#  Freeness test
#
################################################################################

function is_free(L::ModAlgAssLat)
  O = L.base_ring
  if !is_free(L.V)
    return false
  end
  @assert L.V.free_rank == 1
  return is_isomorphic(L, free_lattice(O, 1))
end

function is_free_with_basis(L::ModAlgAssLat)
  if !is_free(L.V)
    return false, elem_type(L.V)[]
  end
  d = L.V.free_rank
  @assert d != -1
  @assert d == 1
  O = L.base_ring
  A = algebra(O)
  M = free_lattice(O, d)
  V = M.V
  fl, iso = is_isomorphic_with_isomorphism(L, M)
  if fl
    return true, [preimage(iso, _element_of_standard_free_module(V, [elem_in_algebra(one(M.base_ring)) for i in 1:d]))]
  else
    return false, elem_type(L.V)[]
  end
end

function is_locally_free(L::ModAlgAssLat, p::IntegerUnion)
  if !is_free(L.V)
    return false
  end
  d = L.V.free_rank
  @assert d != -1
  O = L.base_ring
  M = free_lattice(O, d)
  fl, LL, MM = _can_transport_into_same_ambient_module(L, M)
  if !fl
    return false
  else
    return is_locally_isomorphic(LL, MM, p)[1]
  end
end

function _can_transport_into_same_ambient_module(L, M)
  if L.V === M.V
    return true, L, M
  end
  fl, iso = is_isomorphic_with_isomorphism(M.V, L.V)
  if !fl
    return false, L, M
  end
  MM = iso(M)
  return true, L, MM
end

################################################################################
#
#  Testing Aut(G)-isomorphism
#
################################################################################

# Take a Z[G]-lattice L and Z[H]-lattice M with G isomorhic to H
# Check if there is an isomorphism G -> H, such that
# L and M are isomorphic
# If G === H, this is the test for Aut(G)-isomorphism
function is_aut_isomorphic(L::ModAlgAssLat, M::ModAlgAssLat)
  G = group(algebra(L.base_ring))
  H = group(algebra(M.base_ring))
  if G !== H
    # I adjust L, so that all things cached on M are preserved
    # (the data on M is used for isomorphism checks)
    L = _make_compatible(M, L)
  end

  for T in _twists(L)
    if is_isomorphic(T, M)
      return true
    end
  end
  return false
end

function _make_compatible(L::ModAlgAssLat, M::ModAlgAssLat)
  # Returns a module M', such that M' is defined over the same
  # group as L such that
  # L is aut-isomorphic to M, if and ony if it is aut-isomorphic
  # to M'
  G = group(algebra(L.base_ring))
  H = group(algebra(M.base_ring))
  @assert is_isomorphic(G, H)
  i = isomorphism(G, H)
  h = hom(algebra(L.base_ring), algebra(M.base_ring), i)
  return change_base_ring(h, L.base_ring, M)
end
