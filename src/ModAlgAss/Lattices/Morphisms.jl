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
  x = action_of_basis(L)
  B = _basis_of_integral_commutator_algebra(x, x)
  # before we transport into domain(f), we first have to write it in the basis of A
  Bm = basis_matrix(L)
  Bminv = basis_matrix_inverse(L)
  bas = [Bminv * b * Bm for b in B]
  E = domain(f)
  O = Order(E, E.(bas))
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
  x = action_of_basis(L)
  y = action_of_basis(M)
  B = _basis_of_integral_commutator_algebra(y, x)
  for b in B
    for i in 1:length(x)
      @assert x[i] * b == b * y[i]
    end
  end

  # These should be maps from L to M
  Bminv = basis_matrix_inverse(L)
  Bm = basis_matrix(M)
  bas = [Bminv * b * Bm for b in B]

  # This is a basis for Hom_Lambda(L, M)
  E, f = endomorphism_algebra(L.V)
  O = endomorphism_ring(f, M) # this is End_Lambda(M) in E = End_A(V)
  Ibas = E.(bas) # this is Hom_Lambda(L, M) in E = End_A(V)
  I = ideal(E, O, FakeFmpqMat(basis_matrix(Ibas)); side=:right)
  @assert _test_ideal_sidedness(I, O, :right)
  return E, f, O, I
end

################################################################################
#
#  Local isomorphism
#
################################################################################

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

function _is_isomorphic_with_isomorphism_same_ambient_module(L::ModAlgAssLat, M::ModAlgAssLat; strategy = :default)
  E, f, O, I = _hom_space_as_ideal(L, M)
  if strategy == :s1
    fl = __isprincipal_s1(O, I, :right)
    return fl, zero_map(L.V, M.V)
  end
  fl, beta = __isprincipal(O, I, :right)
  if !fl 
    return false, zero_map(L.V, M.V)
  else
    isom = f(beta)
    # test something
    @assert isom(L) == M
    return true, isom
  end
end

function is_isomorphic_with_isomorphism(L::ModAlgAssLat, M::ModAlgAssLat; strategy = :s1)
  # the hom_space function wants L and M sitting inside the same ambient space
  # there is some choice we can make
  # we try to choose the order, where we already computed the endomorphism
  # algebra

  if get_attribute(L.V, :endomorphism_algebra) !== nothing && isdefined(domain(get_attribute(L.V, :endomorphism_algebra)), :decomposition)
    fl, iso = is_isomorphic_with_isomorphism(M.V, L.V)
    if !fl
      return false, zero_map(L.V, M.V)
    end
    MM = iso(M)
    fl, LtoMM = _is_isomorphic_with_isomorphism_same_ambient_module(L, MM; strategy = strategy)
    if fl
      _iso = LtoMM * inv(iso)
      if !is_zero(LtoMM.matrix)
        @assert _iso(L) == M
      end
      return true, _iso
    else
      return false, zero_map(L.V, M.V)
    end
  else
    fl, iso = is_isomorphic_with_isomorphism(L.V, M.V)
    if !fl
      return false, zero_map(L.V, M.V)
    end
    LL = iso(L)
    fl, LLtoM = _is_isomorphic_with_isomorphism_same_ambient_module(LL, M; strategy = strategy)
    if fl
      _iso = iso * LLtoM
      @assert _iso(L) == M
      return true, _iso
    else
      return false, zero_map(L.V, M.V)
    end
  end
end

function is_isomorphic(L::ModAlgAssLat, M::ModAlgAssLat; strategy = :default)
  return is_isomorphic_with_isomorphism(L, M; strategy = strategy)[1]
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
function is_aut_isomorphic(L::ModAlgAssLat, M::ModAlgAssLat; strategy = :default)
  G = group(algebra(L.base_ring))
  H = group(algebra(M.base_ring))
  if G !== H
    M = _make_compatible(L, M)
  end

  for T in _twists(M)
    if is_isomorphic(L, T; strategy = strategy)
      return true
    end
  end
  return false
end

function _make_compatible(L::ModAlgAssLat, M::ModAlgAssLat)
  G = group(algebra(L.base_ring))
  H = group(algebra(M.base_ring))
  @assert is_isomorphic(G, H)
  i = isomorphism(G, H)
  h = hom(algebra(L.base_ring), algebra(M.base_ring), i)
  return change_base_ring(h, L.base_ring, M)
end
