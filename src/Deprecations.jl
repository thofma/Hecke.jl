###############################################################################
#
#   Aliases
#
###############################################################################

# ALL aliases here are only a temporary measure to allow for a smooth transition downstream.
# they will be replaced by deprecations eventually

#= currently none =#

###############################################################################
#
#   Deprecated bindings
#
###############################################################################

# Deprecated bindings don't get reexported automatically in Oscar/etc.
# By calling this macro from the respective packages, we can ensure that the deprecated bindings are available there.
macro include_deprecated_bindings()
  return esc(quote
      # Deprecated during 0.24.*
      Base.@deprecate_binding TorQuadModuleMor TorQuadModuleMap

      # deprecated for 0.28
      Base.@deprecate_binding AbsLat AbstractLat
      Base.@deprecate_binding AbsSpace AbstractSpace
      Base.@deprecate_binding AbsSpaceMor AbstractSpaceMor
      Base.@deprecate_binding GenusHerm HermGenus
      Base.@deprecate_binding GenusQuad QuadGenus
      Base.@deprecate_binding LocalGenusHerm HermLocalGenus
      Base.@deprecate_binding LocalGenusQuad QuadLocalGenus
      Base.@deprecate_binding TorQuadMod TorQuadModule
      Base.@deprecate_binding TorQuadModElem TorQuadModuleElem
      Base.@deprecate_binding TorQuadModMor TorQuadModuleMap
      Base.@deprecate_binding ZGenus ZZGenus
      Base.@deprecate_binding ZLat ZZLat
      Base.@deprecate_binding ZpGenus ZZLocalGenus

  end)
end

@include_deprecated_bindings()

###############################################################################
#
#   Deprecations
#
###############################################################################

# Deprecated during 0.24.*

@deprecate hasimage has_image_with_image
@deprecate has_image has_image_with_image

@deprecate haspreimage has_preimage_with_preimage
@deprecate has_preimage has_preimage_with_preimage

@deprecate psylow_subgroup sylow_subgroup

# deprecated for 0.28

@deprecate add_assert_scope add_assertion_scope
@deprecate add_verbose_scope add_verbosity_scope

@deprecate get_assert_level get_assertion_level
@deprecate get_verbose_level get_verbosity_level
@deprecate genera integer_genera
@deprecate genera_hermitian hermitian_genera
@deprecate genera_quadratic quadratic_genera

@deprecate hasalgebra has_algebra
@deprecate hasembedding has_embedding
@deprecate hasmatrix_action has_matrix_action
@deprecate hasroot has_root

@deprecate is2_normal_difficult is_2_normal_difficult
@deprecate isGLZ_conjugate is_GLZ_conjugate
@deprecate isabelian is_abelian
@deprecate isabelian2 is_abelian2
@deprecate isabsolute is_absolute
@deprecate isabsolutely_primitive is_absolutely_primitive
@deprecate isalmost_maximally_ramified is_almost_maximally_ramified
@deprecate isautomorphisms_known is_automorphisms_known
@deprecate isbass is_bass
@deprecate isbijective is_bijective
@deprecate iscached is_cached
@deprecate iscanonical is_canonical
@deprecate iscentral is_central
@deprecate ischain_complex is_chain_complex
@deprecate ischaracteristic is_characteristic
@deprecate iscm is_cm
@deprecate iscm_field is_cm_field
@deprecate iscm_field_easy is_cm_field_easy
@deprecate iscm_field_known is_cm_field_known
@deprecate iscochain_complex is_cochain_complex
@deprecate iscommutative is_commutative
@deprecate iscommutative_known is_commutative_known
@deprecate iscomplex is_complex
@deprecate iscomplex_conjugation is_complex_conjugation
@deprecate isconductor is_conductor
@deprecate isconjugate is_conjugate
@deprecate isconsistent is_consistent
@deprecate iscontained is_contained
@deprecate iscoprime is_coprime
@deprecate iscyclic is_cyclic
@deprecate iscyclotomic_type is_cyclotomic_type
@deprecate isdefining_polynomial_nice is_defining_polynomial_nice
@deprecate isdefinite is_definite
@deprecate isdegenerate is_degenerate
@deprecate isdiagonalisable is_diagonalisable
@deprecate isdiscriminant is_discriminant
@deprecate isdivisible is_divisible
@deprecate isdivisible2 is_divisible2
@deprecate isdivisible_mod_ideal is_divisible_mod_ideal
@deprecate isdyadic is_dyadic
@deprecate iseichler is_eichler
@deprecate iseisenstein_polynomial is_eisenstein_polynomial
@deprecate iseq is_eq
@deprecate isequation_order is_equation_order
@deprecate isequivalent is_equivalent
@deprecate isfinite_gen is_finite_gen
@deprecate isfinite_snf is_finite_snf
@deprecate isfixed_point_free is_fixed_point_free
@deprecate isfree is_free
@deprecate isfree_a4_fabi is_free_a4_fabi
@deprecate isfree_a5_fabi is_free_a5_fabi
@deprecate isfree_resolution is_free_resolution
@deprecate isfree_s4_fabi is_free_s4_fabi
@deprecate isfrom_db is_from_db
@deprecate isfull_lattice is_full_lattice
@deprecate isfundamental_discriminant is_fundamental_discriminant
@deprecate isgenus is_genus
@deprecate isgood_bong is_good_bong
@deprecate isgorenstein is_gorenstein
@deprecate isidentity is_identity
@deprecate isin is_in
@deprecate isindefinite is_indefinite
@deprecate isindependent is_independent
@deprecate isindex_divisor is_index_divisor
@deprecate isinduced is_induced
@deprecate isinert is_inert
@deprecate isinfinite is_infinite
@deprecate isinjective is_injective
@deprecate isintegral is_integral
@deprecate isinvolution is_involution
@deprecate isirreducible_easy is_irreducible_easy
@deprecate isirreducible_known is_irreducible_known
@deprecate isisometric is_isometric
@deprecate isisometric_with_isometry is_isometric_with_isometry
@deprecate isisotropic is_isotropic
@deprecate iskummer_extension is_kummer_extension
@deprecate isleaf is_leaf
@deprecate isleft_ideal is_left_ideal
@deprecate islessorequal is_lessorequal
@deprecate islinearly_disjoint is_linearly_disjoint
@deprecate islll_reduced is_lll_reduced
@deprecate islocal_norm is_local_norm
@deprecate islocal_square is_local_square
@deprecate islocally_equivalent is_locally_equivalent
@deprecate islocally_free is_locally_free
@deprecate islocally_hyperbolic is_locally_hyperbolic
@deprecate islocally_isometric is_locally_isometric
@deprecate islocally_isometric_kirschmer is_locally_isometric_kirschmer
@deprecate islocally_isomorphic is_locally_isomorphic
@deprecate islocally_isomorphic_with_isomophism is_locally_isomorphic_with_isomophism
@deprecate islocally_represented_by is_locally_represented_by
@deprecate ismaximal is_maximal
@deprecate ismaximal_integral is_maximal_integral
@deprecate ismaximal_known is_maximal_known
@deprecate ismaximal_known_and_maximal is_maximal_known_and_maximal
@deprecate ismaximal_order_known is_maximal_order_known
@deprecate ismodular is_modular
@deprecate isnegative_definite is_negative_definite
@deprecate isnorm is_norm
@deprecate isnorm_divisible is_norm_divisible
@deprecate isnorm_divisible_pp is_norm_divisible_pp
@deprecate isnorm_fac_elem is_norm_fac_elem
@deprecate isnormal is_normal
@deprecate isnormal_basis_generator is_normal_basis_generator
@deprecate isnormal_difficult is_normal_difficult
@deprecate isnormal_easy is_normal_easy
@deprecate isnormalized is_normalized
@deprecate isone_sided is_one_sided
@deprecate ispairwise_coprime is_pairwise_coprime
@deprecate ispositive_definite is_positive_definite
@deprecate ispower_trager is_power_trager
@deprecate ispower_unram is_power_unram
@deprecate isprimary is_primary
@deprecate isprime_known is_prime_known
@deprecate isprime_nice is_prime_nice
@deprecate isprime_power is_prime_power
@deprecate isprimitive is_primitive
@deprecate isprimitive_over is_primitive_over
@deprecate isprimitive_root is_primitive_root
@deprecate isprincipal is_principal
@deprecate isprincipal_fac_elem is_principal_fac_elem
#@deprecate isprincipal_maximal is_principal_maximal
#@deprecate isprincipal_maximal_fac_elem is_principal_maximal_fac_elem
#@deprecate isprincipal_non_maximal is_principal_non_maximal
@deprecate ispseudo_hnf is_pseudo_hnf
@deprecate isquadratic is_quadratic
@deprecate isquadratic_type is_quadratic_type
@deprecate isradical_extension is_radical_extension
@deprecate isramified is_ramified
@deprecate isrationally_isometric is_rationally_isometric
@deprecate isreduced is_reduced
@deprecate isreducible is_reducible
@deprecate isregular is_regular
@deprecate isregular_at is_regular_at
@deprecate isrepresented_by is_represented_by
@deprecate isright_ideal is_right_ideal
@deprecate issimilar is_similar
@deprecate issimple is_simple
@deprecate issimple_known is_simple_known
@deprecate issimultaneous_diagonalizable is_simultaneous_diagonalizable
@deprecate issmooth is_smooth
@deprecate issmooth! is_smooth!
@deprecate issplit is_split
@deprecate isstable is_stable
@deprecate issubfield is_subfield
@deprecate issubfield_normal is_subfield_normal
@deprecate issubgroup is_subgroup
@deprecate issublattice is_sublattice
@deprecate issublattice_with_relations is_sublattice_with_relations
@deprecate issurjective is_surjective
@deprecate istamely_ramified is_tamely_ramified
@deprecate istorsion is_torsion
@deprecate istorsion_point is_torsion_point
@deprecate istorsion_unit is_torsion_unit
@deprecate istorsion_unit_group_known is_torsion_unit_group_known
@deprecate istotally_complex is_totally_complex
@deprecate istotally_positive is_totally_positive
@deprecate istotally_real is_totally_real
@deprecate istriangular is_triangular
@deprecate isweakly_ramified is_weakly_ramified
@deprecate iszero_entry is_zero_entry
@deprecate iszero_mod_hnf! is_zero_mod_hnf!
@deprecate iszerodivisor is_zerodivisor

@deprecate local_genera_hermitian hermitian_local_genera
@deprecate local_genera_quadratic quadratic_local_genera

@deprecate set_assert_level set_assertion_level
@deprecate set_verbose_level set_verbosity_level

@deprecate Zgenera integer_genera
@deprecate Zlattice integer_lattice

@deprecate real_field real_number_field

@deprecate points_with_x points_with_x_coordinate


# Deprecated for 0.29

@deprecate a_invars a_invariants
@deprecate b_invars b_invariants
@deprecate c_invars c_invariants
@deprecate basis_mat_inv(x; copy = true) basis_mat_inv(FakeFmpqMat, x; copy)

# Deprecated in 0.31.0

@deprecate force_coerce_cyclo(a::AbsSimpleNumField, b::AbsSimpleNumFieldElem, throw_error::Type{Val{T}}) where {T} force_coerce_cyclo(a, b, Val(T)) false
@deprecate reduce_full(A::SMat{T}, g::SRow{T}, trafo::Type{Val{N}}) where {N, T} reduce_full(A, g, Val(N))
@deprecate gens(A::GroupAlgebra, return_full_basis::Type{Val{T}}) where T gens(A, Val(T))
@deprecate gens(A::AbstractAssociativeAlgebra, return_full_basis::Type{Val{T}}; thorough_search::Bool = false) where T gens(A, Val(T); thorough_search)

@deprecate hom(G::FinGenAbGroup, H::FinGenAbGroup, A::Matrix{ <: Map{FinGenAbGroup, FinGenAbGroup}}) hom_direct_sum(G, H, A)
@deprecate hom(G::FinGenAbGroup, H::FinGenAbGroup, A::Vector{ <: Map{FinGenAbGroup, FinGenAbGroup}}) hom_tensor(G, H, A)

# Deprecated in 0.33.0

@deprecate rres reduced_resultant

# Deprecated in 0.34.0

@deprecate lift(a::LocalFieldValuationRingElem) lift(ZZ, a)
@deprecate prime_field(L::Union{QadicField, LocalField}) absolute_base_field(L)
@deprecate coefficient_ring(k::LocalField) base_field(k)
@deprecate coefficient_field(k::QadicField) base_field(k)

# Deprecated in 0.35.10
@deprecate minpoly(a::Union{LocalFieldElem, QadicFieldElem, RelFinFieldElem, AbsNumFieldOrderElem}, R::PolyRing) minpoly(R, a)
@deprecate charpoly(a::AbsNumFieldOrderElem, R::PolyRing) charpoly(R, a)

# Deprecated in 0.35.15
@deprecate MaximalOrder maximal_order
@deprecate Order order
@deprecate EquationOrder equation_order
