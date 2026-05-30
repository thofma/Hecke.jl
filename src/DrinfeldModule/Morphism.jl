################################################################################
#
#  DrinfeldModule/Morphism.jl : Morphisms between Drinfeld modules
#
#  A morphism phi -> psi is an Ore polynomial f in K{tau} such that
#    f * phi_T = psi_T * f
#
#  The zero polynomial defines the zero morphism (which is valid for any
#  domain and codomain with the same base).
#
################################################################################

################################################################################
#
#  Constructor
#
################################################################################

@doc raw"""
    drinfeld_module_morphism(phi::DrinfeldModule{T}, psi::DrinfeldModule{T},
                             f::OrePoly{T}) -> DrinfeldModuleMorphism{T}

Construct the morphism from `phi` to `psi` defined by the Ore polynomial `f`.

The Ore polynomial must satisfy `f * phi_T = psi_T * f`.  The zero polynomial
is always accepted and gives the zero morphism.
"""
function drinfeld_module_morphism(phi::DrinfeldModule{T},
                                  psi::DrinfeldModule{T},
                                  f::OrePoly{T}) where {T}
  @req function_ring(phi) === function_ring(psi) "domain and codomain must have the same function ring"
  R_phi = ore_polynomial_ring(phi)
  @req parent(f) === R_phi "Ore polynomial must be in K{tau} of the domain"
  if !iszero(f)
    phi_T = gen(phi)
    # Coerce psi_T into R_phi (same K and q, possibly different OrePolyRing object)
    psi_coeffs = coefficients(gen(psi))
    psi_T_in_R = OrePoly{T}(R_phi, psi_coeffs)
    @req f * phi_T == psi_T_in_R * f "Ore polynomial does not define a morphism (f*phi_T != psi_T*f)"
  end
  return DrinfeldModuleMorphism{T}(phi, psi, f)
end

################################################################################
#
#  Accessors
#
################################################################################

@doc raw"""
    domain(m::DrinfeldModuleMorphism) -> DrinfeldModule

Return the domain of the morphism `m`.
"""
function domain(m::DrinfeldModuleMorphism)
  return m.domain
end

@doc raw"""
    codomain(m::DrinfeldModuleMorphism) -> DrinfeldModule

Return the codomain of the morphism `m`.
"""
function codomain(m::DrinfeldModuleMorphism)
  return m.codomain
end

@doc raw"""
    ore_polynomial(m::DrinfeldModuleMorphism) -> OrePoly

Return the Ore polynomial defining the morphism `m`.
"""
function ore_polynomial(m::DrinfeldModuleMorphism)
  return m.ore_poly
end

@doc raw"""
    degree(m::DrinfeldModuleMorphism) -> Int

Return the degree of the defining Ore polynomial of `m`, or `-1` if `m` is
the zero morphism.
"""
function degree(m::DrinfeldModuleMorphism)
  return degree(ore_polynomial(m))
end

################################################################################
#
#  Predicates
#
################################################################################

@doc raw"""
    is_zero(m::DrinfeldModuleMorphism) -> Bool

Return `true` if `m` is the zero morphism.
"""
function is_zero(m::DrinfeldModuleMorphism)
  return iszero(ore_polynomial(m))
end

@doc raw"""
    is_identity(m::DrinfeldModuleMorphism) -> Bool

Return `true` if `m` is the identity morphism.
"""
function is_identity(m::DrinfeldModuleMorphism)
  return isone(ore_polynomial(m))
end

@doc raw"""
    is_isogeny(m::DrinfeldModuleMorphism) -> Bool

Return `true` if `m` is an isogeny (i.e., nonzero).
"""
function is_isogeny(m::DrinfeldModuleMorphism)
  return !is_zero(m)
end

@doc raw"""
    is_isomorphism(m::DrinfeldModuleMorphism) -> Bool

Return `true` if `m` is an isomorphism, i.e., the defining Ore polynomial
is a nonzero constant (degree 0).
"""
function is_isomorphism(m::DrinfeldModuleMorphism)
  f = ore_polynomial(m)
  return !iszero(f) && degree(f) == 0
end

@doc raw"""
    is_endomorphism(m::DrinfeldModuleMorphism) -> Bool

Return `true` if `m` is an endomorphism (domain equals codomain).
"""
function is_endomorphism(m::DrinfeldModuleMorphism)
  return domain(m) == codomain(m)
end

################################################################################
#
#  Arithmetic
#
################################################################################

@doc raw"""
    +(m::DrinfeldModuleMorphism{T}, n::DrinfeldModuleMorphism{T})
      -> DrinfeldModuleMorphism{T}

Return the sum of morphisms `m` and `n` (requires same domain and codomain).
"""
function Base.:+(m::DrinfeldModuleMorphism{T},
                 n::DrinfeldModuleMorphism{T}) where {T}
  @req domain(m) == domain(n) "domains must be equal"
  @req codomain(m) == codomain(n) "codomains must be equal"
  f = ore_polynomial(m) + ore_polynomial(n)
  return DrinfeldModuleMorphism{T}(domain(m), codomain(m), f)
end

@doc raw"""
    *(m::DrinfeldModuleMorphism{T}, n::DrinfeldModuleMorphism{T})
      -> DrinfeldModuleMorphism{T}

Return the composition `n ∘ m` (first `m`, then `n`).  Requires
`codomain(m) == domain(n)`.
"""
function Base.:*(m::DrinfeldModuleMorphism{T},
                 n::DrinfeldModuleMorphism{T}) where {T}
  @req codomain(m) == domain(n) "codomain of first must equal domain of second"
  # Composition n∘m: ore poly is ore_poly(n) * ore_poly(m)
  fm = ore_polynomial(m)
  fn = ore_polynomial(n)
  # Both fm and fn may live in different OrePolyRing objects (same K, q).
  # Use fm's ring as the common ring.
  R = parent(fm)
  fn_in_R = OrePoly{T}(R, coefficients(fn))
  f = fn_in_R * fm
  return DrinfeldModuleMorphism{T}(domain(m), codomain(n), f)
end

@doc raw"""
    inverse(m::DrinfeldModuleMorphism{T}) -> DrinfeldModuleMorphism{T}

Return the inverse of the isomorphism `m`.  Raises an error if `m` is not
an isomorphism.
"""
function Base.inv(m::DrinfeldModuleMorphism{T}) where {T}
  @req is_isomorphism(m) "morphism is not an isomorphism"
  u = constant_coefficient(ore_polynomial(m))
  u_inv = inv(u)
  R = ore_polynomial_ring(codomain(m))
  f_inv = R(u_inv)
  return DrinfeldModuleMorphism{T}(codomain(m), domain(m), f_inv)
end

################################################################################
#
#  Equality and hashing
#
################################################################################

function ==(m::DrinfeldModuleMorphism{T}, n::DrinfeldModuleMorphism{T}) where {T}
  domain(m) == domain(n) || return false
  codomain(m) == codomain(n) || return false
  # Compare coefficient vectors directly (avoids parent identity issue)
  return coefficients(ore_polynomial(m)) == coefficients(ore_polynomial(n))
end

function Base.hash(m::DrinfeldModuleMorphism, h::UInt)
  b = 0x7e3a2b8c6f1d4059 % UInt
  return xor(hash(ore_polynomial(m), xor(hash(domain(m), h))), b)
end

################################################################################
#
#  Convenience constructors on DrinfeldModule
#
################################################################################

@doc raw"""
    hom(phi::DrinfeldModule{T}, psi::DrinfeldModule{T}, f::OrePoly{T})
      -> DrinfeldModuleMorphism{T}

Construct the morphism from `phi` to `psi` defined by the Ore polynomial `f`.
"""
function hom(phi::DrinfeldModule{T}, psi::DrinfeldModule{T},
             f::OrePoly{T}) where {T}
  return drinfeld_module_morphism(phi, psi, f)
end

@doc raw"""
    hom(phi::DrinfeldModule{T}, f::OrePoly{T}) -> DrinfeldModuleMorphism{T}

Construct an endomorphism of `phi` defined by the Ore polynomial `f`.
"""
function hom(phi::DrinfeldModule{T}, f::OrePoly{T}) where {T}
  return drinfeld_module_morphism(phi, phi, f)
end

################################################################################
#
#  Show
#
################################################################################

function Base.show(io::IO, m::DrinfeldModuleMorphism)
  io = pretty(io)
  print(io, "Drinfeld module morphism")
  println(io)
  print(io, Indent())
  print(io, "from  ", domain(m))
  println(io)
  print(io, "to    ", codomain(m))
  println(io)
  print(io, "given by  ", ore_polynomial(m))
  print(io, Dedent())
end
