
@doc raw"""
Create a cyclic algebra.

The field is expected to be a cyclic extension over its base field,
and $sigma a generator of its Galois group. This creates the algebra commonly
denoted (K/k, σ, a). Its basis is chosen to be xᵢ⋅πʲ, where xᵢ is the basis
of K/k, and π a generating element, i.e. whose conjugation on K acts as σ and satisfies
πⁿ = a.
"""
function cyclic_algebra(
  fld::NumField{T},
  sigma::NumFieldHom{S, S},
  a::T
) where {T, S<:NumField{T}}
  k = base_field(fld)
  alpha = fld(a)
  d = degree(fld)
  sc = zeros(k, d^2, d^2, d^2)
  # Calculate xᵢ⋅πʲ⋅xₘ⋅πⁿ = xᵢ⋅σʲ(xₘ)⋅πʲ⁺ⁿ
  for (i, (xi, j)) in enumerate(Iterators.product(basis(fld), 1:d))
    c_sigma = sigma^(j - 1)
    for (m, (xm, n)) in enumerate(Iterators.product(basis(fld), 1:d))
      c_im = coordinates(xi * c_sigma(xm) * (j + n - 2 >= d ? alpha : 1))
      for (l, c) in enumerate(c_im)
        sc[i, m, rem(j + n - 2, d)*d+l] = c
      end
    end
  end
  one = [i == 1 ? 1 : 0 for i in 1:d^2]
  sca = structure_constant_algebra(k, sc; check=false, one=one)
  pi = d > 1 ? sca(collect(map(x -> x == d + 1 ? 1 : 0, 1:d^2))) : sca(a)
  cyc_fld_emb = hom(fld, sca, basis(sca)[d == 1 ? 1 : 2]; check=false)
  return CyclicAlgebra(sca, fld, cyc_fld_emb, sigma, pi, a)
end

@doc raw"""
Return the maximal, cyclic base field over which the cyclic algebra is represented.

Returns the cyclic field and its embedding in $c$.
"""
function maximal_cyclic_subfield(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return c.cyc_fld, c.cyc_fld_emb
end

"""
Return the canonical element which generates the cyclic algebra together with the cyclic field.
"""
function generating_element(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return c.pi
end

"""Return the base field of the cyclic algebra."""
function base_ring(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return base_ring(c.sca)::parent_type(T)
end

"""Return the cyclic algebra as a structure constant algebra."""
function structure_constant_algebra(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return StructureConstantAlgebra(c.sca)::StructureConstantAlgebra{T}
end

"""
Return the default basis.

If (xᵢ)ᵢ is the basis of the distinguished cyclic subfield, and π the
generating element, this basis is colex ordered (xᵢ⋅πʲ)ᵢⱼ.
"""
function basis(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return basis(c.sca)
end

function dim(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return dim(c.sca)
end

function one(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return c.sca(1)
end

function zero(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return c.sca(0)
end

function has_one(
  _::CyclicAlgebra{T, S},
) where {T, S}
  return true
end

function is_commutative(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return dim(c) == 1
end

"""
Create a ring homomorphism from a cyclic algebra.

# Parameters

- `g`: Image of the primitive element of the cyclic field.
- `p`: Image of the generating element of the cyclic algebra.

# Examples

```jldoctest
julia> QQx, x = QQ[:x];

julia> k, g = number_field(x^4 + x^3 + x^2 + x^1 + 1);

julia> _, phi = automorphism_group(k);

julia> c = cyclic_algebra(k, phi(first(gens(domain(phi)))), QQ(17));

julia> l, emb = Hecke.maximal_cyclic_subfield(c);

julia> p = Hecke.generating_element(c);

julia> aut = hom(c, c.sca, p * emb(gen(l)) / p, p);

```
"""
function hom(
  dom::CyclicAlgebra{T, S},
  codom::AbstractAssociativeAlgebra{U},
  g::AbstractAssociativeAlgebraElem{U},
  p::AbstractAssociativeAlgebraElem{U};
  check::Bool = true,
) where {T, S, U}
  d = degree(dom.cyc_fld)
  return hom(
    dom.sca,
    codom,
    collect(g^i * p^j for i in 0:d-1, j in 0:d-1)[:];
    check=check,
  )
end

"""
Determine whether the cyclic algebra splits.

See also [`is_split_with_map`](@ref).

# Examples

```jldoctest
julia> QQx, x = QQ[:x];

julia> k, g = number_field(x^2 + 1);

julia> is_split(cyclic_algebra(k, hom(k, k, -g), QQ(4)))
true
```
"""
function is_split(
  c::CyclicAlgebra{T, S},
) where {T, S}
  return first(is_norm(c.cyc_fld, c.a))
end

"""
Determine whether the cyclic algebra splits, and compute an iso to the matrix algebra.

If the algebra does not split, the null map is returned. This function is not pure.

See also [`is_split`](@ref).

# Examples

```jldoctest
julia> QQx, x = QQ[:x];

julia> k, g = number_field(x^2 + 1);

julia> c = cyclic_algebra(k, hom(k, k, -g), QQ(4));

julia> _, f = is_split_with_map(c);

julia> f(Hecke.generating_element(c))
[2 0; 0 -2]
```
"""
function is_split_with_map(
  c::CyclicAlgebra{T, S},
) where {T, S}
  d = degree(c.cyc_fld)
  g = gen(c.cyc_fld)
  k = c.cyc_fld
  mat_alg = matrix_algebra(base_field(k), d)
  emb1 = hom(k, mat_alg, mat_alg(representation_matrix(g)); check=false)
  emb2 = hom(k, mat_alg, mat_alg(representation_matrix(c.sigma(g))); check=false)
  sn = skolem_noether_conjugator(emb2, emb1; check=false)
  if first(local _, sol = is_norm(k, c.a / (sn^d)[1, 1]))
    m_pi = emb1(sol)*sn
    return true, hom(c.sca, mat_alg, collect(
      emb1(x)*m_pi^j
      for x in basis(k), j in 0:d - 1
    )[:]; check=false)
  end
  return false, hom(c.sca, mat_alg, [mat_alg(0) for _ in 1:d^2]; check=false)
end

"""
Determine whether the given cyclic algebras are isomorphic.
"""
function is_isomorphic(
  c1::CyclicAlgebra{T, S},
  c2::CyclicAlgebra{T, S},
) where {T, S}
  return first(is_isomorphic_with_map(c1, c2))
end

"""
Determine an isomorphism between two cyclic algebras.

Returns a tuple, the first element being `true` in case the algebras are isomorphic. In
this case the second tuple element is an isomorphism `c1` to `c2`, otherwise it is the
null map. This function is not pure.

See also [`is_isomorphic`](@ref).

# Examples

```jldoctest
julia> QQx, x = QQ[:x];

julia> k, g = number_field(x^2 - 5);

julia> c1 = cyclic_algebra(k, hom(k, k, -g), QQ(5));

julia> c2 = cyclic_algebra(k, hom(k, k, -g), QQ(5 * 3^2));

julia> first(is_isomorphic_with_map(c1, c2))
true
```

# References

Algorithm as described in [han07](@cite).
"""
function is_isomorphic_with_map(
  c1::CyclicAlgebra{T},
  c2::CyclicAlgebra{T};
  linearly_disjoint::Bool = false,
) where T
  d = degree(c1.cyc_fld)
  k, k1, k2 = parent(c1.a), c1.cyc_fld, c2.cyc_fld
  g1, g2 = gen(k1), gen(k2)
  a1, a2 = c1.a, c2.a

  if dim(c1.sca)!= dim(c2.sca)
    return false, hom(c1.sca, c2.sca, [c2.sca(0) for _ in 1:d^2]; check=false)
  end

  # Case: Base fields are isomorphic
  if !linearly_disjoint && first(local _, iso = is_isomorphic_with_map(k1, k2))
    i = 1
    while (iso((c1.sigma^i)(inv(iso)(g2))) != c2.sigma(g2))
      i += 1
    end
    if first(local _, x2 = is_norm(k2, a1/a2^i))
      return true, hom(
        c1.sca,
        c2.sca,
        collect(
          c2.cyc_fld_emb(iso(x)) * (c2.cyc_fld_emb(x2) * c2.pi)^i
          for (x, i) in Iterators.product(basis(k1), 0:d-1)
        )[:];
        check = false
      )
    end
    return false, hom(c1.sca, c2.sca, [c2.sca(0) for _ in 1:d^2]; check=false)
  end

  # Case: Maximally cyclic subfields are linearly disjoint.
  if linearly_disjoint || is_linearly_disjoint(k1, k2)
    # Solve the norm equation N₁(x₁) = a₁ for x₁ where N₁:k₁k₂ → k₂.
    k1k2, k1_to_k1k2, k2_to_k1k2 = _compositum(k1, k2)
    k2_abs, _ = absolute_simple_field(k2)
    k1k2_over_k2, k1k2_over_k2_to_k1k2 = relative_simple_extension(k1k2, k2_abs)
    if !first(local _, x1 = is_norm(k1k2_over_k2, base_field(k1k2_over_k2)(k2(a1))))
      return false, hom(c1.sca, c2.sca, [c2.sca(0) for _ in 1:d^2]; check=false)
    end
    x1 = k1k2_over_k2_to_k1k2(x1)
    # Reset the base field of the compositum in the relative field case.
    # One cannot compose the resulting maps since one has to ensure that
    # the inclusion maps k⟶ k₁⟶ k₁k₂ and k⟶ k₂⟶ k₁k₂ are the same.
    if k1 isa RelSimpleNumField
      k1k2, as_rel = relative_simple_extension(k1k2, k)
      _, k1_to_k1k2 = is_subfield(k1, k1k2)
      _, k2_to_k1k2 = is_subfield(k2, k1k2)
      x1 = inv(as_rel)(x1)
    end
    # Solve σ₁(x)σ₂(y) = xy for x in k₁k₂ ("bicyclic Hilbert 90").
    # First reinterprete σᵢ as maps of k₁k₂ using the "tensor basis".
    tb = Iterators.product(basis(k1), basis(k2))
    bb = collect(map(((a,b),)-> k1_to_k1k2(a) * k2_to_k1k2(b), tb))[:]
    tensor_ctx = solve_init(basis_matrix(bb))
    tensor_g12 = solve(tensor_ctx, coordinates(gen(k1k2)))
    sigma1_g12 = mapreduce(prod, +, zip((k1_to_k1k2(c1.sigma(a)) * k2_to_k1k2(b) for (a, b) in tb), tensor_g12))
    sigma2_g12 = mapreduce(prod, +, zip((k1_to_k1k2(a) * k2_to_k1k2(c2.sigma(b)) for (a, b) in tb), tensor_g12))
    sigma1 = hom(k1k2, k1k2, sigma1_g12)
    sigma2 = hom(k1k2, k1k2, sigma2_g12)
    # Take an element x in the kernel of σ₁(x) - xx₁/σ₂(x₁).
    proj = (sigma1(a) - a * x1 / sigma2(x1) for a in basis(k1k2))
    if is_empty(local ker = kernel(basis_matrix(collect(proj))))
      return false, hom(c1.sca, c2.sca, [c2.sca(0) for _ in 1:d^2]; check=false)
    end
    x = k1k2(ker[1, :])
    @assert sigma1(x) - x * x1/sigma2(x1) == 0

    # Solve norm equation N₂(y) = N₂(x)/a₂ for y.
    n2_y = Iterators.reduce(1:d; init=k1k2(1)) do prev, _ x * sigma2(prev) end
    if !first(local _, y = is_norm(k2, k(n2_y)/a2))
      return false, hom(c1.sca, c2.sca, [c2.sca(0) for _ in 1:d^2]; check=false)
    end
    x2 = k2_to_k1k2(y) / x

    # Bicyclic Hilbert 90 solved.
    @assert x1/sigma2(x1) == x2/sigma1(x2)
    @assert norm(x1) == a1^d
    @assert norm(x2) == inv(a2)^d

    # Left regular embedding of c₁ in Mₙ²(k).
    left = _left_regular_representation(c1)
    mm = codomain(left)
    # Embedding φ₁ of c₁ into c₁⊗c₂ᵒᵖ = Mₙ²(k) using the isomorphism constructed above.
    alpha = solve(tensor_ctx, coordinates(x1))
    _, s1 = is_split_with_map(cyclic_algebra(k1, c1.sigma, k(1)))
    _, s2 = is_split_with_map(cyclic_algebra(k2, c2.sigma, k(1)))

    function add_kronecker_prod!(trg, a, b)
      d = number_of_rows(a)
      for i in 1:d:d^2-1, j in 1:d:d^2-1
        trg[i:i+d-1, j:j+d-1] .+= (a * b[div(i, d)+1, div(j, d)+1])
      end
    end

    # Calculate image φ₁(g₁) of primitive element of k₁ in Mₙ²(k).
    phi1_g1 = zero_matrix(k, d^2, d^2)
    add_kronecker_prod!(phi1_g1, matrix(s1(c1.cyc_fld_emb(g1))), identity_matrix(k, d))
    # Calculate image φ₁(π₁) of generating element of c₁ in Mₙ²(k).
    phi1_pi1 = zero_matrix(k, d^2, d^2)
    for i in 1:d
      add_kronecker_prod!(
        phi1_pi1,
        matrix(s1(c1.cyc_fld_emb(k1(alpha[(i-1)*d+1:i*d])) * c1.pi)),
        matrix(s2(c2.cyc_fld_emb(g2^(i - 1))))
      )
    end
    phi1 = hom(c1, mm, mm(phi1_g1), mm(phi1_pi1); check=false)
    # Get conjugating element of the two embeddings.
    sn = skolem_noether_conjugator(left, phi1; check=false)

    # Construct the image under the anti-embedding.
    alphas = collect(Iterators.accumulate(1:d; init = k1k2(1)) do prev, _ x2 * sigma2(prev) end)
    mm_s = zero_matrix(k, d^2, d^4)
    for j in 0:d-1, i in 0:d-1
      column = zero_matrix(k, d^2, d^2)
      # Get coefficients of in terms of tensor basis.
      split = solve(
        basis_matrix(bb),
        coordinates(k2_to_k1k2(k2(a2) * (c2.sigma^(d - j))(g2^i)) * alphas[d-j])
      )
      for u in 1:d
        add_kronecker_prod!(
          column,
          matrix(s1(c1.cyc_fld_emb(k1(split[d*(u-1)+1:d*u])))),
          matrix(s2(c2.cyc_fld_emb(g2^(u - 1))) * s2(c2.pi)^(d - j)),
        )
      end
      column = matrix(sn) * column
      # Write the image into the linear equation.
      for t in 1:d^2
        mm_s[i+j*d+1, (t-1)*d^2+1:t*d^2] = column[t, :]
      end
    end
    md4_ctx = solve_init(mm_s)

    # Construct the image of generating elements under right regular representation ρ.

    # Solve ρ(g₁) sn = sn φ₂.
    x_mm = zero_matrix(k, 1, d^4)
    right_g1 = zero_matrix(k, d^2, d^2)
    for j in 0:d-1
      right_g1[j*d+1:j*d+d, j*d+1:j*d+d] = reshape([c for i in 0:d-1 for c in coordinates(g1^i * (c1.sigma^j)(g1))], d, d)
    end
    lhs = right_g1 * matrix(sn)
    for i in 1:d^2
      x_mm[1, (i-1)*d^2+1:(i-1)*d^2+d^2] = lhs[i, :]
    end
    im_g = solve(md4_ctx, x_mm; side=:left)
    im_g = mapreduce(prod, +, zip(basis(c2.sca), im_g))

    right_pi1 = zero_matrix(k, d^2, d^2)
    right_pi1[d+1:d^2, 1:d^2-d] = identity_matrix(k, d^2 - d)
    right_pi1[1:d, d^2-d+1:d^2] = diagonal_matrix(a1, d, d)
    lhs = right_pi1 * matrix(sn)
    for i in 1:d^2
      x_mm[1, (i-1)*d^2+1:(i-1)*d^2+d^2] = lhs[i, :]
    end
    im_pi = solve(md4_ctx, x_mm; side=:left)
    im_pi = mapreduce(prod, +, zip(basis(c2.sca), im_pi))
    return true, hom(c1, c2.sca, im_g, im_pi; check=false)
  end

  # Case: Maximally cyclic subfields have nonempty intersection.
  # Get largest common subfield k₀.
  local k0, k0_to_k1
  for (subfld, subfld_to_k1) in Iterators.rest(sort(subfields(k1); by=degree ∘ first, rev=true),2)
    if first(is_subfield(subfld, k2))
      k0, k0_to_k1 = subfld, subfld_to_k1
      break
    end
  end
  # Interpret centralizers of kᵢ as cyclic algebra over k₀.
  k1_over_k0, k1_over_k0_to_k1 = relative_simple_extension(k1, k0)
  k2_over_k0, k2_over_k0_to_k2 = relative_simple_extension(k2, k0)
  dz = degree(k1_over_k0)
  d0 = degree(k0)
  sigma1 = hom(k1_over_k0, k1_over_k0, k1_over_k0_to_k1\ (c1.sigma^d0)(k1_over_k0_to_k1(gen(k1_over_k0))))
  sigma2 = hom(k2_over_k0, k2_over_k0, k2_over_k0_to_k2\ (c2.sigma^d0)(k2_over_k0_to_k2(gen(k2_over_k0))))
  z1 = cyclic_algebra(k1_over_k0, sigma1, k0(c1.a))
  z2 = cyclic_algebra(k2_over_k0, sigma2, k0(c2.a))
  if !first(local _, iso = is_isomorphic_with_map(z1, z2; linearly_disjoint=true))
    return false, hom(c1.sca, c2.sca, [c2.sca(0) for _ in 1:d^2]; check=false)
  end
  # Test for isomorphism between generalized cyclic algebras over the centralizers.
  # Since z₂ and c₂ are defined over different base fields, apply embedding manually.
  function z2_to_c2(elem)
    coos = matrix(basis_matrix([elem]))[1, :]
    res = c2.sca(0)
    for i in 1:dz
      res += c2.cyc_fld_emb(k2_over_k0_to_k2(k2_over_k0(coos[dz*(i-1)+1:dz*(i-1)+dz]))) * c2.pi^(d0 * (i - 1))
    end
    return res
  end

  # Embedding of z₂ into c₂ given by χ∘σ₁∘χ⁻¹, where χ is the iso z₁→z₂
  # and σ₁ is an extension of σ to the centralizer.
  im = c2.sca(0)
  ims = typeof(im)[]
  for i in 0:dz - 1, b in basis(c2.cyc_fld)
     im = inv(iso)(z2.cyc_fld_emb(k2_over_k0_to_k2\ (b)) * z2.pi^i)
     coos = matrix(basis_matrix([im]))[1, :]
     for j in 1:dz:dim(z1.sca) - 1
       coos[j:j+dz-1] = coordinates(k1_over_k0_to_k1\ (c1.sigma(k1_over_k0_to_k1(k1_over_k0(coos[j:j+dz-1])))))
     end
     im = iso(z1.sca(coos))
     push!(ims, z2_to_c2(im))
  end
  z2b = collect(b for (i, b) in enumerate(basis(c2.sca)) if rem(div(i - 1, d), d0) == 0)[:]
  z2_over_k, emb2 = _subalgebra(c2.sca, z2b)
  emb1 = hom(z2_over_k, c2.sca, ims; check=false)

  sn = skolem_noether_conjugator(emb1, emb2; check=false)
  u = z2_to_c2(iso(z1.pi)) / sn^d0
  # Result must be in base field k of algebra.
  if !first(local _, nu = is_norm(k0, k(u)))
    return false, hom(c1.sca, c2.sca, [c2.sca(0) for _ in 1:d^2]; check=false)
  end
  img = z2_to_c2(iso(z1.cyc_fld_emb(gen(z1.cyc_fld))))
  return true, hom(c1, c2.sca, img, c2.cyc_fld_emb(k2_over_k0_to_k2(k2_over_k0(nu))) * sn; check=false)
end

function _left_regular_representation(
  c::CyclicAlgebra{T, S},
) where {T, S}
  k = c.cyc_fld
  d = degree(k)
  g_mm = zero_matrix(base_field(k), d^2, d^2)
  g = gen(k)
  # Representation via action from left on column vector
  g_m = transpose(representation_matrix(g))
  for i in 1:d:d^2-1
    g_mm[i:i+d-1, i:i+d-1] = g_m
  end
  pi_mm = zero_matrix(base_field(k), d^2, d^2)
  s_m = reshape([x for i in 0:d-1 for x in coordinates(c.sigma(g^i))], d, d)
  for i in 1:d:d^2-d
    pi_mm[i+d:i+d+d-1, i:i+d-1] = s_m
  end
  pi_mm[1:d, d^2-d+1:d^2] = c.a .* s_m
  mm = matrix_algebra(base_field(k), d^2)
  return hom(c, mm, mm(g_mm), mm(pi_mm); check=false)
end


"""
Given two relative simple number fields, return their compositum with the embeddings.

The compositum is returned as an absolute number field. As with `_compositum`, the condition
of normality on either of the fields is not checked.
"""
function _compositum(
  k1::RelSimpleNumField,
  k2::RelSimpleNumField,
)
  k1_abs, k1_abs_to_k1 = absolute_simple_field(k1)
  k2_abs, k2_abs_to_k2 = absolute_simple_field(k2)
  k1k2, k1_to_k1k2, k2_to_k1k2 = compositum(k1_abs, k2_abs)
  k1_to_k1_abs = inv(k1_abs_to_k1)
  k2_to_k2_abs = inv(k2_abs_to_k2)
  return k1k2,
    hom(k1, k1k2, k1_to_k1k2(k1_to_k1_abs(k1(gen(base_field(k1))))), k1_to_k1k2(k1_to_k1_abs(gen(k1)))),
    hom(k2, k1k2, k2_to_k1k2(k2_to_k2_abs(k2(gen(base_field(k2))))), k2_to_k1k2(k2_to_k2_abs(gen(k2))))
end

function _compositum(
  k1::AbsSimpleNumField,
  k2::AbsSimpleNumField,
)
  return compositum(k1, k2)
end
