################################################################################
#
#  HypellCrv/Isomorphisms.jl : Isomorphisms of hyperelliptic curves
#
# References:
#
# [LRS13] R. Lercier, C. Ritzenthaler, J. Sijsling,
#         "Fast computation of isomorphisms of hyperelliptic curves and
#         explicit Galois descent",
#         Proceedings of ANTS-X, Open Book Series 1 (2013), pp. 463-486.
#         https://doi.org/10.2140/obs.2013.1.463
#
# [Igu60] J.-I. Igusa,
#         "Arithmetic variety of moduli for genus two",
#         Ann. Math. 72 (1960), 612-649.
#
################################################################################

################################################################################
#
#  Types
#
################################################################################

@doc raw"""
    HypellCrvIsom{T}

An isomorphism between two hyperelliptic curves.

Given hyperelliptic curves $C_1 \colon y^2 = f_1(x)$ and $C_2 \colon y^2 = f_2(x)$
over a field $K$, an isomorphism $C_1 \to C_2$ is given by
$$x \mapsto \frac{ax + b}{cx + d}, \qquad y \mapsto \frac{u \cdot y}{(cx + d)^{g+1}}$$
where $[a, b, c, d] \in K^4$ with $ad - bc \neq 0$, $u \in K^*$, and $g$ is the
genus. When the input curves have an $h \neq 0$ term, a $y$-shift polynomial $v$
is also stored.
"""
mutable struct HypellCrvIsom{T}
  domain::HypellCrv{T}
  codomain::HypellCrv{T}
  a::T
  b::T
  c::T
  d::T
  u::T
  v::PolyRingElem{T}

  function HypellCrvIsom{T}(C1::HypellCrv{T}, C2::HypellCrv{T},
                             a::T, b::T, c::T, d::T, u::T,
                             v::PolyRingElem{T}) where T
    @req a*d - b*c != 0 "Matrix [a, b; c, d] must be invertible"
    m = new{T}()
    m.domain = C1
    m.codomain = C2
    m.a = a
    m.b = b
    m.c = c
    m.d = d
    m.u = u
    m.v = v
    return m
  end

  # Uninitialised sentinel used when no isomorphism exists
  HypellCrvIsom{T}() where T = new{T}()
end

################################################################################
#
#  Accessors
#
################################################################################

domain(m::HypellCrvIsom) = m.domain
codomain(m::HypellCrvIsom) = m.codomain

@doc raw"""
    isomorphism_data(m::HypellCrvIsom) -> (a, b, c, d, u, v)

Return the defining data of the isomorphism `m`. The isomorphism maps
$(x, y) \mapsto \left(\frac{ax+b}{cx+d},\; \frac{u \cdot y + v(x)}{(cx+d)^{g+1}}\right)$.
"""
function isomorphism_data(m::HypellCrvIsom)
  return m.a, m.b, m.c, m.d, m.u, m.v
end

################################################################################
#
#  Evaluate / apply an isomorphism to a point
#
################################################################################

@doc raw"""
    (m::HypellCrvIsom)(P::HypellCrvPt) -> HypellCrvPt

Apply the isomorphism `m` to the point `P`.
"""
function (m::HypellCrvIsom{T})(P::HypellCrvPt{T}) where T
  @req parent(P) === domain(m) "Point must lie on the domain"
  C2 = codomain(m)
  g = genus(C2)
  a, b, c, d, u, v = isomorphism_data(m)

  if is_infinite(P)
    # Point at infinity: send (x:y:z) = (1:0:0) or (1:+-1:0)
    # For the standard point at infinity on y^2 = f(x) of even degree 2g+2,
    # the image under x -> (ax+b)/(cx+d) as c != 0 maps infinity to a/c.
    # We let the curve constructor figure out the correct projective point.
    # For now handle the most common case: map back through affine coords.
    K = base_field(C2)
    if c == 0
      # x -> (ax+b)/d, so infinity maps to infinity
      x2 = one(K)
      y2 = iszero(u) ? zero(K) : u * P[2]
      z2 = zero(K)
      return C2([x2, y2, z2]; check = false)
    else
      # infinity (z=0 in x-direction) maps to x = a/c (finite point)
      x0 = a * inv(c)
      f2, h2 = hyperelliptic_polynomials(C2)
      rhs = f2(x0)
      # y^2 + h2(x0)*y - rhs = 0
      Kt, t = polynomial_ring(base_field(C2), "t"; cached = false)
      ypoly = t^2 + h2(x0)*t - rhs
      ys = roots(ypoly)
      if isempty(ys)
        error("Image of point at infinity has no rational y-coordinate in codomain")
      end
      return C2([x0, ys[1]])
    end
  end

  x1 = P[1]
  y1 = P[2]
  denom = c * x1 + d
  @req !iszero(denom) "Denominator c*x + d is zero at this point"
  x2 = (a * x1 + b) * inv(denom)
  y2 = (u * y1 + v(x1)) * inv(denom)^(g + 1)
  return C2([x2, y2])
end

################################################################################
#
#  Inverse of an isomorphism
#
################################################################################

@doc raw"""
    inv(m::HypellCrvIsom) -> HypellCrvIsom

Return the inverse isomorphism.
"""
function Base.inv(m::HypellCrvIsom{T}) where T
  a, b, c, d, u, v = isomorphism_data(m)
  # Inverse of Mobius x -> (ax+b)/(cx+d) is x -> (dx-b)/(-cx+a)
  # i.e. matrix [d, -b; -c, a]
  # For y: y2 = (u*y1 + v(x1)) / (cx1+d)^(g+1)
  #   => y1 = (y2*(cx1+d)^(g+1) - v(x1)) / u
  # In terms of x2 = (ax1+b)/(cx1+d):
  #   cx1+d = a/(cx2 - ... ) ... simplest: u_inv = inv(u), v_inv = -v(x1)/u expressed as poly in x2
  # For the h=0 case (v=0), this simplifies nicely:
  # y2 = u*y1/(cx1+d)^(g+1), and (-cx2+a) = (ad-bc)/(cx1+d)
  # so (cx1+d)^(g+1) = (det)^(g+1) / (-cx2+a)^(g+1) where det = ad-bc
  # thus y1 = y2 * (-cx2+a)^(g+1) / (u * det^(g+1))
  # i.e. new u_inv = 1/(u * det^(g+1)), new mat = [d,-b;-c,a]
  det = a*d - b*c
  g = genus(domain(m))
  K = base_field(domain(m))
  Kx = parent(v)
  u_inv = inv(u * det^(g + 1))
  # v_inv: if v != 0 this is more involved; for v=0 it is 0.
  # General formula: x1 = (d*x2 - b)/(-c*x2 + a)
  # v_inv(x2) = -v(x1)/u * (-c*x2+a)^(... ) -- complicated rational expression.
  # Since we only build isomorphisms with v=0 in is_isomorphic (char != 2),
  # we assert v == 0 here for now and leave the general case for future work.
  @req iszero(v) "inv not implemented for isomorphisms with non-zero v (h != 0 case)"
  v_inv = zero(Kx)
  return HypellCrvIsom{T}(codomain(m), domain(m), d, -b, -c, a, u_inv, v_inv)
end

################################################################################
#
#  Composition of isomorphisms
#
################################################################################

@doc raw"""
    compose(m1::HypellCrvIsom, m2::HypellCrvIsom) -> HypellCrvIsom

Return the composition `m2 ∘ m1`, i.e. first apply `m1` then `m2`.
"""
function compose(m1::HypellCrvIsom{T}, m2::HypellCrvIsom{T}) where T
  @req codomain(m1) === domain(m2) "Codomain of m1 must equal domain of m2"
  a1, b1, c1, d1, u1, v1 = isomorphism_data(m1)
  a2, b2, c2, d2, u2, v2 = isomorphism_data(m2)
  # Compose Mobius: (m2 o m1)(x) = m2(m1(x))
  # m1: x -> (a1*x+b1)/(c1*x+d1)
  # m2: x -> (a2*x+b2)/(c2*x+d2)
  # (m2 o m1)(x) = (a2*(a1*x+b1) + b2*(c1*x+d1)) / (c2*(a1*x+b1) + d2*(c1*x+d1))
  a = a2*a1 + b2*c1
  b = a2*b1 + b2*d1
  c = c2*a1 + d2*c1
  d = c2*b1 + d2*d1
  u = u1 * u2
  # v: again restrict to v1=v2=0 for now
  @req iszero(v1) && iszero(v2) "compose not implemented for isomorphisms with non-zero v"
  v = zero(parent(v1))
  return HypellCrvIsom{T}(domain(m1), codomain(m2), a, b, c, d, u, v)
end

################################################################################
#
#  Helper: transform a polynomial by a GL2 matrix
#
################################################################################

# transform_polynomial(f, n, [a,b,c,d]):
# Treats f as the dehomogenization of a degree-n binary form F(X,Z) = sum_i coeff(f,i)*X^i*Z^(n-i).
# Returns the dehomogenization of F(a*X+b*Z, c*X+d*Z) as a univariate polynomial.
function _transform_polynomial(f::PolyRingElem, n::Int, mat::Vector)
  a, b, c, d = mat
  R = parent(f)
  x = gen(R)
  ax_plus_b = a*x + b
  cx_plus_d = c*x + d
  result = zero(R)
  for i in 0:n
    ci = (i <= degree(f)) ? coeff(f, i) : zero(base_ring(f))
    result += ci * ax_plus_b^i * cx_plus_d^(n - i)
  end
  return result
end


@doc raw"""
    hyperelliptic_transform(C1::HypellCrv{T}, t::Vector{T}, u::T = one(base_field(C1)), 
  v::PolyRingElem = zero(polynomial_ring(base_field(C1))[1])) where T

Consider the morphism phi of hyperelliptic curves C1 -> C2.
(x: y: z) -> (ax + bz : uy + v_hom(x, z) : cx + dz)
where t = [a, b, c, d] and v_hom is the homogenization of v.

Return C2, phi and inv(phi).

"""
function hyperelliptic_transform(C1::HypellCrv{T}, t::Vector{T}, u::T = one(base_field(C1)), 
  v::PolyRingElem = zero(polynomial_ring(base_field(C1))[1])) where T
  K = base_field(C1)
  @req is_unit(u) "u needs to be a unit"

  a, b, c, d = t
  t_shift = [d, -b, -c, a]
  f, h = hyperelliptic_polynomials(C1)
  g = genus(C1)
  d1 = 2*g + 2
  d2 = g + 1

  det = (a*d - b*c)^(-g+1)

  f_new = _transform_polynomial(f, d1, t_shift)
  h_new = _transform_polynomial(h, d2, t_shift)
  v_new = _transform_polynomial(v, d2, t_shift)

  h2 = (u*h_new - 2*v_new) * det
  f2 = (u^2*f_new + (u*h_new - v_new)*v_new) *det^2

  C2 = hyperelliptic_curve(f2, h2)
  phi =  HypellCrvIsom{T}(C1, C2, a, b, c, d, u, v)
  return C2, phi, inv(phi)
end


################################################################################
#
#  Helper: adjoin a root of an irreducible polynomial
#
################################################################################

# _adjoin_root(K, f) -> (L, embed, root)
# Returns an extension L/K, an embedding K -> L, and the image of the
# generator (a root of f in L).
function _adjoin_root(K, f::PolyRingElem)
  if K isa QQField || K isa NumField
    L, r = number_field(f; cached = false)
    embed = x -> L(x)
    return L, embed, r
  end
  if K isa FqField
    L, h = Nemo._residue_field(f)
    Kx = parent(f)
    return L, a -> h(Kx(a)), h(gen(Kx))
  end
  error("_adjoin_root not yet implemented for base field of type $(typeof(K)). Please implement this stub.")
end

################################################################################
#
#  Helper: coordinates of an element of L over K
#
################################################################################

# Returns the coordinates of x in L as a vector of K-elements,
# in the same basis used by _adjoin_root.
function _coords(x, L, K)
  if K isa QQField || K isa NumField
    return coordinates(x)
  end
  if K isa FqField
    return [coeff(x, i) for i in 0:degree(L)-1]
  end
  error("_coords not yet implemented for field of type $(typeof(L)). This stub must be filled together with _adjoin_root.")
end

################################################################################
#
#  Helper: roots of a polynomial over an extension field
#
################################################################################

# Returns all roots of g in the field L (with L returned by _adjoin_root).
function _roots_in(g::PolyRingElem, L, embed)
  # Change coefficients to L and call roots
  Lx, _ = polynomial_ring(L, cached = false)
  g_L = map_coefficients(embed, g; parent = Lx)
  return roots(g_L)
end

################################################################################
#
#  GL2-equivalence test
#
################################################################################

@doc raw"""
    is_gl2_equivalent(f1, f2, n) -> (Bool, Vector{Vector})

Given univariate polynomials `f1`, `f2` over a field `K` with `deg(fi) ∈ {n-1, n}`,
considered as dehomogenizations of binary forms of degree `n`, determine whether
they lie in the same $\mathrm{GL}(2,K)$-orbit modulo scalars.

Returns a boolean and a list of matrices `[a, b, c, d]` (as vectors) such that
`f2(x) = const * _transform_polynomial(f1, n, [a,b,c,d])` for each returned matrix.

This implements the naive variant of the algorithm in [LRS13], Section 3:
factor both forms, adjoin a root of an irreducible factor, enumerate image
roots, and recover the Mobius matrix by solving a linear system.
"""
function is_gl2_equivalent(f1::PolyRingElem{T}, f2::PolyRingElem{T}, n::Int) where T
  K = base_ring(f1)
  @req base_ring(f2) === K "Polynomials must have the same base ring"
  @req n >= 4 "n must be at least 4"
  @req degree(f1) in (n-1, n) && degree(f2) in (n-1, n) "deg(fi) must be n or n-1"

  # Factor both polynomials (squarefree assumed for hyperelliptic curves)
  fact1 = collect(factor(f1))   # Vector of (poly, exp) pairs
  fact2 = (f1 == f2) ? fact1 : collect(factor(f2))

  # Build degree multisets, including a virtual degree-1 factor for the
  # point at infinity when deg(f) < n.
  degs1 = sort([degree(p) for (p, _) in fact1])
  if degree(f1) < n
    push!(degs1, 1)
    sort!(degs1)
  end
  degs2 = sort([degree(p) for (p, _) in fact2])
  if degree(f2) < n
    push!(degs2, 1)
    sort!(degs2)
  end

  if degs1 != degs2
    return false, Vector{T}[]
  end

  d = maximum(degs1)   # largest degree of an irreducible factor
  result = Vector{T}[]

  # Helper: check if transform_polynomial(f1, n, t) is proportional to f2
  _check_and_add = function(t)
    f3 = _transform_polynomial(f1, n, t)
    lc2 = leading_coefficient(f2)
    lc3 = leading_coefficient(f3)
    if f3 * lc2 == f2 * lc3
      push!(result, t)
    end
  end

  if d >= 3
    # Construct L = K[alpha] / (irred factor of f1 of degree d)
    f_irred = first(p for (p, _) in fact1 if degree(p) == d)
    L, embed, rf = _adjoin_root(K, f_irred)  # rf is the root of f_irred in L

    e1 = _coords(one(L), L, K)   # coords of 1
    ex = _coords(-rf, L, K)      # coords of -rf

    for (g_poly, _) in fact2
      degree(g_poly) == d || continue
      for root in _roots_in(g_poly, L, embed)
        ey   = _coords(root, L, K)       # coords of root
        exy  = _coords(-rf * root, L, K) # coords of -rf*root

        data = T[c for i in 1:d for c in (ey[i], e1[i], exy[i], ex[i])]
        M = matrix(K, d, 4, data)
        ker = kernel(M; side = :right)
        if ncols(ker) == 1
          t = T[ker[i, 1] for i in 1:4]
          _check_and_add(t)
        end
      end
    end
  elseif d == 2
    f_irred = first(p for (p, _) in fact1 if degree(p) == d)
    L1, embed1, rf = _adjoin_root(K, f_irred)

    sorted_degs = sort(degs1; rev = true)
    d1 = sorted_degs[2]  # second-largest degree of a factor  # second largest (possibly equal to d=2)

    if d1 == 2
      # Need a second degree-2 factor of f1
      ff_irred = first(p for (p, _) in fact1 if degree(p) == 2 && p != f_irred)
      L2, embed2, rff = _adjoin_root(K, ff_irred)

      e1 = vcat(_coords(one(L1), L1, K), _coords(one(L2), L2, K))
      ex = vcat(_coords(-rf, L1, K),     _coords(-rff, L2, K))

      for (g1, _) in fact2
        degree(g1) == 2 || continue
        for root1 in _roots_in(g1, L1, embed1)
          for (g2, _) in fact2
            (degree(g2) == 2 && g2 != g1) || continue
            for root2 in _roots_in(g2, L2, embed2)
              ey  = vcat(_coords(root1, L1, K),        _coords(root2, L2, K))
              exy = vcat(_coords(-rf * root1, L1, K),  _coords(-rff * root2, L2, K))
              data = T[c for i in 1:4 for c in (ey[i], e1[i], exy[i], ex[i])]
              M = matrix(K, 4, 4, data)
              ker = kernel(M; side = :right)
              if ncols(ker) == 1
                t = T[ker[i, 1] for i in 1:4]
                _check_and_add(t)
              end
            end
          end
        end
      end
    else  # d1 == 1
      ff_irred = first(p for (p, _) in fact1 if degree(p) == 1)
      rff = -coeff(ff_irred, 0) * inv(leading_coefficient(ff_irred))  # rational root

      e1 = vcat(_coords(one(L1), L1, K), [one(K)])
      ex = vcat(_coords(-rf, L1, K),     [-rff])

      for (g1, _) in fact2
        degree(g1) == 2 || continue
        for root1 in _roots_in(g1, L1, embed1)
          # Loop over linear factors of f2
          for (g2, _) in fact2
            degree(g2) == 1 || continue
            root2 = -coeff(g2, 0) * inv(leading_coefficient(g2))
            ey  = vcat(_coords(root1, L1, K),       [root2])
            exy = vcat(_coords(-rf * root1, L1, K), [-rff * root2])
            data = T[c for i in 1:3 for c in (ey[i], e1[i], exy[i], ex[i])]
            M = matrix(K, 3, 4, data)
            ker = kernel(M; side = :right)
            if ncols(ker) == 1
              t = T[ker[i, 1] for i in 1:4]
              _check_and_add(t)
            end
          end
          # Also handle point at infinity if deg(f2) < n
          if degree(f2) < n
            e1i = vcat(_coords(one(L1), L1, K),  [zero(K)])
            exi = vcat(_coords(-rf, L1, K),       [zero(K)])
            ey  = vcat(_coords(root1, L1, K),     [one(K)])
            exy = vcat(_coords(-rf * root1, L1, K), [-rff])
            data = T[c for i in 1:3 for c in (ey[i], e1i[i], exy[i], exi[i])]
            M = matrix(K, 3, 4, data)
            ker = kernel(M; side = :right)
            if ncols(ker) == 1
              t = T[ker[i, 1] for i in 1:4]
              _check_and_add(t)
            end
          end
        end
      end
    end
  else  # d == 1, all factors split over K
    # Take three rational roots of f1
    rat_roots1 = T[-coeff(p, 0) * inv(leading_coefficient(p)) for (p, _) in fact1 if degree(p) == 1]
    @assert length(rat_roots1) >= 3
    rs = rat_roots1[1:3]

    # Build pool of roots of f2, represented as (numerator, denominator) in P^1(K)
    rootsf2 = Tuple{T,T}[(-coeff(p,0)*inv(leading_coefficient(p)), one(K))
                         for (p, _) in fact2 if degree(p) == 1]
    if degree(f2) < n
      push!(rootsf2, (one(K), zero(K)))  # point at infinity
    end

    for r1 in rootsf2
      for r2 in rootsf2
        r2 == r1 && continue
        for r3 in rootsf2
          (r3 == r1 || r3 == r2) && continue
          # Build 3x4 matrix encoding rs[i] -> ri for i=1,2,3
          # (a*rs[i] + b)*ri[2] = (c*rs[i] + d)*ri[1]
          rows = vcat(
            [r1[1], r1[2], -rs[1]*r1[1], -rs[1]*r1[2]],
            [r2[1], r2[2], -rs[2]*r2[1], -rs[2]*r2[2]],
            [r3[1], r3[2], -rs[3]*r3[1], -rs[3]*r3[2]]
          )
          M = matrix(K, 3, 4, rows)
          ker = kernel(M; side = :right)
          if ncols(ker) == 1
            t = T[ker[i, 1] for i in 1:4]
            _check_and_add(t)
          end
        end
      end
    end
  end

  return !isempty(result), result
end

################################################################################
#
#  Main function
#
################################################################################

# Internal implementation. Always returns a HypellCrvIsom as second value;
# if the curves are not isomorphic, returns an uninitialised (illegal) object.
function _is_isomorphic(C1::HypellCrv{T}, C2::HypellCrv{T}) where T
  K = base_field(C1)
  @req base_field(C2) === K "Curves must have the same base field"

  dummy = HypellCrvIsom{T}()

  if genus(C1) != genus(C2)
    return false, dummy
  end
  g = genus(C1)

  # Fast exit for genus 2: compare absolute invariants
  # Reference: [Igu60], implemented via Igusa-Clebsch invariants.
  if g == 2
    # test equality in P(2, 4, 6, 10)
    if !weighted_equality(igusa_clebsch_invariants(C1), igusa_clebsch_invariants(C2), [2, 4, 6, 10])
      return false, dummy
    end
  end

  @req characteristic(K) != 2 "is_isomorphic currently does not work in characteristic 2"

  Kx = parent(hyperelliptic_polynomials(C1)[1])

  f1, h1 = hyperelliptic_polynomials(C1)
  f2, h2 = hyperelliptic_polynomials(C2)

  # Step 1: remove h by completing the square y -> 2y + h(x), giving y^2 = 4f + h^2.
  # The isomorphism C_raw -> C (where C_raw has h=0) is:
  #   x -> x,  y -> (2*y + h(x)) with u=2, v=h on the codomain side.
  # We record the *inverse*: C -> C_raw is x->x, y->(y - h(x)/2)/1 which as
  # HypellCrvIsom (with v=0) is only valid for h=0. We handle h via the curve
  # constructor and only compose the GL2 part.

  if !iszero(h1)
    f1 = 4*f1 + h1^2
  end
  if !iszero(h2)
    f2 = 4*f2 + h2^2
  end

  # Build intermediate curves with h=0 (over K)
  # We need monic f; rescale if necessary.
  lc1 = leading_coefficient(f1)
  lc2 = leading_coefficient(f2)
  f1_monic = iszero(lc1) ? f1 : f1 * inv(lc1)
  f2_monic = iszero(lc2) ? f2 : f2 * inv(lc2)

  C1h = hyperelliptic_curve(f1_monic; check = false)
  C2h = hyperelliptic_curve(f2_monic; check = false)

  # Step 2: flip to even-degree model if degree is odd (i.e. 2g+1).
  # The flip x -> 1/x corresponds to matrix [0,1,1,0] (Magma: Transformation(C,[0,1,1,0])).

  flip1 = isodd(degree(f1))
  flip2 = isodd(degree(f2))

  flip_mat = T[zero(K), one(K), one(K), zero(K)]

  if flip1
    # Apply [0,1,1,0] (x -> 1/x) to f1_monic as a degree-(2g+2) form (Magma: TransformPolynomial)
    f1_even = _transform_polynomial(f1_monic, 2*g + 2, flip_mat)
    lc = leading_coefficient(f1_even)
    f1_even = f1_even * inv(lc)
    C1f = hyperelliptic_curve(f1_even; check = false)
  else
    f1_even = f1_monic
    C1f = C1h
  end

  if flip2
    f2_even = _transform_polynomial(f2_monic, 2*g + 2, flip_mat)
    lc = leading_coefficient(f2_even)
    f2_even = f2_even * inv(lc)
    C2f = hyperelliptic_curve(f2_even; check = false)
  else
    f2_even = f2_monic
    C2f = C2h
  end

  # Step 3: call GL2 equivalence test on the even-degree polynomials
  _, list = is_gl2_equivalent(f1_even, f2_even, 2*g + 2)

  for t in list
    # Compose flips with GL2 matrix to get the overall x-map matrix C1 -> C2.
    # The composition is: inv(flip2) * t * flip1  where flip = [0,1;1,0].
    # In terms of the [a,b,c,d] representation:
    #   pre-compose flip1:   [a,b,c,d] -> [b,a,d,c]  (right-multiply by flip)
    #   post-compose flip2^-1: [a,b,c,d] -> [c,d,a,b]  (left-multiply by flip)
    mat = t
    if flip1
      a2, b2, c2, d2 = mat
      mat = T[b2, a2, d2, c2]
    end
    if flip2
      a2, b2, c2, d2 = mat
      mat = T[c2, d2, a2, b2]
    end

    # Check validity: the composed matrix applied to f1 (h-removed) must be proportional
    # to f2 (h-removed) with a proportionality constant that is a square.
    f3_orig = _transform_polynomial(f1, 2*g + 2, mat)
    lc3_orig = leading_coefficient(f3_orig)
    iszero(lc3_orig) && continue
    ratio = lc3_orig * inv(lc2)
    fl_ratio, rc_total = is_square_with_sqrt(ratio)
    fl_ratio || continue

    u_total = rc_total

    # Build the final isomorphism C1 -> C2
    a_f, b_f, c_f, d_f = mat
    isom_final = HypellCrvIsom{T}(C1, C2, a_f, b_f, c_f, d_f, u_total, zero(Kx))

    return true, isom_final
  end

  return false, dummy
end

@doc raw"""
    is_isomorphic_with_isomorphism(C1::HypellCrv, C2::HypellCrv) -> Bool, HypellCrvIsom

Return `true` and an isomorphism $C_1 \to C_2$ if $C_1$ and $C_2$ are
isomorphic as hyperelliptic curves over their common base field. Otherwise
return `false` and an undefined value.

Currently requires characteristic $\neq 2$.
"""
function is_isomorphic_with_isomorphism(C1::HypellCrv{T}, C2::HypellCrv{T}) where T
  return _is_isomorphic(C1, C2)
end

@doc raw"""
    is_isomorphic(C1::HypellCrv, C2::HypellCrv) -> Bool

Return `true` if $C_1$ and $C_2$ are isomorphic as hyperelliptic curves over
their common base field, and `false` otherwise.

Currently requires characteristic $\neq 2$.
"""
function is_isomorphic(C1::HypellCrv{T}, C2::HypellCrv{T}) where T
  return _is_isomorphic(C1, C2)[1]
end
