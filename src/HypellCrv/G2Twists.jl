################################################################################
#
#  HypellCrv/G2Twists.jl : Twists of genus 2 curves
#
# (C) 2026
#
# References:
#
# [Igu60] J.-I. Igusa,
#         "Arithmetic variety of moduli for genus two",
#         Ann. Math. 72 (1960), 612-649.
#
# [Mes91]  J.-F. Mestre,
#          "Construction de courbes de genre 2 \`a partir de leurs modules",
#          in "Effective Methods in Algebraic Geometry",
#          vol 94 of Progress in Mathematics, 313-334, Birkhauser, 1991.
#
# [ShVo2004] T. Shaska, H. Volklein,
#            "Elliptic subfields and automorphisms of genus 2 function fields",
#            Algebra, Arithmetic and Geometry with Applications (West Lafayette, IN, 2000),703-723,
#            Springer, 2004
#
# [CaNaPu2005] G. Cardona, E. Nart and J. Pujolas,
#              "Curves of genus two over fields of even characteristic",
#               Mathematische Zeitschrift, 250, 177-201, Springer, 2005
#
# [CaQu2005] G. Cardona, J. Quer,
#            "Field of moduli and field of definition for curves of genus 2",
#             Computational aspects of algebraic curves,  71-83,
#             Lecture Notes Ser. Comput., 13, World Sci. Publ., Hackensack, NJ, 2005.
#
# [CaNa2007] G. Cardona, E. Nart,
#            "Zeta Function and Cryptographic Exponent of Supersingular
#             Curves of Genus 2",  ArXiv e-prints 0704.1951C, 2007.
#
# [LRS20] R. Lercier, C. Ritzenthaler, and J. Sijsling
#            "hyperelliptic, a Magma repository for reconstruction and isomorphisms of hyperelliptic curves.
#            2020
#            Note: https://github.com/JRSijsling/hyperelliptic
#
# [BLRS26] T.Bouchet, R. Lercier, C. Ritzenthaler, J. Sijsling,
#          "Functionality for isomorphism classes of curves and hypersurfaces"
#
################################################################################

@doc raw"""
    quadratic_twist(C::HypellCrv{FinFieldElem})

Return a quadratic twist of the hyperelliptic curve C.
"""
function quadratic_twist(C::HypellCrv{T}) where T <: FinFieldElem
  F = base_field(C)
  R, x = polynomial_ring(F, :x)
  if characteristic(F) == 2
    f,h = hyperelliptic_polynomials(C)
    if is_odd(degree(F))
      u = one(F)
    else
      u = Hecke.normal_basis(base_field(F), F)
    end
    return hyperelliptic_curve([f + u*(h^2), h])
  else
    f, _ = hyperelliptic_polynomials(simplified_model(C))
    return hyperelliptic_curve(primitive_element(F)*f)
  end
end

function filter_g2_isomorphism_classes(curves::Vector{HypellCrv{T}}) where T <: FieldElem
  result = HypellCrv{T}[]
  for C in curves
    if !any([ is_isomorphic(C, D) for D in result ])
       push!(result, C)
    end
  end
  return result
end

#Twists for characteristic 2. Mostly follows [CaNaPu2005] and [LRS20].

function g2_models_FF_char2_C2(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(g2_invs[1])
  g1, g2, g3 = g2_invs
  R, x = polynomial_ring(F, :x)
  if all_twists
    o = trace_one_element(F)
  end

  if g1 == 0
	  H1 = hyperelliptic_curve(g2*x^5 + g3*x^3 + x, x)
	  if !all_twists
      return [H1]
    end
	  H2 = hyperelliptic_curve(g2*x^5 + g3*x^3 + o*x^2 + x, x)
	  return [H1, H2]
  end

  fac = [(f,d) for (f,d) in  factor(x^3 + g3*x^2 + g2*x + g1)]
  splitF = maximum(map(f -> degree(f[1]), fac))
  if splitF == 1
    roots = []
    for f in fac
      for i in (1:f[2])
        push!(roots, coeff(f[1], 0))
      end
    end
    a, b, c = roots
    H1 = hyperelliptic_curve(a*x^5 + 2*a*x^4 + (c + b + a)*x^3 + (2*b + c)*x^2 + b*x, x*(x + 1))
    if !all_twists
      return [H1]
    end
    H2 = hyperelliptic_curve(a*x^5 + (2*a + o)*x^4 + (c + b + 2*o + a)*x^3 + (2*b + c + o)*x^2 + b*x, x*(x + 1))
	  return [H1, H2]
  end

  u = v = F(1)
  if splitF == 2
    for f in fac
      if degree(f[1]) == 1
        a = coeff(f[1], 0)
      else
        v = coeff(f[1], 0)
        u = coeff(f[1], 1)
      end
	  end
	  H1 = hyperelliptic_curve(a*x*(x^2 + x + v/u^2)^2 + (u*x + u)*(x^2 + x + v/u^2), x^2 + x + v/u^2)
	  if !all_twists
      return [H1]
    end
	  H2 = hyperelliptic_curve((a*x + o)*(x^2 + x + v/u^2)^2 + (u*x + u)*(x^2 + x + v/u^2), x^2 + x + v/u^2)
	  return [H1, H2]
  end

  if g2 == g3^2
    s = b = g1 + g2*g3
    t = a = 0
    c = g3*b
  else
    den2 = (g1 + g2*g3)^2
    s = t = (g2 + g3^2)^3/den2
    a = b = (g1 + g3^3)*(g2 + g3^2)^2/den2
    c = (g2 + g3^2)^3*(g1*(g2 + g3^2)^2 + g3*(g1 + g3^3)^2)/den2^2
  end
  H1 = hyperelliptic_curve(a*x^5 + b*x^4 + (c + a*t)*x^3 + (a*s + b*t)*x^2 + (c*t + b*s)*x + c*s, x^3 + t*x + s)
  if !all_twists
    return [H1]
  end
  H2 = hyperelliptic_curve(o*x^6 + a*x^5 + (2*o*t + b)*x^4 + (2*o*s + a*t + c)*x^3 + (a*s + t*(o*t + b))*x^2 + (s*(o*t + b) + t*(o*s + c))*x + s*(o*s + c), x^3 + t*x + s)
  return [H1, H2]
end

function g2_models_FF_char2_C2xC2(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem
  F = parent(g2_invs[1])
  _, g2, g3 = g2_invs
  R, x = polynomial_ring(F, :x)
  a = g3
  b = c = sqrt(g2)
  H1 = hyperelliptic_curve(a*x^5 + 2*a*x^4 + a*x^3 + c*x^2 + c*x, x^2 + x)

  if !all_twists
    return [H1]
  end
  o = trace_one_element(F)
  H2 = hyperelliptic_curve(a*x^5 + 2*a*x^4 + (2*a*o + a)*x^3 + (c + 2*a*o)*x^2 + (c + a*o^2)*x + c*o, x^2 + x + o)

  if trace(g3) == 0
    H3 = hyperelliptic_curve(a*x^5 + (o + 2*a)*x^4 + (2*o + a)*x^3 + (c + o)*x^2 + c*x,x^2 + x)
    H4 = hyperelliptic_curve(a*x^5 + (o + 2*a)*x^4 + (2*o + 2*a*o + a)*x^3 + (o^2 + c + o + a*o + (o + a)*o)*x^2 + (o^2 + c + (o + a*o)*o)*x + (o^2 + c)*o, x^2 + x + o)
    return [H1, H2, H3, H4]
  else
    return [H1, H2]
  end
end

function g2_models_FF_char2_C2xS3(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(g2_invs[1])
  _, _, g3 = g2_invs
  R, x = polynomial_ring(F, :x)

  a = b = c = g3

  H1 = hyperelliptic_curve(a*x^5 + 2*a*x^4 + a*x^3 + c*x^2 + c*x, x^2 + x)
  if !all_twists
    return [H1]
  end

  o = trace_one_element(F)
  H2 = hyperelliptic_curve(a*x^5 + 2*a*x^4 + (2*a*o + a)*x^3 + (c + 2*a*o)*x^2 + (c + a*o^2)*x + c*o, x^2 + x + o)

  if trace(g3) == 0
	  H3 = hyperelliptic_curve(a*x^5 + (o + 2*a)*x^4 + (2*o + a)*x^3 + (c + o)*x^2 + c*x, x^2 + x)
	  H4 = hyperelliptic_curve(a*x^5 + (o + 2*a)*x^4 + (2*o + 2*a*o + a)*x^3 + (o^2 + c + o + a*o + (o + a)*o)*x^2 + (o^2 + c + (o + a*o)*o)*x + (o^2 + c)*o, x^2 + x + o)
    quads = [H1, H2, H3, H4]
  else
	  quads = [H1,H2]
  end

  u = rand(F)
  while !is_irreducible(x^3 + u*x + u)
    u = rand(F)
  end

  t = s = u
  a = b = g3*u
  c = g3*u*(u + 1)
	Hc1 = hyperelliptic_curve(a*x^5 + b*x^4 + (c + a*t)*x^3 + (a*s + b*t)*x^2 + (c*t + b*s)*x + c*s, x^3 + t*x + s)
	Hc2 = hyperelliptic_curve(o*x^6 + a*x^5 + (2*o*t + b)*x^4 + (2*o*s + a*t + c)*x^3 + (a*s + t*(o*t + b))*x^2 + (s*(o*t + b) + t*(o*s + c))*x + s*(o*s + c), x^3 + t*x + s)

  cubs = [Hc1, Hc2]
  return vcat(quads, cubs)
end

function g2_models_FF_char2_C2_mixed(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem
  F = parent(g2_invs[1])
  _, g2, _ = g2_invs
  R, x = polynomial_ring(F, :x)

  H1 = hyperelliptic_curve(g2*x^5 + x, x)
  if !all_twists
    return [H1]
  end

  o = trace_one_element(F)
  H2 = hyperelliptic_curve(g2*x^5 + o*x^2 + x, x)
  return [H1, H2]
end

function g2_models_FF_char2_M32(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(g2_invs[1])
  _, _, g3 = g2_invs
  R, x = polynomial_ring(F, :x)

  sqrt_g3 = sqrt(g3)
  if !all_twists
    return [hyperelliptic_curve(sqrt_g3*x^5 + sqrt_g3*x^3, R(1))]
  end

  P, _ = polynomial_ring(GF(2))
  u = gen(F)

  E = sqrt_g3^4*x^16 + sqrt_g3^4*x^8 + sqrt_g3^2*x^2 + sqrt_g3*x
  KE = roots(E)
  V = vector_space(GF(2), degree(F))
  wa = [ P([v[i] for i in (1:degree(F))])(u) for v in basis(V)]
  wa = map(x-> V(absolute_coordinates(E(x))), wa)
  S, phi = sub(V, wa)
  W, pi = quo(V, S)




  K = [P([preimage(pi, w)[i] for i in (1:degree(F)) ])(u) for w in W]
  twists = HypellCrv{T}[]
  for b in K
	  H = hyperelliptic_curve(sqrt_g3*x^5 + b*x^4 + sqrt_g3*x^3, R(1))
	  push!(twists, H)

	  notwists = false
	  for k in KE
	    if trace(sqrt_g3*k^5 + b*k^4 + sqrt_g3*k^3) == GF(2)(1)
        notwists = true
        break
      end
	  end

	  if notwists == false
      o = trace_one_element(F)
	    twists = vcat(twists, hyperelliptic_curve(sqrt_g3*x^5 + b*x^4 + sqrt_g3*x^3 + o, R(1)))
	  end
  end

  return twists
end

function g2_models_FF_char2_M160(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(g2_invs[1])
  R, x = polynomial_ring(F, :x)

  H1 = hyperelliptic_curve(x^5, R(1))

  if !all_twists
    return [H1]
  end

  o = trace_one_element(F)
  prim = primitive_element(F)

  H2 = hyperelliptic_curve(x^5 + x^4, R(1))
  if (mod(degree(F),4)) != 0
    if (mod(degree(F), 2)) != 0
      H3 = hyperelliptic_curve(x^5 + x^4 + 1, R(1))
      return [H1, H2, H3]
    end
    F4 = GF(4)
    phi = embed(F4, F)
    u = phi(gen(F4))
    H3 = hyperelliptic_curve(x^5 + u*x^4, R(1))
    H4 = hyperelliptic_curve(x^5 + (u + 1)*x^4, R(1))
    H5 = hyperelliptic_curve(x^5 + x^4 + u, R(1))

    return [H1, H2, H3, H4, H5]
  end

  A = collect(Set([prim^i for i in (0:4)]))

  MU5 = roots(x^5 - 1)

  twists = HypellCrv{T}[]
  for a in A
    H = hyperelliptic_curve(a*x^5, R(1))
    push!(twists, H)
    push!(twists, hyperelliptic_curve(a*x^5 + o, R(1)))
  end

  E1 = x^16 + x
  V = vector_space(GF(2), degree(F))
  S, phi = sub(V, [ V([E1(v[i]) for i in (1:degree(F))]) for v in basis(V)])
  W, pi = quo(V, S)

  W = [w for w in W if w != zero(W)]
  o = gen(F)
  P, _ = polynomial_ring(GF(2))

  for i in (1:3)
    vec = [preimage(pi, W[1])[i] for i in (1:degree(F)) ]
    a = P(vec)(o)
    H = hyperelliptic_curve(x^5 + a*x^4, R(1))
    push!(twists, H)
    for mu in MU5
      W = collect(setdiff(Set(W), Set([pi(V(absolute_coordinates(a*mu)))])))
    end
  end
  return twists
end

# y^2 = 1/t*x^6 + x^4 + x^2 + 1 in characteristic 3, and its twists.
# Follows [LRS20].
function g2_models_FF_char3_D12(igusa_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(igusa_invs[1])
  R, x = polynomial_ring(F, :x)
  J2, J4, J6, _, J10 = igusa_invs

  _, t = is_power(-J2^3/J6, 3)

  H1 = hyperelliptic_curve(x^6 + t*x^4 + (t - 1)*x^3 + t*x^2 + 1)
  twists = [H1]
  if !all_twists
    return twists
  end

  push!(twists, quadratic_twist(H1))


  q = length(F)
  GF_q2 = GF(q^2)
  a = d = primitive_element(GF_q2)
  b = c = a^q
  Ctwist = hyperelliptic_transform(base_change(GF_q2, H1), [a,b,c,d])[1]
  Ctwist = base_change(F, Ctwist)
  f, h = hyperelliptic_polynomials(Ctwist)
  H2 = hyperelliptic_curve(f(x), h(x))
  push!(twists, H2)
  push!(twists, quadratic_twist(H2))

  while true
	  a0 = rand(F)
	  a1 = rand(F)
	  f = x^3  +  a1*x  +  a0
	  if is_irreducible(f)
      break
    end
  end

  GF_q3, a = finite_field(f, :a)

  b = -a^q - a
  c = a^q
  d = -c^q - c

  Ctwist = hyperelliptic_transform(base_change(GF_q3, H1),[a,b,c,d])[1]
  f, h = hyperelliptic_polynomials(Ctwist)
  f = map_coefficients(coerce_to_base_field, f)
  h = map_coefficients(coerce_to_base_field, h)
  H3 = hyperelliptic_curve(f(x), h(x))
  push!(twists, H3)
  push!(twists, quadratic_twist(H3))

  return twists
end


#   y^2 = x^5 - x in characteristic 5,
#   Mostly follows [CaNa2007] and [LRS20].
function g2_models_FF_char5_G240(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(g2_invs[1])
  R, x = polynomial_ring(F, :x)

  H1 = hyperelliptic_curve(x^5 - x)
  twists = [H1]
  if !all_twists
    return twists
  end

  prim = primitive_element(F)
  t = trace_one_element(F)
  H2 = hyperelliptic_curve(x^5 - x - t)

  push!(twists, H2)
  push!(twists, quadratic_twist(H2))

  t = rand(F)
  f = x^6 + t*x^5 + (1 - t)*x + 2
  while !is_irreducible(f)
	  t = rand(F)
	  f = x^6 + t*x^5 + (1 - t)*x + 2
  end

  H3 = hyperelliptic_curve(f)
  push!(twists, H3)

  d = degree(F)
  if is_odd(d)

    push!(twists, hyperelliptic_curve(x^5 - 2*x))
    push!(twists, hyperelliptic_curve(x^5 - 4*x))
    push!(twists, hyperelliptic_curve((x^2 + 2)*(x^2 + 4*x + 2)*(x^2 - 4*x + 2)))

    t = rand(F)
    f1 = x^3 - t*x^2 + (t - 3)*x + 1
    while !is_irreducible(f1)
      t = rand(F)
      f1 = f = x^3 - t*x^2 + (t - 3)*x + 1
    end

    t = (3 + 2*t)/(3 + 3*t)
    f2 = x^3 - t*x^2 + (t - 3)*x + 1
    push!(twists, hyperelliptic_curve(f1*f2))

    return twists
  end

  push!(twists, quadratic_twist(H1))
  push!(twists, quadratic_twist(H3))

  H4 = hyperelliptic_curve(x^5 - prim^2*x)
  push!(twists, H4)

  H5 = hyperelliptic_curve(x^5 - prim*x)
  push!(twists, H5)
  push!(twists, quadratic_twist(H5))

  t = prim
  H6 = hyperelliptic_curve((x^2 - t)*(x^4 + 6*t*x^2 + t^2))
  push!(twists, H6)

  sqrt_3 = sqrt(F(3))
  H7 = hyperelliptic_curve((x^3 - prim)*(x^3 - (15*sqrt_3 - 26)*prim))
  push!(twists, H7)
  push!(twists, quadratic_twist(H7))

  return twists
end


# y^2 = x^6 - 1 in characteristic not equal to 3 or 5
# Follows [CaNa2007] and [LRS20].

function g2_models_FF_2D12(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(g2_invs[1])
  R, x = polynomial_ring(F, :x)

  H1 = hyperelliptic_curve(x^6 - 1)
  if !all_twists
    return [H1]
  end

  twists = [H1, quadratic_twist(H1)]

  q = length(F)
  prim = primitive_element(F)
  t = prim
  H2 = hyperelliptic_curve(x^6 - t^3)
  push!(twists, H2)
  push!(twists, quadratic_twist(H2))

  H3 = hyperelliptic_curve(x*(t*x^2 + 3)*(3*t*x^2 + 1))
  push!(twists, H3)
  push!(twists, quadratic_twist(H3))

  GF_q4 = GF(q^4)
  t = primitive_element(GF_q4)
  a = t^(div(q^2 + 1,2))
  b = a^q
  c = -b
  d = a
  Ctwist = hyperelliptic_transform(base_change(GF_q4, H1),[a,b,c,d])[1]
  f4, _ = hyperelliptic_polynomials(Ctwist)
  f4 = f4/leading_coefficient(f4)
  f4 = change_base_ring(F, f4)(x)
  H4 = hyperelliptic_curve(f4)
  push!(twists, H4)
  push!(twists, quadratic_twist(H4))

  if is_square(F(-3))
    t = prim
    H5 = hyperelliptic_curve(x^6 - t^2)
    push!(twists, H5)
    push!(twists, quadratic_twist(H5))

    H6 = hyperelliptic_curve(x^6 - t)
    push!(twists, H6)
    push!(twists, quadratic_twist(H6))
  else
    GF_q6 = GF(q^6)
    t = primitive_element(GF_q6)
    a = t^(div(q^4 + q^2 + 1, 3))
    b = a^4
    c = a^q*t^(div(q^6 - 1, 3))
    d = b^q*t^(div(q^6 - 1, 3))

    R6, s = polynomial_ring(GF_q6, :s)
    f6 = (a*s + b)^6 - (c*s + d)^6
    f6 = f6/leading_coefficient(f6)
    f6 = change_coefficient_ring(F, f6)
    H7 = hyperelliptic_curve(f6(x))
    push!(twists, H7)
    push!(twists, quadratic_twist(H7))

    GF_q12 = GF(q^12)
    t = primitive_element(GF_q12)
    a = t^(div((q^4 + q^2 + 1)*(q^6 + 1), 6))
    b = a^7
    c = a^q*t^(div(q^12 - 1, 6))
    d = b^q*t^((div(q^12 - 1, 6)))
    R12, s = polynomial_ring(GF_q12, :s)
    f12 = (a*s + b)^6 - (c*s + d)^6
    f12 = f12/leading_coefficient(f12)
    f12 = change_coefficient_ring(F, f12)
    H8 = hyperelliptic_curve(f12(x))
    push!(twists, H8)
    push!(twists, quadratic_twist(H8))
  end

  return filter_g2_isomorphism_classes(twists)
end



#   y^2 = x^5 - x in char != 5,
#   Follows [CaNa2007] and [LRS20].

function g2_models_FF_G48(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(g2_invs[1])
  R, x = polynomial_ring(F, :x)

  H1 = hyperelliptic_curve(x^5 - x)
  twists = [H1]
  if !all_twists
    return twists
  end

  push!(twists, quadratic_twist(H1))

  q = length(F)
  prim = primitive_element(F)
  test = is_square(F(-1))
  if test
    sqr = sqrt(F(-1))
    t = prim
    H2 = hyperelliptic_curve(x^5 - t*x)
    push!(twists, H2)
    push!(twists, quadratic_twist(H2))

    H3 = hyperelliptic_curve(x^5 - t^2*x)
    push!(twists, H3)
    push!(twists, quadratic_twist(H3))

    GF_q8 = GF(q^8)
    t = primitive_element(GF_q8)
    a = t^(div((q^2 + 1)*(q^4 + 1), 4))
    i = a^(q^2 - 1)
    b = a^5
    c = a^q/i
    d = b^q/i
    R8, s = polynomial_ring(GF_q8)
    f8 = (a*s + b)^5*(c*s + d) - (a*s + b)*(c*s + d)^5
    f8 = f8/leading_coefficient(f8)
    f8 = change_base_ring(F, f8)(x)
    H4 = hyperelliptic_curve(f8)
    push!(twists, H4)
    push!(twists, quadratic_twist(H4))


    t = rand(F)
    f1 = x^3 - t*x^2 + (t - 3)*x + 1
    while !is_irreducible(f1)
      t = rand(F)
      f1 = x^3 - t*x^2 + (t - 3)*x + 1
    end

    t = F((18 + (5*sqr - 3)*t)/((5*sqr + 3) - 2*t))
    f2 = x^3 - t*x^2 + (t - 3)*x + 1
    H5 = hyperelliptic_curve(f1*f2)
    push!(twists, H5)
    push!(twists, quadratic_twist(H5))
  else
    H6 = hyperelliptic_curve(x^5  +  x)
    push!(twists, H6)
    push!(twists, quadratic_twist(H6))

    GF_q4 = GF(q^4)
    t = primitive_element(GF_q4)
    a = t^(div(q^2 + 1,2))
    b = a^q
    c = -b
    d = a
    Ctwist = hyperelliptic_transform(base_change(GF_q4, H1), [a,b,c,d])[1]
    f4, _ = hyperelliptic_polynomials(Ctwist)
    f4 = f4/leading_coefficient(f4)
    f4 = change_base_ring(F, f4)(x)
    H7 = hyperelliptic_curve(f4)
    push!(twists, H7)
    push!(twists, quadratic_twist(H7))

    GF_q8 = GF(q^8)
    t = primitive_element(GF_q8)
    a = t^(div((q^2 + 1)*(q^4 + 1), 4))
    i = -a^(q^2 - 1)
    b = a^5
    c = a^q/i
    d = b^q/i
    R8, s = polynomial_ring(GF_q8, :s)
    f8 = (a*s + b)^5*(c*s + d) - (a*s + b)*(c*s + d)^5
    f8 = f8/leading_coefficient(f8)
    f8 = change_base_ring(F, f8)(x)
    H8 = hyperelliptic_curve(f8)
    push!(twists, H8)
    push!(twists, quadratic_twist(H8))


    f9 = R(0)

    while true
      while true
        a = rand(F)
        test = is_square(-2 - a^2)
        if test
          sqr = sqrt(-2 - a^2)
          break
        end
      end
      f9 = x^6 - (a + 3)*x^5 + 5*(2 + a - sqr)/2*x^4 + 5*(sqr - 1)*x^3 + 5*(2 - a - sqr)/2*x^2 + (a - 3)*x + F(1)
      if is_irreducible(f9)
        break
      end
    end
    H9 = hyperelliptic_curve(f9)
    push!(twists, H9)
    push!(twists, quadratic_twist(H9))
  end
  return filter_g2_isomorphism_classes(twists)
end

#   y^2 = x^5 - 1,
#   Follows [CaNa2007] and [LRS20]
function g2_models_FF_C10(g2_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem
  F = parent(g2_invs[1])
  R, x = polynomial_ring(F, :x)

  H1 = hyperelliptic_curve(x^5 - 1)
  twists = [H1]
  if !all_twists
    return twists
  end

  prim = primitive_element(F)
  push!(twists, quadratic_twist(H1))

  if (GF(5)(characteristic(F)))^degree(F) != 1
	  return twists
  end

  A = collect(Set([prim^i for i in (0:4)]))
  for a in A
	  H2 = hyperelliptic_curve(a*x^5 - 1)
    push!(twists, H2)
    push!(twists, quadratic_twist(H2))
  end
  return filter_g2_isomorphism_classes(twists)
end

#   y^2 = x^6  +  x^3  +  t in char != 3,
#   Follows [CaNa2007] and [LRS20].

function g2_models_FF_D12(igusa_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(igusa_invs[1])
  R, x = polynomial_ring(F, :x)
  J2, J4, J6, _, J10 = igusa_invs
  p = characteristic(F)

  if p == 5
	  a = -1 - J4/J2^2
  else
	  C2, C4, C6, C10 = clebsch_from_igusa_clebsch([8*J2,4*J2^2 - 96*J4,8*J2^3 - 160*J2*J4 - 576*J6, 4096*J10])
	  a = (3*C4*C6 - C10)/50/C10
  end

  f = x^6 + x^3 + a
  if F == QQ
    f, gamma = reduce_binary_form(f)
  end

  H1 = hyperelliptic_curve(f)
  twists = [H1]
  if !all_twists
    return twists
  end

  n = degree(F)
  prim = primitive_element(F)
  q = length(F)
  if mod(q,3) == 2
    if is_square(a)
      push!(twists, quadratic_twist(H1))
    end

    A = roots(x^3 - a)[1]
    while true
      t = rand(F)
      delta = t^2 - 4/A
      if !is_square(delta)
        break
      end
    end

    GF_q2 = GF(q^2)
    t = GF_q2(t)
    A = GF_q2(A)
    R2, s = polynomial_ring(GF_q2, :s)

    sqr = sqrt(GF_q2(delta))
    theta1 = (t + sqr)/2
    theta2 = (t - sqr)/2
    f = ((s - theta1)^6/theta1^3 - (s^2 - t*s + 1/A)^3 + GF_q2(a)*theta1^3*(s - theta2)^6)
    f = change_coefficient_ring(F, f)
    f = f(x)
    H2 = hyperelliptic_curve(f)
    push!(twists, H2)
    if is_square(a)
      push!(twists, quadratic_twist(H2))
    end

    theta = GF_q2(1)
    while true
      t = rand(F)
      delta = t^2 - 4*a
      if !is_square(delta)
        sqr = sqrt(GF_q2(delta))
        theta = (t + sqr)/2
        if is_irreducible(s^3 - theta)
          break
        end
      end
    end

    eta =  roots(s^2 + s + 1)[1]
    f = (s - eta)^6*theta - (s^2 + s + 1)^3 + GF_q2(a)*(s - eta^2)^6/theta
    f = change_coefficient_ring(F, f)
    f = f(x)
    H3 = hyperelliptic_curve(f)
    push!(twists, H3)
    push!(twists, quadratic_twist(H3))
    return twists
  end

  if (is_power(a, 3)[1] && is_square(a)) || !(is_power(a,3)[1])
	  push!(twists, quadratic_twist(H1))
  end

  if !(is_power(a, 3)[1])
	  t = a
  else
	  t =  prim
  end

  H4 = hyperelliptic_curve(x^6  +  t * x^3  +  a * t^2)
  push!(twists, H4)

  if is_power(a, 3)[1] || is_square(a) || !(is_power(a, 3)[1])
	  push!(twists, quadratic_twist(H4))
  end

  if is_power(a, 3)[1]
    delta = F(0)
	  A = roots(x^3 - a)[1]
	  while true
	    t = rand(F)
	    delta = t^2 - 4/A
	    if !is_square(delta)
        break
      end
	  end

	  GF_q2 = GF(q^2)
    R2, s = polynomial_ring(GF_q2, :s)

    sqr = sqrt(GF_q2(delta))
    t = GF_q2(t)
    A = GF_q2(A)
    a = GF_q2(a)
	  theta1 = (t + sqr)/2
    theta2 = (t - sqr)/2

    f = (s - theta1)^6/theta1^3 - (s^2 - t*s + 1/A)^3 + a*theta1^3*(s - theta2)^6
    f = change_coefficient_ring(F, f)
    f = f(x)
    H5 = hyperelliptic_curve(f)
    push!(twists, H5)
  else
	  while true
	    t = rand(F)
	    delta = t^2 - 4/a
	    if !is_square(delta)
        break
      end
	  end

	  GF_q2 = GF(q^2)
    R2, s = polynomial_ring(GF_q2, :s)
    t = GF_q2(t)

    sqr = sqrt(GF_q2(delta))
	  theta1 = (t + sqr)/2
    theta2 = (t - sqr)/2
	  f = (s - theta1)^6/theta1 - (s^2 - t*s + 1/a)^3 + a*theta1*(s - theta2)^6
    f = change_coefficient_ring(F, f)
    f = f(x)
	  H5 = hyperelliptic_curve(f)
	  push!(twists, H5)
  end

  if is_square(a)
	  push!(twists, quadratic_twist(H5))
  end

  return twists
end


#   y^2 = x^5 + x^3 + t*x,
#   Follows [CaNa2007] and [LRS20].

function g2_models_FF_D8(igusa_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(igusa_invs[1])
  R, x = polynomial_ring(F, :x)
  J2, J4, J6, _, J10 = igusa_invs
  p = characteristic(F)

  if p == 3
	  t =  - J2^2/J4
  elseif p == 5
	  t = J4/J2^2 + F(1)
  else
	  C2, C4, C6, C10 = clebsch_from_igusa_clebsch([8*J2, 4*J2^2 - 96*J4,8*J2^3 - 160*J2*J4 - 576*J6, 4096*J10])
	  t = (8*C6*(6*C4 - C2^2) + 9*C10)/(900*C10)
  end

  f = x^5 + x^3 + t*x
  if F == QQ
    f, gamma = reduce_binary_form(f)
  end

  if !all_twists
    return [hyperelliptic_curve(f)]
  end

  if is_square(t)
    v = 1
    z0 = 1/sqrt(t)
    s0 = 0

    H1 = hyperelliptic_curve((1 + 2*t*z0)*x^6 - (8*s0*t*v)*x^5 + v*(3 - 10*t*z0)*x^4 +
        v^2*(3 - 10*t*z0)*x^2 + 8*s0*t*v^3*x + v^3*(1 + 2*t*z0))

    prim = primitive_element(F)
    twists =[H1, quadratic_twist(H1)]

    while true
      v = rand(F)
      if v == 0 || !is_square(v)
        continue
      end
      z0 = rand(F)
      if z0^2*t == 1 || !is_square(1 - z0^2*t)
        continue
      end
      if is_square((1 - z0*sqrt(t))/2)
        continue
      end
      break
    end
    s0 = sqrt((1 - z0^2*t)/v/t)

    H2 = hyperelliptic_curve((1 + 2*t*z0)*x^6 - (8*s0*t*v)*x^5 + v*(3 - 10*t*z0)*x^4 +
        v^2*(3 - 10*t*z0)*x^2 + 8*s0*t*v^3*x + v^3*(1 + 2*t*z0))
    push!(twists, H2)

    v = prim
    s0 = 0
    z0 = 1/sqrt(t)

    H3 = hyperelliptic_curve((1 + 2*t*z0)*x^6 - (8*s0*t*v)*x^5 + v*(3 - 10*t*z0)*x^4 +
        v^2*(3 - 10*t*z0)*x^2 + 8*s0*t*v^3*x + v^3*(1 + 2*t*z0))
    H4 = hyperelliptic_curve((1 - 2*t*z0)*x^6 + (8*s0*t*v)*x^5 + v*(3 + 10*t*z0)*x^4 +
        v^2*(3 + 10*t*z0)*x^2 - 8*s0*t*v^3*x + v^3*(1 - 2*t*z0))
    push!(twists, H3)
    push!(twists, H4)

    return twists
  end

  R, (x1, x2, x3) = polynomial_ring(F, [:x1,:x2, :x3])
  v = 1
  C = conic_curve(x1^2*t*v + x2^2*t - x3^2)
  P = rational_point(C)
  s0 = P[1]
  z0 = P[2]

  H5 = hyperelliptic_curve((1 + 2*t*z0)*x^6 - (8*s0*t*v)*x^5 + v*(3 - 10*t*z0)*x^4 +
	v^2*(3 - 10*t*z0)*x^2 + 8*s0*t*v^3*x + v^3*(1 + 2*t*z0))

  prim = primitive_element(F)

  twists = [H5, quadratic_twist(H5)]

  v = prim
  C = conic_curve(x1^2*t*v + x2^2*t - x3^2)
  P = rational_point(C)
  s0 = P[1]
  z0 = P[2]

  H6 = hyperelliptic_curve((1 + 2*t*z0)*x^6 - (8*s0*t*v)*x^5 + v*(3 - 10*t*z0)*x^4 +
  v^2*(3 - 10*t*z0)*x^2 + 8*s0*t*v^3*x + v^3*(1 + 2*t*z0))
  push!(twists, H6)

  return twists
end


# Automorphism group V4
# Follows [ShVo2004], [CaQu2005] and [LRS20].
function g2_models_FF_V4(igusa_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem

  F = parent(igusa_invs[1])
  R, x = polynomial_ring(F, :x)
  J2, J4, J6, _, J10 = igusa_invs

  Au = J2^5*J4^2 - 64*J2^3*J4^3 + 1024*J2*J4^4 + 3*J2^6*J6 - 202*J2^4*J4*J6 + 4014*J2^2*J4^2*J6 -
	20160*J4^3*J6 + 666*J2^3*J6^2 - 20520*J2*J4*J6^2 + 48600*J6^3 - 30*J2^4*J10 + 2800*J2^2*J4*J10 -
	192000*J4^2*J10 - 360000*J2*J6*J10

  Bu = 2*J2^4*J4*J6 - 114*J2^2*J4^2*J6 + 1344*J4^3*J6 + 6*J2^3*J6^2 + 216*J2*J4*J6^2 - 3240*J6^3 +
	18*J2^4*J10 - 1040*J2^2*J4*J10 + 12800*J4^2*J10 + 4800*J2*J6*J10

  Av = J2^6*J4^2 - 96*J2^4*J4^3+3072*J2^2*J4^4 - 32768*J4^5+3*J2^7*J6 - 164*J2^5*J4*J6 +
	1250*J2^3*J4^2*J6 + 29760*J2*J4^3*J6 + 858*J2^4*J6^2 - 22680*J2^2*J4*J6^2 -
	172800*J4^2*J6^2 + 81000*J2*J6^3 + 1176*J2^5*J10 - 79600*J2^3*J4*J10 +
	1344000*J2*J4^2*J10 - 72000*J2^2*J6*J10 - 12960000*J4*J6*J10 - 134400000*J10^2

  Bv = 3*J2^3*J4^2*J6 - 160*J2*J4^3*J6 + J2^4*J6^2 - 36*J2^2*J4*J6^2 + 3456*J4^2*J6^2 - 1188*J2*J6^3 +
	24*J2^3*J4*J10 - 1280*J2*J4^2*J10 + 160*J2^2*J6*J10 + 105600*J4*J6*J10 + 640000*J10^2

  u = Au/Bu
  v = Av/Bv
  if u != 0
    t = v^2 - 4*u^3
    a0 = v^2 + u^2*v - 2*u^3
    a1 = 2*(u^2 + 3*v)*(v^2 - 4*u^3)
    a2 =(15*v^2 - u^2*v - 30*u^3)*(v^2 - 4*u^3)
    a3 =4*(5*v - u^2)*(v^2 - 4*u^3)^2
  else
    t = one(F)
    a0 = 1 + 2*v
    a1 = 2*(3 - 4*v)
    a2 = 15 + 14*v
    a3 = 4*(5 - 4*v)
  end

  f = a0*x^6 + a1*x^5 + a2*x^4 + a3*x^3 + t*a2*x^2 + t^2*a1*x + t^3*a0
  if F == QQ
    f, gamma = reduce_binary_form(f)
  end
  H1 = hyperelliptic_curve(f)
  twists = [H1]
  if !all_twists
    return twists
  end

  q = length(F)

  if is_square(t)
    GF_q2 = GF(q^2)
    t = GF_q2(t)
    a = primitive_element(GF_q2)
    b = a^q*sqrt(t)
    c = a^q
    d = a*sqrt(t)
    H_GF_q2 = base_change(GF_q2, H1)
    H_GF_q2_twist = hyperelliptic_transform(H_GF_q2, [a, b, c, d])[1]
    f2, _ = hyperelliptic_polynomials(H_GF_q2_twist)
    f2 = f2/leading_coefficient(f2)
    f2 = change_base_ring(F, f2)(x)
    H2 = hyperelliptic_curve(f2)
    push!(twists, quadratic_twist(H1))
    push!(twists, H2)
    push!(twists, quadratic_twist(H2))
    return twists
  end

  GF_q4 = GF(q^4)
  s = primitive_element(GF_q4)
  t = GF_q4(t)
  a = s^(div((q^2 + 1), 2))
  c = a^q
  b = sqrt(t)*c
  d = sqrt(t)*c^q
  H_GF_q4 = base_change(GF_q4, H1)
  H_GF_q4_twist = hyperelliptic_transform(H_GF_q4,[a,b,c,d])[1]
  f3, _ = hyperelliptic_polynomials(H_GF_q4_twist)
  f3 = f3/leading_coefficient(f3)
  f3 = change_base_ring(F, f3)(x)
  H3 = hyperelliptic_curve(f3)
  push!(twists, H3)
  return twists
end

function g2_models_FF_C2(igusa_invs::Vector{T}, all_twists::Bool = true) where T <: FieldElem
  K = parent(igusa_invs[1])
  Kx, x = polynomial_ring(K, :x)
  J2, J4, J6, _, J10 = igusa_invs

  p = characteristic(K)

  if p == 5 && J2 == 0 && J4 == 0
    _, _, g3 = g2_from_igusa(igusa_invs)
    while true
      c = rand(K)
      test, a = is_power(3*c^2/g3, 3)
      if c != 0 && test
        f = x^5+c*x^2+a*c
        break
      end
    end
    H = hyperelliptic_curve(f)
  elseif p == 5
    P3, (x1, x2, x3) = polynomial_ring(K, [:x1, :x2, :x3])
	  if J2 == 0
	    R2 = J6^5+3*J10*J4^5+3*J6^3*J4^3+J6*J4^6
	    if !is_square(R2)
		    J4 *= R2^2
        J6 *= R2^3
        J10 *= R2^5
        R2 *= R2^15
	    end
	    R = sqrt(R2)
	    L = J6*x1^2+4*J4^2*x2*x1+4*x3^2*J4^2
	    M = (3*J4^4+4*J6^2*J4)*x1^2*x2+(4*J4^4+3*J6^2*J4)*x1*x3^2+
		      2*J4^5*x2^3+J6*J4^2*x1^3+4*x1*J6*J4^3*x2^2+4*x3*x1^2*R
	  else
      L = J2*x1^2+((J4*J2^2+2*J4^2+J2^4+4*J2*J6)*x2+(2*J2*J4^2+J6*J4+4*J2^5)*x3)*x1 +
      (J4^2*J2^3+4*J2^7+3*J6*J4^2+3*J4*J2^5+2*J4^3*J2)*x2^2+(3*J2^3*J10 +
      (3*J4+3*J2^2)*J6^2+(J2*J4^2+4*J2^5+J2^3*J4)*J6+2*J2^8+2*J2^6*J4+3*J2^2*J4^3+2*J2^4*J4^2)*x3*x2 +
      ((4*J4*J2^2+3*J2^4)*J10+2*J6^3+3*J6^2*J2^3+(2*J4*J2^4+3*J2^6+3*J4^2*J2^2)*J6 +
      4*J2^9+J4^3*J2^3)*x3^2

	    M = (3*J4*J2+3*J2^3)*x1^3+(((2*J2^3+2*J4*J2)*J6+3*J4*J2^4+J2^6+2*J4^3+2*J4^2*J2^2)*x2 +
      (4*J6^2*J2+(J4^2+3*J4*J2^2+J2^4)*J6+2*J4^3*J2+J4^2*J2^3+4*J4*J2^5+J2^7)*x3)*x1^2 +
      ((4*J10*J2^4+2*J6^2*J2^3+(4*J2^6+3*J4^3+J4^2*J2^2+2*J4*J2^4)*J6+2*J4^2*
      J2^5+J4^4*J2+3*J4^3*J2^3+J4*J2^7)*x2^2+((4*J2^5+3*J2^3*J4)*J10+(J4*J2^2+2*J2^4 +
      3*J4^2)*J6^2+(3*J4*J2^5+3*J2^7+2*J4^2*J2^3+J4^3*J2)*J6+2*J2^10+2*J4^4*J2^2 +
      J4*J2^8+3*J4^2*J2^6)*x3*x2+((4*J4^2*J2^2+J4*J2^4+3*J6*J2^3)*J10 +
      (2*J4+4*J2^2)*J6^3+(4*J2*J4^2+2*J2^5)*J6^2+(J2^2*J4^3+2*J2^4*J4^2+J2^6*J4)*J6 +
      3*J2^11+2*J4^3*J2^5+J4^4*J2^3+2*J4^2*J2^7)*x3^2)*x1+((J4*J2^5+J2^7+J6*J2^4)*J10 +
      (3*J2^6+2*J4^2*J2^2+J4*J2^4)*J6^2+(3*J4^3*J2^3+J2^9+2*J4^2*J2^5)*J6+2*J4*J2^10+2*J2^12 +
      3*J4^3*J2^6+4*J4^5*J2^2+3*J4^2*J2^8)*x2^3+(((4*J2^5+2*J2^3*J4)*J6+J2^6*J4+4*J2^8 +
      J2^2*J4^3+4*J2^4*J4^2)*J10+(2*J2^4+2*J4*J2^2)*J6^3+(J4*J2^5+4*J2^7+J4^2*J2^3 +
      4*J4^3*J2)*J6^2+(4*J2^4*J4^3+2*J2^10+2*J4^2*J2^6+4*J4^4*J2^2+3*J4*J2^8)*J6 +
      J4^5*J2^3+3*J4^2*J2^9+3*J4^3*J2^7+2*J2^13)*x3*x2^2+((J6^2*J2^3+(J4^2*J2^2+2*J2^6 +
      2*J4*J2^4)*J6+2*J4^3*J2^3+J2^9+4*J4*J2^7)*J10+3*J6^4*J2^2+(2*J2^3*J4+J2^5 +
      4*J2*J4^2)*J6^3+(3*J2^8+4*J2^4*J4^2+3*J2^2*J4^3)*J6^2+(J2^11 +
      J4*J2^9+3*J4^4*J2^3)*J6+2*J4^5*J2^4+3*J4^4*J2^6+2*J4^2*J2^10)*x3^2*x2 +
      (3*J10^2*J2^5+((4*J4*J2^2+2*J2^4)*J6^2+(3*J4*J2^5+3*J4^2*J2^3+J2^7)*J6 +
      J4^2*J2^6+3*J2^4*J4^3+2*J4*J2^8+3*J2^10)*J10+(J2^3+J4*J2)*J6^4+(J4^2*J2^2 +
      3*J2^6+3*J4*J2^4)*J6^3+(2*J4^2*J2^5+2*J4^3*J2^3+4*J4*J2^7+J2^9)*J6^2 +
      (3*J4^2*J2^8+4*J4^3*J2^6+4*J4^4*J2^4)*J6+J2^15+3*J4*J2^13+3*J4^2*J2^11 +
      J4^4*J2^7+2*J4^3*J2^9)*x3^3
    end
    P = parametrization(conic_curve(L))

    f = evaluate(M, [P[1],P[2],P[3]])
    g = evaluate(f, [x, Kx(1)])
    H = hyperelliptic_curve(g)
  else
    H = reconstruct_from_igusa_C2(igusa_invs)
  end
  if !all_twists
    return [H]
  else
    return [H, quadratic_twist(H)]
  end
end

