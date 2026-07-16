
################################################################################
#
#  HypellCrv/G2Rec.jl : Reconstruction of genus 2 curves from their invariants
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
# [LR12]     R. Lercier and C. Ritzenthaler
#            "Hyperelliptic curves and their invariants: geometric, arithmetic and algorithmic aspects."
#            J. Algebra 372, pp. 595–636, 2012.
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

#Function that decides which method to call based on the characteristic of the field.
function models_from_igusa_invariants(igusa_invs::Vector{T}, all_twists::Bool = false) where T <: FieldElem
  K = parent(igusa_invs[1])
  p = characteristic(K)

  if p == 2
    g2_invs = g2_from_igusa(igusa_invs)
    return models_from_g2_invariants_char2(g2_invs, all_twists)
  elseif p == 3
    return models_from_igusa_invariants_char3(igusa_invs, all_twists)
  elseif p == 5
    return models_from_igusa_invariants_char5(igusa_invs, all_twists)
  else
    return models_from_igusa_invariants_general_char(igusa_invs, all_twists)
  end
end

#Reconstruct only returns one model. Twists returns all twists, but only works over finite fields.

@doc raw"""
    reconstruct_from_igusa(igusa_invs::Vector{T})

Construct a genus 2 curve whose Igusa invariants are equal
(as elements of P(2, 4, 6, 8, 10)) to the input vector igusa_invs.
"""
function reconstruct_from_igusa(igusa_invs::Vector{T}) where T <: FieldElem
  return models_from_igusa_invariants(igusa_invs, false)[1]
end

@doc raw"""
    reconstruct_from_igusa(igusa_invs::Vector{T})

Construct a genus 2 curve whose Cardona-Quer-Nart-Pujolas invariants are equal
to the input vector igusa_invs.
"""
function reconstruct_from_g2(g2_invs::Vector{T}) where T <: FieldElem
  return models_from_igusa_invariants(igusa_from_g2(g2_invs), false)[1]
end

@doc raw"""
    twists(C::HypellCrv{FinFieldElem})

Compute all the twists of the hyperelliptic curve C.
This function has only been implemented for curves of genus 2
"""
function twists(C::HypellCrv{FinFieldElem})
  @req genus(C) == 2 "twists has only been implemented for hyperelliptic curves of genus 2."
  return twists_from_igusa(igusa_invariants(C))
end

function twists_from_igusa(igusa_invs::Vector{T}) where T <: FinFieldElem
  return models_from_igusa_invariants(igusa_invs, true)
end

function twists_from_g2(g2_invs::Vector{T}) where T <: FinFieldElem
  return models_from_igusa_invariants(igusa_from_g2(g2_invs), true)
end

# Reconstruction over the rational numbers following [LR12] and [LRS20].
function reconstruct_from_igusa_C2(igusa_invs::Vector{T}) where T <: Union{ZZRingElem, QQFieldElem}
  K = parent(igusa_invs[1])

  if length(igusa_invs)!= 6
    J2, J4, J6, J8, J10 = igusa_invs
    J15_squared = 2^22*(J2^6*J6^3 - 2*J2^5*J4^2*J6^2 + J2^4*J4^4*J6 -
    72*J10*J2^5*J4*J6 + 8*J10*J2^4*J4^3 - 72*J2^4*J4*J6^3 +
    136*J2^3*J4^3*J6^2 - 64*J2^2*J4^5*J6 - 432*J10^2*J2^5 -
    48*J10*J2^4*J6^2 + 4816*J10*J2^3*J4^2*J6 - 512*J10*J2^2*J4^4 +
    216*J2^3*J6^4 + 1080*J2^2*J4^2*J6^3 - 2304*J2*J4^4*J6^2 + 1024*J4^6*J6 +
    28800*J10^2*J2^3*J4 - 12960*J10*J2^2*J4*J6^2 - 84480*J10*J2*J4^3*J6 +
    8192*J10*J4^5 - 7776*J2*J4*J6^4 + 6912*J4^3*J6^3 - 96000*J10^2*J2^2*J6 -
    512000*J10^2*J2*J4^2 - 129600*J10*J2*J6^3 + 691200*J10*J4^2*J6^2 +
    11664*J6^5 + 11520000*J10^2*J4*J6 + 51200000*J10^3)

    if J15_squared < 0
      J15_squared *= -1
      igusa_invs *= -1
    end
    if is_square(J15_squared)
      J15 = sqrt(J15_squared)
      push!(igusa_invs, J15)
    end
    #TODO: If J15_squared is not a square, one could optionally try to find how one can find a
    # different representative of [J2 : J4 : J6 : J8 : J10 : J15] in weighted projective space such that
    # it is a square. J15 allows us to find equations with smaller coefficients during reconstruction.
  end


  # One can construct the function R based on three covariants q1, q2, q3 of order 2 as in 2.1 of [LR12]
  # If we let q3 be a linear combination of covariants instead, we can try to minimize R
  # for chosen values of u and v. See also [Mes91] 1.3 for the covariants of sextic forms.
  if length(igusa_invs) == 6
    igusa_invs = weighted_reduction(igusa_invs, [2,4,6,8,10,15])
    J2, J4, J6, _, J10, J15 = igusa_invs
    Kuv, (u,v) = polynomial_ring(K, ["u","v"])
    R = (188160*u - 75600*v)*J2^4*J10 + (-10035200*u + 4416000*v)*J2^2*J4*J10 +
      (-225792000*u - 36000000*v)*J2*J6*J10 - 61440000*v*J4^2*J10 +
      (2352*u+135*v)*J2^6*J6 + (784*u + 45*v)*J2^5*J4^2 +
      (-134848*u - 17340*v)*J2^4*J4*J6 + (-50176*u - 2880*v)*J2^3*J4^3 +
      (592704*u+5220*v)*J2^3*J6^2 + (1806336*u + 650880*v)*J2^2*J4^2*J6 +
      (802816*u+46080*v)*J2*J4^4 + (-13547520*u - 1814400*v)*J2*J4*J6^2 -
      6451200*v*J4^3*J6 + 15552000*v*J6^3
    if R != 0
      compute_conic_and_cubic = compute_conic_and_cubic_1245
    else
      #If the choses linear combination didn't work, we try a different one.
      R = -1536000000*J10^2*v + 960*(13*v + u)*J2^5*J10 -
      54400*(2*u + 15*v)*J4*J2^3*J10 - 288000*(-9*v + 4*u)*J6*J2^2*J10 +
      1536000*(9*v + 2*u)*J4^2*J2*J10 + 69120000*(u - 3*v)*J4*J6*J10 +
      3*(4*u + v)*J6*J2^7 + (4*u + v)*J4^2*J2^6 - 4*(352*u - 177*v)*J6*J4*J2^5 -
      16*(31*u + 14*v)*J4^3*J2^4 + 84*(36*u + 29*v)*J6^2*J2^4 +
      16*(3156*u - 3431*v)*J6*J4^2*J2^3 + 1024*(19*u + 11*v)*J4^4*J2^2 -
      8640*(-11*v + 29*u)*J6^2*J4*J2^2 - 7680*(72*u - 121*v)*J6*J4^3*J2 +
      648000*J6^3*J2*v - 81920*(3*u + 2*v)*J4^5 + 1382400*(3*u - 4*v)*J6^2*J4^2

      if R != 0
        compute_conic_and_cubic = compute_conic_and_cubic_1246
      else
      # Otherwise we fall back to the default one.
        return _reconstruct_from_igusa_generic(igusa_invs)
      end
    end
  else
    return _reconstruct_from_igusa_generic(igusa_invs)
  end

  U, V = minimize_linear_equation(R)

  conic, cubic = compute_conic_and_cubic(igusa_invs, U,V)
  conic = conic/content(conic)
  cubic = cubic/content(cubic)

  conic_model, phi, _ = minimal_model(conic_curve(QQ, conic))
  cubic = evaluate(cubic, phi)

  ct = gcd([denominator(c) for c in coefficients(cubic)]) //gcd([numerator(c) for c in coefficients(cubic)])
  cubic *= ct
  P = parametrization(conic_model)


  f = evaluate(cubic, [P[1],P[2],P[3]])
  K = base_ring(f)
  Kx, x = polynomial_ring(K)

  g = evaluate(f, [x, Kx(1)])
  g_rev = evaluate(f, [Kx(1), x])

  if abs(leading_coefficient(g_rev)) <= abs(leading_coefficient(g))
    g = g_rev
  end
  g = reduce_binary_form(g)[1]
  a = leading_coefficient(g)
  return hyperelliptic_curve(g/a)
end

function reconstruct_from_igusa_C2(igusa_invs::Vector{T}) where T <: FieldElem
  K = parent(igusa_invs[1])
  igusa_invs = igusa_invs[(1:5)]
  R, conic, cubic = compute_conic_and_cubic_generic(igusa_invs)
  C = conic_curve(K, conic)
  bool, P = has_rational_point_with_point(C)
  if bool
    P = parametrization(C, P)
  else
    #println("Reconstruction not possible over base field. Reconstructing over quadratic extension.")
    P = _parametrization_geometric(C)
    K = base_ring(P[1])
  end
  Kx, x = polynomial_ring(K)
  f = evaluate(cubic, [P[1],P[2],P[3]])
  g = evaluate(f, [x, Kx(1)])
  a = leading_coefficient(g)
  return hyperelliptic_curve(g/a)
end

function compute_conic_and_cubic_generic(igusa_invs::Vector{T}) where T <: Union{ZZRingElem, FieldElem}

  J2, J4, J6, J8, J10 = igusa_invs

  K = parent(igusa_invs[1])
  K, (x, y, z) = polynomial_ring(K, ["x","y","z"])

  R = J2^6*J6^3 - 2*J2^5*J4^2*J6^2 + J2^4*J4^4*J6 - 72*J10*J2^5*J4*J6 +
  8*J10*J2^4*J4^3 - 72*J2^4*J4*J6^3 + 136*J2^3*J4^3*J6^2 - 64*J2^2*J4^5*J6 -
  432*J10^2*J2^5 - 48*J10*J2^4*J6^2 + 4816*J10*J2^3*J4^2*J6 -
  512*J10*J2^2*J4^4 + 216*J2^3*J6^4 + 1080*J2^2*J4^2*J6^3 -
  2304*J2*J4^4*J6^2 + 1024*J4^6*J6 + 28800*J10^2*J2^3*J4 -
  12960*J10*J2^2*J4*J6^2 - 84480*J10*J2*J4^3*J6 + 8192*J10*J4^5 -
  7776*J2*J4*J6^4 + 6912*J4^3*J6^3 - 96000*J10^2*J2^2*J6 -
  512000*J10^2*J2*J4^2 - 129600*J10*J2*J6^3 + 691200*J10*J4^2*J6^2 +
  11664*J6^5 + 11520000*J10^2*J4*J6 + 51200000*J10^3
  if R == zero(K) then
      error("Could not reconstruct conic.")
  end

  conic = (-3600*J6 - 160*J4*J2+3*J2^3)*x^2 +
  (6000*J6*J2+6400*J4^2 - 360*J4*J2^2 + 6*J2^4)*x*y +
  (-1600000*J10 + (-96000*J4 - 800*J2^2)*J6 - 400*J4*J2^3 +
    6400*J4^2*J2 + 6*J2^5)*x*z + (-800000*J10 + (-48000*J4-400*J2^2)*J6 -
    200*J4*J2^3+3200*J4^2*J2+3*J2^5)*y^2 + (360000*J6^2 + (-8000*J4*J2 +
    2400*J2^3)*J6 + 10000*J4^2*J2^2 - 440*J4*J2^4+6*J2^6-64000*J4^3)*y*z +
    ((-600000*J2^2 + 8000000*J4)*J10 - 150000*J6^2*J2 + (300*J2^4 -
    38000*J4*J2^2+320000*J4^2)*J6 + 3*J2^7 - 240*J4*J2^5 + 6100*J4^2*J2^3 -
    48000*J4^3*J2)*z^2

  cubic = (-3200000*J10 + (-288000*J4+600*J2^2)*J6 -
  100*J4*J2^3 + 3200*J4^2*J2+J2^5)*x^3 + (4000000*J10*J2 + 2160000*J6^2 +
  (-1600*J2^3 + 432000*J4*J2)*J6 - 128000*J4^3 - 320*J4*J2^4 + 3*J2^6 +
  10400*J4^2*J2^2)*x^2*y + ((32000000*J4 - 2400000*J2^2)*J10 - 160000*J4^3*J2 +
  13000*J4^2*J2^3 - 2700000*J6^2*J2 - 180000*J6*J4*J2^2 -
  340*J4*J2^5 + 3*J2^7)*x^2*z + ((32000000*J4 -2400000*J2^2)*J10 -
  160000*J4^3*J2 + 13000*J4^2*J2^3 - 2700000*J6^2*J2 - 180000*J6*J4*J2^2 -
  340*J4*J2^5 + 3*J2^7)*x*y^2 + ((16000000*J4*J2 + 1200000*J2^3 +
    960000000*J6)*J10 + (43200000*J4 + 3060000*J2^2)*J6^2 +
  (-1800*J2^5 + 260000*J4*J2^3 - 960000*J4^2*J2)*J6 + 2560000*J4^4 -
  496000*J4^3*J2^2 + 29800*J4^2*J2^4 + 6*J2^8 - 720*J4*J2^6)*x*y*z +
  ((-800000*J2^4 - 200000000*J6*J2 - 320000000*J4^2 + 28000000*J4*J2^2)*J10 -
  108000000*J6^3 + (-5400000*J4*J2 - 1405000*J2^3)*J6^2 +
  (-880000*J4^2*J2^2 - 3000*J4*J2^4 - 550*J2^6 + 6400000*J4^3)*J6 +
  17350*J4^2*J2^5 - 380*J4*J2^7 + 3*J2^9 + 2240000*J4^4*J2 -
  334000*J4^3*J2^3)*x*z^2 + ((-8000000*J4*J2 + 400000*J2^3 -
    80000000*J6)*J10 + (-7200000*J4 + 1140000*J2^2)*J6^2 + (2200*J2^5 -
    100000*J4*J2^3 + 1760000*J4^2*J2)*J6 + 1280000*J4^4 - 136000*J4^3*J2^2 +
  5800*J4^2*J2^4 + J2^8 - 120*J4*J2^6)*y^3 + ((-1400000*J2^4 -
  800000000*J6*J2 - 960000000*J4^2 + 64000000*J4*J2^2)*J10 + 54000000*J6^3 +
  (-37800000*J4*J2 - 760000*J2^3)*J6^2 + (7700000*J4^2*J2^2 -
  318000*J4*J2^4 + 3200*J2^6 - 60800000*J4^3)*J6 + 18600*J4^2*J2^5 -
  380*J4*J2^7 + 3*J2^9 + 3520000*J4^4*J2 - 414000*J4^3*J2^3)*z*y^2 +
  (160000000000*J10^2 + ((20000000000*J4 + 100000000*J2^2)*J6 +
  70000000*J4*J2^3 - 1200000000*J4^2*J2 - 900000*J2^5)*J10 +
  (648000000*J4^2 - 7200000*J4*J2^2 + 895000*J2^4)*J6^2 +
  (6480000*J4^2*J2^3 - 129000*J4*J2^5 + 1050*J2^7 - 94400000*J4^3*J2)*J6 -
  12800000*J4^5 + 4880000*J4^4*J2^2 - 480000*J4^3*J2^4 + 20350*J4^2*J2^6 -
  400*J4*J2^8 + 3*J2^10)*z^2*y + ((3200000000*J4^3 - 20000000000*J6^2 +
  24000000*J4*J2^4 - 350000*J2^6 - 100000000*J6*J2^3 -
  520000000*J4^2*J2^2)*J10 + (19500000*J2^2 - 1260000000*J4)*J6^3 +
  (-80000*J2^5 - 10250000*J4*J2^3 + 122000000*J4^2*J2)*J6^2 +
  (-29000000*J4^3*J2^2 + 1325000*J4^2*J2^4 + 50*J2^8 + 224000000*J4^4 -
  23500*J4*J2^6)*J6 + J2^11 + 2300000*J4^4*J2^3 - 193500*J4^3*J2^5 +
  7550*J4^2*J2^7 - 9600000*J4^5*J2 - 140*J4*J2^9)*z^3

  return R, conic, cubic
end

function compute_conic_and_cubic_1245(igusa_invs::Vector{T}, u, v) where T <: Union{QQFieldElem, ZZRingElem}
  J2, J4, J6, _, J10, J15 = igusa_invs

  K = parent(igusa_invs[1])
  K, (x, y, z) = polynomial_ring(K, ["x","y","z"])

  conic = 153837509765625*(3*J2^3 - 160*J2*J4 - 3600*J6)*x^2 +
        9845600625000*(3*J2^4 - 180*J4*J2^2 + 3000*J2*J6 + 3200*J4^2)*x*y +
        157529610000*(3*J2^5 - 200*J4*J2^3 - 400*J6*J2^2 + 3200*J4^2*J2 -
        48000*J4*J6 - 800000*J10)*y^2+186046875*v*J15*y*z +
        4*(-3686400000000*v^2*J10^2 -
        240*(784*u+45*v)*(784*u - 675*v)*J2^5*J10 + 12800*(614656*u^2 -
        540960*u*v - 43875*v^2)*J2^3*J4*J10 + 288000*(614656*u^2 + 196000*u*v +
        6025*v^2)*J2^2*J6*J10 + 860160000*v*(15*v + 112*u)*J2*J4^2*J10 -
        608256000000*v^2*J10*J6*J4 - 3*(784*u + 45*v)^2*J2^7*J6 -
        (784*u+45*v)^2*J2^6*J4^2 + 4*(33712*u + 6735*v)*(784*u + 45*v)*
        J2^5*J4*J6 + 64*(784*u + 45*v)^2*J2^4*J4^3 -
        36*(12907776*u^2+227360*u*v + 130525*v^2)*J2^4*J6^2 - 9216*
        (153664*u^2 + 110740*u*v+7725*v^2)*J2^3*J4^2*J6 -
        1024*(784*u + 45*v)^2*J2^2*J4^4 +
        120960*(87808*u^2 + 23520*u*v + 2775*v^2)*J2^2*J4*J6^2 +
        1843200*v*(815*v + 5488*u)*J2*J4^3*J6 -
        217728000*v*(-25*v + 112*u)*J2*J6^3 - 19906560000*v^2*J6^2*J4^2)*z^2

  cubic = 195385944403125000000000*(J2^5 - 100*J4*J2^3 + 600*J6*J2^2 + 3200*J4^2*J2 - 288000*J4*J6 - 3200000*J10)*x^3 +
        6252350220900000000000*(3*J2^6 - 320*J4*J2^4 - 1600*J6*J2^3 + 10400*J4^2*J2^2 + 432000*J6*J4*J2 - 128000*J4^3 + 4000000*J2*J10 + 2160000*J6^2)*x^2*y +
        184605011718750000*J15*J2*(-784*u - 25*v)*x^2*z +
        200075207068800000000*(3*J2^7 - 340*J4*J2^5 + 13000*J4^2*J2^3 - 180000*J6*J4*J2^2 - 160000*J4^3*J2 - 2400000*J2^2*J10 - 2700000*J6^2*J2 + 32000000*J10*J4)*x*y^2 +
        4922800312500000*((784*u + 69*v)*J15*J2^2 - 1920*v*J4*J15)*x*y*z +
        2540160000*(-224*(784*u + 45*v)^2*J2^6*J4^3 + 12*(124775168*u^2 - 96063520*u*v - 5444925*v^2)*J2^6*J6^2 + 11264*(784*u + 45*v)^2*J2^4*J4^4 + 648000*(614656*u^2 - 556640*u*v + 6665*v^2)*J2^3*J6^3 - 163840*(784*u + 45*v)^2*J2^2*J4^5 - 1536000000*(614656*u^2 + 39200*u*v + 5025*v^2)*J2^2*J10^2 + 3*(784*u + 45*v)^2*J2^9*J6 + (784*u + 45*v)^2*J2^8*J4^2 + 165888000000*v*(75*v + 784*u)*J2*J6^2*J10 + 12*(784*u + 45*v)*(46256*u + 1055*v)*J2^7*J4*J6 - 147456000*v*(745*v + 8624*u)*J2*J4^4*J6 + 12441600000*v*(11*v + 784*u)*J2*J4*J6^3 - 69120000*(1843968*u^2 + 54880*u*v + 33875*v^2)*J2^2*J4*J6*J10 - 9830400000*v*(75*v + 784*u)*J2*J4^3*J10 - 16*(2108884736*u^2 + 277841760*u*v + 7919775*v^2)*J2^5*J4^2*J6 + 2880*(20283648*u^2 + 26538400*u*v + 2424425*v^2)*J2^4*J4*J6^2 + 53760*(10624768*u^2 + 2621920*u*v + 119775*v^2)*J2^3*J4^3*J6 - 5529600*(614656*u^2 + 235200*u*v + 46875*v^2)*J2^2*J4^2*J6^2 + 960*(784*u + 45*v)*(10192*u + 405*v)*J2^7*J10 - 48000*(10449152*u^2 + 1224608*u*v + 32985*v^2)*J2^5*J4*J10 + 96000*(16595712*u^2 + 525280*u*v + 229875*v^2)*J2^4*J6*J10 + 4608000*(1843968*u^2 + 305760*u*v + 11875*v^2)*J2^3*J4^2*J10 + 3450470400000*v^2*J4^3*J6^2 + 294912000000000*v^2*J4*J10^2 - 4478976000000*v^2*J6^4 + 66355200000000*v^2*J4^2*J6*J10)*x*z^2 +
        6402406626201600000*(J2^8 - 120*J2^6*J4 + 2200*J2^5*J6 + 5800*J2^4*J4^2 - 100000*J2^3*J4*J6 - 136000*J2^2*J4^3 + 400000*J2^3*J10 + 1140000*J2^2*J6^2 + 1760000*J2*J4^2*J6 + 1280000*J4^4 - 8000000*J2*J4*J10 - 7200000*J4*J6^2 - 80000000*J6*J10)*y^3 +
        15752961000000*(-3*(784*u + 45*v)*J15*J2^3 + 280*(15*v + 112*u)*J15*J2*J4 + 72000*v*J6*J15)*y^2*z +
        81285120*(3*(784*u + 45*v)^2*J2^10*J6 + (784*u + 45*v)^2*J2^9*J4^2 - 64*(784*u + 45*v)^2*J2^7*J4^3 - 4*(301796096*u^2 - 104593440*u*v - 8437725*v^2)*J2^7*J6^2 + 1024*(784*u + 45*v)^2*J2^5*J4^4 - 86400*(4302592*u^2 - 1230880*u*v - 69625*v^2)*J2^4*J6^3 + 640000000*(614656*u^2 + 108192*u*v + 1305*v^2)*J2^3*J10^2 - 5529600000*v*(145*v + 784*u)*J2*J4^3*J6^2 + 120960000*(614656*u^2 + 70560*u*v + 3625*v^2)*J2^3*J4*J6*J10 - 2457600000000*v*(15*v + 784*u)*J2*J4*J10^2 + 143360000*(784*u + 825*v)*(15*v + 112*u)*J2^2*J4^3*J10 - 4*(159152*u + 13935*v)*(784*u + 45*v)*J2^8*J4*J6 - 18662400000*v*(-275*v + 784*u)*J2*J6^4 - 240*(18032*u + 1755*v)*(784*u + 45*v)*J2^8*J10 + 1600*(143214848*u^2 + 30364320*u*v + 1357425*v^2)*J2^6*J4*J10 - 16000*(69456128*u^2 + 1952160*u*v + 516825*v^2)*J2^5*J6*J10 - 4480000*(965888*u^2 + 333984*u*v + 20925*v^2)*J2^4*J4^2*J10 + 172800000*(614656*u^2 - 117600*u*v - 32775*v^2)*J2^2*J6^2*J10 + 32*(852527872*u^2 + 181127520*u*v + 8127675*v^2)*J2^6*J4^2*J6 - 9600*(614656*u^2 + 2654624*u*v + 363945*v^2)*J2^5*J4*J6^2 - 640*(705010432*u^2 + 273137760*u*v + 17674875*v^2)*J2^4*J4^3*J6 + 115200*(12907776*u^2 + 4257120*u*v + 934625*v^2)*J2^3*J4^2*J6^2 + 1536000*(614656*u^2 + 1168160*u*v + 143025*v^2)*J2^2*J4^4*J6 + 5184000*(614656*u^2 - 148960*u*v - 87375*v^2)*J2^2*J4*J6^3 - 1474560000000*v^2*J4^5*J6 - 4976640000000*v^2*J4^2*J6^3 - 11796480000000*v^2*J4^4*J10 - 2211840000000000*v^2*J6*J10^2 - 110592000000*v*(65*v + 2352*u)*J2*J4^2*J6*J10 - 298598400000000*v^2*J4*J6^2*J10)*y*z^2 +
        ((784*u + 45*v)^3*J15*J2^8 - 32*(1568*u + 165*v)*(784*u + 45*v)^2*J15*J2^6*J4 + 384*(784*u + 45*v)*(307328*u^2 + 84280*u*v - 11175*v^2)*J15*J2^5*J6 + 1024*(195*v + 784*u)*(784*u + 45*v)^2*J15*J2^4*J4^2 - 5760*(481890304*u^3 + 193616640*u^2*v - 1352400*u*v^2 - 3024375*v^3)*J15*J2^3*J4*J6 - 128000*(-15*v + 784*u)*(614656*u^2 + 70560*u*v + 16425*v^2)*J15*J2^3*J10 - 2457600*v*(784*u + 45*v)^2*J15*J2^2*J4^3 + 10368000*v*(784*u + 5*v)*(784*u - 155*v)*J15*J2^2*J6^2 + 1105920000*v^2*(-365*v + 2352*u)*J15*J2*J4^2*J6 + 73728000000*v^2*(-15*v + 784*u)*J15*J2*J4*J10 + 1990656000000*v^3*J4*J6^2*J15 + 44236800000000*v^3*J6*J10*J15)*z^3;

  return conic, cubic
end

function compute_conic_and_cubic_1246(igusa_invs::Vector{T}, u, v) where T <: Union{QQFieldElem, ZZRingElem}

  J2, J4, J6, _, J10, J15 = igusa_invs

  K = parent(igusa_invs[1])
  K, (x, y, z) = polynomial_ring(K, ["x","y","z"])

  conic = 158939263916015625*(3*J2^3 - 160*J2*J4 - 3600*J6)*x^2 +
      10172112890625000*(3*J2^4 - 180*J4*J2^2 + 3000*J2*J6 + 3200*J4^2)*x*y +
      299003906250*v*J15*x*z + 162753806250000*(3*J2^5 - 200*J4*J2^3 -
      400*J6*J2^2 + 3200*J4^2*J2 - 48000*J4*J6 - 800000*J10)*y^2 -
      3986718750*v*J2*J15*y*z + 1024*( - 43200*v*(611*v + 120*u)*J6^3*J2^3 +
      81920*(3*u + 2*v)*(23*u + 12*v)*J4^5*J2^2 - 122880000000*v*(v +
      6*u)*J4*J10^2 + 32*(23*u + 12*v)*(4*u + v)*J4^3*J2^6 - 240*(4*u +
      103*v)*(4*u + v)*J2^7*J10 + 256000000*v*(11*v + 48*u)*J2^2*J10^2 -
      11520000*(48*u^2 - 252*u*v - 47*v^2)*J2^2*J4*J6*J10 + 4*(4*u +
      v)*(532*u - 397*v)*J6*J4*J2^7 + 62208000*v*(13*v +
      5*u)*J6^3*J4*J2 - 4*(3024*u^2 + 4872*u*v + 29929*v^2)*J2^6*J6^2 -
      256*(769*u^2 + 772*u*v + 184*v^2)*J2^4*J4^4 + 110592000*(9*u^2 -
      24*u*v + 5*v^2)*J4^3*J6^2 - 1866240000*v^2*J6^4 - (4*u +
      v)^2*J4^2*J2^8 - 3*(4*u + v)^2*J6*J2^9 + 13824000000*J2*J6^2*J10*v^2 -
      6553600*(3*u + 2*v)^2*J4^6 + 3200*(208*u^2 + 3912*u*v +
      863*v^2)*J2^5*J4*J10 + 32000*(144*u^2 - 648*u*v -
      137*v^2)*J2^4*J6*J10 - 1536000*(25*u^2 + 327*u*v +
      68*v^2)*J2^3*J4^2*J10 + 81920000*(9*u^2 + 81*u*v +
      17*v^2)*J2*J4^3*J10 + 5529600000*(3*u^2 - 18*u*v - v^2)*J10*J4^2*J6 -
      16*(33744*u^2 - 48688*u*v - 7731*v^2)*J2^5*J4^2*J6 + 2880*(600*u^2 +
      142*u*v + 2693*v^2)*J2^4*J4*J6^2 + 2560*(5598*u^2 - 13197*u*v -
      1096*v^2)*J2^3*J4^3*J6 - 691200*(111*u^2 - 130*u*v +
      207*v^2)*J2^2*J4^2*J6^2 - 3686400*(36*u^2 - 121*u*v -
      5*v^2)*J2*J4^4*J6)*z^2;

  cubic = 50691691485214233398437500*(J2^5 - 100*J4*J2^3 + 600*J6*J2^2 +
      3200*J4^2*J2 - 288000*J4*J6 - 3200000*J10)*x^3 +
      1622134127526855468750000*(3*J2^6 - 320*J4*J2^4 - 1600*J6*J2^3 +
      10400*J4^2*J2^2 + 432000*J6*J4*J2 - 128000*J4^3 + 4000000*J2*J10 +
      2160000*J6^2)*x^2*y + 3973481597900390625*( - (24*u + 11*v)*J15*J2^2 +
      480*(3*u + v)*J15*J4)*x^2*z + 51908292080859375000000*(3*J2^7 -
      340*J4*J2^5 + 13000*J4^2*J2^3 - 180000*J6*J4*J2^2 - 160000*J4^3*J2 -
      2400000*J2^2*J10 - 2700000*J6^2*J2 + 32000000*J10*J4)*x*y^2 +
      508605644531250000*((5*u + 3*v)*J15*J2^3 - 20*(15*u + 8*v)*J15*J2*J4 -
      3600*v*J6*J15)*x*y*z + 163296000000*(3*(4*u + v)^2*J2^11*J6 + (4*u +
      v)^2*J4^2*J2^10 - 1048576000*(3*u + 2*v)^2*J4^7 +
      3276800000*(243*u^2 + 204*u*v + 85*v^2)*J2*J4^4*J10 -
      147456000000*(81*u^2 + 18*u*v + 25*v^2)*J4^3*J6*J10 -
      64*(32264*u^2 + 27372*u*v + 3189*v^2)*J2^7*J4^2*J6 - 640*(4932*u^2 +
      186735*u*v + 703*v^2)*J2^6*J4*J6^2 + 640*(251640*u^2 + 127844*u*v +
      15521*v^2)*J2^5*J4^3*J6 - 230400*(567*u^2 - 21126*u*v +
      4885*v^2)*J2^4*J4^2*J6^2 - 102400*(48303*u^2 + 14592*u*v +
      3550*v^2)*J2^3*J4^4*J6 - 1728000*(720*u^2 + 11076*u*v -
      2755*v^2)*J2^3*J4*J6^3 + 55296000*(291*u^2 - 1322*u*v +
      520*v^2)*J2^2*J4^3*J6^2 + 147456000*(363*u^2 + 60*u*v +
      37*v^2)*J2*J4^5*J6 + 2488320000*(15*u^2 + 156*u*v -
      79*v^2)*J2*J4^2*J6^3 - 12800*(2892*u^2 + 2653*u*v +
      457*v^2)*J2^7*J4*J10 + 64000*(648*u^2 + 548*u*v +
      7449*v^2)*J2^6*J6*J10 + 128000*(19584*u^2 + 16884*u*v +
      3977*v^2)*J2^5*J4^2*J10 - 20480000*(3591*u^2 + 2992*u*v +
      974*v^2)*J2^3*J4^3*J10 - 115200000*v*( - 539*v + 960*u)*J2^3*J6^2*J10 +
      61440000000*(2*u + v)*(24*u + 7*v)*J2^2*J4*J10^2 + 4*(348*u +
      617*v)*(4*u + v)*J2^9*J4*J6 + 480*(104*u + 77*v)*(4*u + v)*J2^9*J10 -
      32*(43*u + 17*v)*(4*u + v)*J4^3*J2^8 + 6553600*(3*u + 2*v)*(49*u +
      26*v)*J4^6*J2^2 + 933120000*v*( - 3*v + 16*u)*J2^2*J6^4 -
      298598400000*v*( - 2*v + 3*u)*J4*J6^4 + 110592000000*v*( - 53*v +
      60*u)*J2*J4*J6^2*J10 + 9953280000000*v^2*J6^3*J10 -
      17694720000*(18*u^2 - 15*u*v + 7*v^2)*J4^4*J6^2 - 512000000*(48*u^2 +
      44*u*v + 9*v^2)*J2^4*J10^2 - 29491200000000*(3*u^2 + 2*u*v +
      v^2)*J4^2*J10^2 + 4*(9744*u^2 + 239432*u*v + 88149*v^2)*J2^8*J6^2 +
      256*(2609*u^2 + 2192*u*v + 424*v^2)*J4^4*J2^6 + 172800*(60*u^2 +
      1222*u*v + 267*v^2)*J2^5*J6^3 - 40960*(907*u^2 + 936*u*v +
      232*v^2)*J4^5*J2^4 - 55296000000000*v^2*J2*J6*J10^2 -
      2560000*(3240*u^2 + 2514*u*v + 12809*v^2)*J2^4*J4*J6*J10 +
      921600000*(594*u^2 + 330*u*v + 709*v^2)*J2^2*J4^2*J6*J10)*x*z^2 +
      1661065346587500000000*(J2^8 - 120*J2^6*J4 + 2200*J2^5*J6 +
      5800*J2^4*J4^2 - 100000*J2^3*J4*J6 - 136000*J2^2*J4^3 +
      400000*J2^3*J10 + 1140000*J2^2*J6^2 + 1760000*J2*J4^2*J6 +
      1280000*J4^4 - 8000000*J2*J4*J10 - 7200000*J4*J6^2 -
      80000000*J6*J10)*y^3 + 2034422578125000*( - 3*(4*u - 7*v)*J15*J2^4 +
      20*(44*u - 63*v)*J15*J4*J2^2 + 21000*v*J2*J6*J15 - 3200*(3*u -
      7*v)*J15*J4^2)*y^2*z + 1275750*(209715200*(5717280*u^2 - 3816646*u*v +
      161031*v^2)*J6*J4*J2^5*J10 - 838860800*(95482260*u^2 - 64933272*u*v -
      1000583*v^2)*J6*J4^2*J2^3*J10 + 226492416000*(929280*u^2 - 682516*u*v +
      50951*v^2)*J6^2*J4*J2^2*J10 + 402653184000*(3500235*u^2 - 2404392*u*v -
      75013*v^2)*J6*J4^3*J2*J10 + 26843545600*(3*u + 2*v)^2*J4^6*J2^3 +
      12288*(4*u + v)^2*J6*J2^12 + 4096*(4*u + v)^2*J4^2*J2^11 -
      3669177139200*(51960*u^2 - 36362*u*v - 343*v^2)*J6^5 -
      16106127360000000*(51960*u^2 - 36362*u*v - 1593*v^2)*J10^3 +
      75*(51960*u^2 - 36362*u*v + 2157*v^2)*J15^2 - 1258291200*(1783560*u^2 -
      1336343*u*v + 49628*v^2)*J6^2*J4^3*J2^3 + 10066329600*(85515*u^2 -
      55264*u*v - 3116*v^2)*J6*J4^5*J2^2 - 169869312000*(105000*u^2 -
      68674*u*v - 5141*v^2)*J6^3*J4^2*J2^2 + 362387865600*(105495*u^2 -
      73999*u*v - 986*v^2)*J6^2*J4^4*J2 + 1223059046400*(103920*u^2 -
      70849*u*v - 2561*v^2)*J6^4*J4*J2 + 6553600*(10352*u^2 - 6088*u*v -
      1965*v^2)*J4*J2^8*J10 - 65536000*(1808*u^2 + 3144*u*v +
      14613*v^2)*J6*J2^7*J10 - 1048576000*(4478*u^2 - 2553*u*v -
      484*v^2)*J4^2*J2^6*J10 + 1677721600*(8285*u^2 + 6868*u*v +
      952*v^2)*J4^3*J2^4*J10 + 5033164800*(158130*u^2 - 77586*u*v -
      47779*v^2)*J6^2*J2^4*J10 + 26843545600*(243885*u^2 - 181672*u*v -
      14308*v^2)*J4^4*J2^2*J10 + 13589544960000*(155880*u^2 - 109086*u*v -
      3529*v^2)*J6^3*J2*J10 - 36238786560000*(310635*u^2 - 212922*u*v -
      6683*v^2)*J6^2*J4^2*J10 + 65536*(152624*u^2 - 38848*u*v -
      12701*v^2)*J6*J4^2*J2^8 + 3932160*(3768*u^2 + 55678*u*v -
      21601*v^2)*J6^2*J4*J2^7 - 20971520*(28073*u^2 - 13824*u*v -
      1834*v^2)*J6*J4^3*J2^6 + 78643200*(412764*u^2 - 400948*u*v +
      63397*v^2)*J6^2*J4^2*J2^5 + 2831155200*(417480*u^2 - 277216*u*v -
      13229*v^2)*J6^3*J4*J2^4 - 167772160000*(2835840*u^2 - 1980548*u*v -
      91647*v^2)*J4*J2^3*J10^2 + 15099494400000*(103920*u^2 - 70724*u*v +
      439*v^2)*J6*J2^2*J10^2 + 80530636800000*(105795*u^2 - 73724*u*v -
      3061*v^2)*J4^2*J2*J10^2 - 3623878656000000*(51960*u^2 - 35862*u*v -
      1343*v^2)*J6*J4*J10^2 - 16384*(4*u + v)*(1172*u - 237*v)*J6*J4*J2^10 -
      983040*(4*u + v)*(92*u - 79*v)*J2^10*J10 - 131072*(23*u + 12*v)*(4*u +
      v)*J4^3*J2^9 - 335544320*(3*u + 2*v)*(23*u + 12*v)*J4^5*J2^5 -
      8493465600*(415680*u^2 - 286396*u*v - 6119*v^2)*J6^4*J2^3 -
      322122547200*(50835*u^2 - 34112*u*v - 1468*v^2)*J6*J4^6 -
      1087163596800*(102795*u^2 - 70474*u*v - 1811*v^2)*J6^3*J4^3 +
      3355443200*(2116880*u^2 - 1480161*u*v - 67329*v^2)*J2^5*J10^2 -
      6012954214400*(21465*u^2 - 15048*u*v - 772*v^2)*J4^5*J10 -
      16384*(7856*u^2 + 109368*u*v - 2049*v^2)*J6^2*J2^9 + 1048576*(769*u^2 +
      772*u*v + 184*v^2)*J4^4*J2^7 - 19660800*(833376*u^2 - 559256*u*v -
      13129*v^2)*J6^3*J2^6)*y*z^2 + 32*((4*u + v)^3*J2^11*J15 -
      4*(244*u + 51*v)*(4*u + v)^2*J2^9*J4*J15 + 8*(4*u + v)*(384*u^2 -
      308*u*v - 14551*v^2)*J2^8*J6*J15 + 128*(4*u + v)*(2918*u^2 + 1229*u*v -
      172*v^2)*J2^7*J4^2*J15 - 640*(4032*u^3 - 768*u^2*v - 93680*u*v^2 +
      20041*v^3)*J15*J2^6*J4*J6 - 128000*(64*u^3 + 88*u^2*v - 36*u*v^2 +
      2443*v^3)*J15*J10*J2^6 - 5120*(13644*u^3 + 8695*u^2*v - 1892*u*v^2 -
      1272*v^3)*J15*J2^5*J4^3 - 115200*v*(60*u^2 + 944*u*v -
      129*v^2)*J2^5*J6^2*J15 + 38400*(5184*u^3 + 948*u^2*v - 66812*u*v^2 +
      32925*v^3)*J15*J2^4*J4^2*J6 + 2560000*(576*u^3 + 720*u^2*v -
      276*u*v^2 + 8191*v^3)*J15*J10*J2^4*J4 + 1638400*(3*u + 2*v)*(324*u^2 -
      19*u*v - 100*v^2)*J2^3*J4^4*J15 + 3456000*v*(240*u^2 + 2864*u*v -
      1875*v^2)*J2^3*J4*J6^2*J15 + 25600000*v^2*( - 2129*v +
      2160*u)*J2^3*J6*J10*J15 - 18432000*(360*u^3 + 207*u^2*v -
      2327*u*v^2 + 1380*v^3)*J15*J2^2*J4^3*J6 - 409600000*(216*u^3 +
      243*u^2*v - 135*u*v^2 + 916*v^3)*J15*J10*J2^2*J4^2 -
      2488320000*v^2*(-3*v + 4*u)*J2^2*J6^3*J15 - 393216000*(-3*v +
      4*u)*(3*u + 2*v)^2*J2*J4^5*J15 - 1658880000*v*(u + 9*v)*(15*u -
      13*v)*J2*J4^2*J6^2*J15 - 73728000000*v^2*(-61*v +
      45*u)*J2*J4*J6*J10*J15 + 36864000000000*v^3*J2*J10^2*J15 +
      8847360000*( - v + u)*( - v + 3*u)*(7*v + 3*u)*J4^4*J6*J15 +
      65536000000*(3*u + 5*v)*( - v + 3*u)^2*J4^3*J10*J15 +
      597196800000*v^2*(-v + u)*J4*J6^3*J15 -
      8847360000000*v^3*J6^2*J10*J15)*z^3
  return conic, cubic
end


function models_from_g2_invariants_char2(g2_invs::Vector{T}, all_twists::Bool = false) where T <: FieldElem
  @req length(g2_invs) == 3 "Input vector has to have length 3."

  K = parent(g2_invs[1])
  p = characteristic(K)
  g1, g2, g3 = g2_invs

  #See Theorem 4 in [CaNaPu2005]
  if g1 != g2*g3
    return g2_models_FF_char2_C2(g2_invs, all_twists)
  elseif g1 == g2*g3 && g1 != 0 && g2 != g3^2
    return g2_models_FF_char2_C2xC2(g2_invs, all_twists)
  elseif g1 == g3^3 && g2 == g3^2 && g3 != 0
    return g2_models_FF_char2_C2xS3(g2_invs, all_twists)
  elseif g1 == 0 && g2 != 0 && g3 == 0
    return g2_models_FF_char2_C2_mixed(g2_invs, all_twists)
  elseif g1 == 0 && g2 == 0 && g3 != 0
    return g2_models_FF_char2_M32(g2_invs, all_twists)
  else
    return g2_models_FF_char2_M160(g2_invs, all_twists)
  end
end

function models_from_igusa_invariants_char3(igusa_invs::Vector{T}, all_twists::Bool = false) where T <: FieldElem
  @req 5 <= length(igusa_invs) <= 6 "Input vector has to have length 5 or 6."

  K = parent(igusa_invs[1])
  p = characteristic(K)

  J2, J4, J6, _, J10 = igusa_invs[1:5]

  g2_invs = g2_from_igusa(igusa_invs)
  g1, g2, g3 = g2_invs

  # y^2 = x^6 - 1
  if g2_invs == [K(50000), K(3750), K(-125) ]
    return g2_models_FF_G48(g2_invs, all_twists)
  end

  # y^2 = x^5 - 1
  if g2_invs == [ K(0), K(0), K(0) ]
    return g2_models_FF_C10(g2_invs, all_twists)
  end

  #y^2 = x^6/t + x^4 + x^2 + 1
  if J4 == 0 && J10 + 2*J6*J2^2 == 0
    return g2_models_FF_char3_D12(igusa_invs, all_twists)
  end

  # y^2 = x^5 + x^3 + t*x
  if 172800*J6^2-23040*J6*J4*J2+592*J6*J2^3-40960*J4^3+3584*J4^2*J2^2-104*J4*J2^4+J2^6 == 0 &&
       128000*J10+5760*J6*J4-192*J6*J2^2-1024*J4^2*J2+64*J4*J2^3-J2^5 == 0
    return g2_models_FF_D8(igusa_invs, all_twists)
  end

  R = J2^6*J6^3 - 2*J2^5*J4^2*J6^2 - 72*J2^5*J4*J6*J10 - 432*J2^5*J10^2 + J2^4*J4^4*J6 +
      8*J2^4*J4^3*J10 - 72*J2^4*J4*J6^3 - 48*J2^4*J6^2*J10 + 136*J2^3*J4^3*J6^2 +
      4816*J2^3*J4^2*J6*J10 + 28800*J2^3*J4*J10^2 + 216*J2^3*J6^4 -
      64*J2^2*J4^5*J6 - 512*J2^2*J4^4*J10 + 1080*J2^2*J4^2*J6^3 -
      12960*J2^2*J4*J6^2*J10 - 96000*J2^2*J6*J10^2 - 2304*J2*J4^4*J6^2 -
      84480*J2*J4^3*J6*J10 - 512000*J2*J4^2*J10^2 - 7776*J2*J4*J6^4 -
      129600*J2*J6^3*J10 + 1024*J4^6*J6 + 8192*J4^5*J10 + 6912*J4^3*J6^3 +
      691200*J4^2*J6^2*J10 + 11520000*J4*J6*J10^2 + 11664*J6^5 + 51200000*J10^3

  if R == 0
    return g2_models_FF_V4(igusa_invs, all_twists)
  end

  return g2_models_FF_C2(igusa_invs, all_twists)
end

function models_from_igusa_invariants_char5(igusa_invs::Vector{T}, all_twists::Bool = false) where T <: FieldElem
  @req 5 <= length(igusa_invs) <= 6 "Input vector has to have length 5 or 6."

  K = parent(igusa_invs[1])
  p = characteristic(K)

  J2, J4, J6, _, J10 = igusa_invs[1:5]

  g2_invs = g2_from_igusa(igusa_invs)
  g1, g2, g3 = g2_invs

  # y^2 = x^6 - 1
  if g2_invs == [K(50000), K(3750), K(-125) ]
    return g2_models_FF_char5_G240(g2_invs, all_twists)
  end

  #y^2 = x^6 + x^3 + t
  if J10*J4*J2^2 + J6^3 + 3*J6*J4^3 + 2*J4^4*J2 == 0 &&
    J10*J2^3 + 3*J6^2*J4 + 4*J4^4 + 2*J4^3*J2^2 == 0 &&
    J6*J2 + 2*J4^2 == 0
    return g2_models_FF_D12(igusa_invs, all_twists)
  end

  # y^2 = x^5 + x^3 + t*x
  if [J10*J4^5 + 4*J6^5 + 2*J6^3*J4^3 + 2*J4^6*J2^3 + 2*J4^4*J2^7 + 4*J4^3*J2^9 + 2*J2^15,
    J10*J4^3*J2 + 2*J6^4 + 3*J6^2*J4^3 + 3*J4^6 + J4^5*J2^2 + 3*J4^4*J2^4 + 2*J4^3*J2^6 + J4^2*J2^8 + 2*J4*J2^10 + 3*J2^12,
    J10*J4*J2^2 + J6^3 + 3*J4^4*J2 + 2*J4^2*J2^5 + 4*J4*J2^7 + 2*J2^9,
    J10*J2^3 + 3*J6^2*J4 + 3*J4^4 + J4^2*J2^4 + 3*J2^8,
    J6*J2 + 2*J4^2 + 3*J4*J2^2 + 3*J2^4
    ] == [K(0), K(0), K(0), K(0), K(0)]
    return g2_models_FF_D8(igusa_invs, all_twists)
  end


  R = J2^6*J6^3 - 2*J2^5*J4^2*J6^2 - 72*J2^5*J4*J6*J10 - 432*J2^5*J10^2 + J2^4*J4^4*J6 +
    8*J2^4*J4^3*J10 - 72*J2^4*J4*J6^3 - 48*J2^4*J6^2*J10 + 136*J2^3*J4^3*J6^2 +
    4816*J2^3*J4^2*J6*J10 + 28800*J2^3*J4*J10^2 + 216*J2^3*J6^4 -
    64*J2^2*J4^5*J6 - 512*J2^2*J4^4*J10 + 1080*J2^2*J4^2*J6^3 -
    12960*J2^2*J4*J6^2*J10 - 96000*J2^2*J6*J10^2 - 2304*J2*J4^4*J6^2 -
    84480*J2*J4^3*J6*J10 - 512000*J2*J4^2*J10^2 - 7776*J2*J4*J6^4 -
    129600*J2*J6^3*J10 + 1024*J4^6*J6 + 8192*J4^5*J10 + 6912*J4^3*J6^3 +
    691200*J4^2*J6^2*J10 + 11520000*J4*J6*J10^2 + 11664*J6^5 + 51200000*J10^3

  if R == 0
    return g2_models_FF_V4(igusa_invs, all_twists)
  end

  return g2_models_FF_C2(igusa_invs, all_twists)
end


function models_from_igusa_invariants_general_char(igusa_invs::Vector{T}, all_twists::Bool = false) where T <: FieldElem
  @req 5 <= length(igusa_invs) <= 6 "Input vector has to have length 5 or 6"

  K = parent(igusa_invs[1])
  p = characteristic(K)

  @req p > 5 || p == 0 "Characteristic has to be either 0 or p > 5."

  J2, J4, J6, _, J10 = igusa_invs[1:5]

  g2_invs = g2_from_igusa(igusa_invs)
  g1, g2, g3 = g2_invs

  # y^2 = x^6-1
  if g2_invs == [ K(6400000)/3, K(440000)/9, K(-32000)/81 ]
    return g2_models_FF_2D12(g2_invs, all_twists)
  end

  if g2_invs == [K(50000), K(3750), K(-125) ]
    return g2_models_FF_G48(g2_invs, all_twists)
  end

  # y^2 = x^5-1, p != 5
  if g2_invs == [ K(0), K(0), K(0) ]
    return g2_models_FF_C10(g2_invs, all_twists)
  end

  #y^2 = x^6 + x^3 + t
  if 750*J10+90*J6*J4-3*J6*J2^2-J4^2*J2 == 0 &&
      2700*J6^2+540*J6*J4*J2-27*J6*J2^3+160*J4^3-9*J4^2*J2^2 == 0
    return g2_models_FF_D12(igusa_invs, all_twists)
  end

  # y^2 = x^5 + x^3 + t*x
  if 172800*J6^2-23040*J6*J4*J2+592*J6*J2^3-40960*J4^3+3584*J4^2*J2^2-104*J4*J2^4+J2^6 == 0 &&
      128000*J10+5760*J6*J4-192*J6*J2^2-1024*J4^2*J2+64*J4*J2^3-J2^5 == 0
    return g2_models_FF_D8(igusa_invs, all_twists)
  end

  # J15^2
  R = J2^6*J6^3 - 2*J2^5*J4^2*J6^2 - 72*J2^5*J4*J6*J10 - 432*J2^5*J10^2 + J2^4*J4^4*J6 +
      8*J2^4*J4^3*J10 - 72*J2^4*J4*J6^3 - 48*J2^4*J6^2*J10 + 136*J2^3*J4^3*J6^2 +
      4816*J2^3*J4^2*J6*J10 + 28800*J2^3*J4*J10^2 + 216*J2^3*J6^4 -
      64*J2^2*J4^5*J6 - 512*J2^2*J4^4*J10 + 1080*J2^2*J4^2*J6^3 -
      12960*J2^2*J4*J6^2*J10 - 96000*J2^2*J6*J10^2 - 2304*J2*J4^4*J6^2 -
      84480*J2*J4^3*J6*J10 - 512000*J2*J4^2*J10^2 - 7776*J2*J4*J6^4 -
      129600*J2*J6^3*J10 + 1024*J4^6*J6 + 8192*J4^5*J10 + 6912*J4^3*J6^3 +
      691200*J4^2*J6^2*J10 + 11520000*J4*J6*J10^2 + 11664*J6^5 + 51200000*J10^3

  if R == 0
    return g2_models_FF_V4(igusa_invs, all_twists)
  end
  return g2_models_FF_C2(igusa_invs, all_twists)
end

