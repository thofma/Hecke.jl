#import Hecke.AbstractAlgebra
export newton_lift

_valuation(x::RingElem) = iszero(x) ? QQ(precision(parent(x))) : valuation(x)


raw"""
    _singular_points_weierstrass_model(E::EllipticCurve{<:FracField{<:AbstractAlgebra.Generic.Poly}})

Return the singular points of the weierstrass model W/k of E/k(t).

It is assumed that they are all defined over k.
"""
function _singular_points_weierstrass_model(E::EllipticCurve{<:AbstractAlgebra.Generic.FracFieldElem{<:AbstractAlgebra.Generic.Poly}})
  p = [i[1] for i in factor(numerator(discriminant(E))) if i[2]>1]
  Ft = base_ring(base_field(E))
  F = coefficient_ring(Ft)
  P,x = polynomial_ring(F,:x)
  a1, a2, a3, a4, a6 = a_invariants(E)

  #f = y^2 + a1*x*y + a3*y - (x^3 + a2*x^2 + a4*x + a6)
  @req iszero(a1) "not implemented for general weierstrass models"
  @req iszero(a3) "not implemented for general weierstrass models"
  sing = Vector{elem_type(F)}[]
  for cc in p
    @req degree(cc)==1 "all reducible singular fibers need to be defined over the base field"
    t0 = -constant_coefficient(cc)
    a1c, a2c, a3c, a4c, a6c = [evaluate(a,t0) for a in a_invariants(E)]
    f = (x^3 + a2c*x^2 + a4c*x + a6c)
    pt = [i[1] for i in factor(f) if i[2]>1]
    @assert length(pt)==1

    pt = pt[1]
    x0 = -constant_coefficient(pt)
    y0 = F(0)
    push!(sing, [x0,y0,t0])
  end
  return sing
end

@doc raw"""
    newton_lift(E::EllipticCurve, P::EllipticCurvePoint, reduction_map; max_iterations=7) -> Bool, EllipticCurvePoint

Return a point `Q` of `E` which reduces by `reduction_map` to `P` and whether it exists.

Let ``F`` be a number field and ``E`` an elliptic curve over ``F(t)`` which is integral over ``F[t]``.
Let ``O_F`` be the maximal order of ``F`` and ``p`` be a prime ideal of ``O_F`` with residue field ``k``.
Suppose that ``E`` is integral over ``(O_F)_p`` and that it has good reduction at ``p``.

The algorithm lifts `P` by a multivariate Newton iteration to a point in the completion of ``F`` at the prime ``p``
(up to some finite precision). The corresponding point of small height in `F` is computed and the result verified.

Throws an error if `max_iterations` is reached without recognizing the point in `F`.
Use `set_verbosity_level(:NewtonLift, 2)` for output during the computation.

Input:
- `E` -- the elliptic curve ``E/F(t)``
- `p` -- a point of ``E/k(t)``
- `reduction map` -- the canonical homomorphism $O_F \rightarrow k$
- max_iterations -- the maximal number of Newton iteration steps, setting to a high value slows down computations a lot.
"""
function newton_lift(E::EllipticCurve{<:Generic.FracFieldElem{<:PolyRingElem}}, P::EllipticCurvePoint{<:Generic.FracFieldElem{<:PolyRingElem}}, reduction_map::Map; max_iterations::Int=7)
  # O_F -> O_F/m =: k
  # K the completion of F at m
  sing = _singular_points_weierstrass_model(E)
  @req codomain(reduction_map)===base_ring(base_ring(base_field(parent(P)))) "codomain of the reduction map incompatible with the point to be lifted"
  @req number_field(domain(reduction_map))===base_ring(base_ring(base_field(E))) "codomain of the reduction map incompatible with the point to be lifted"
  @req max_iterations <= 62 " the desired precision needs to fit into an Int64"
  prime = reduction_map.P
  F = number_field(domain(reduction_map))
  F_to_k = extend(reduction_map, F)
  K, F_to_K = completion(F, prime, 2^max_iterations)
  OK = valuation_ring(K)
  Ft = base_ring(base_field(E))
  OKt,_ = polynomial_ring(OK,'t'; cached=false)
  F_to_OK = map_from_func(x-> OK(F_to_K(x)), F, OK)
  Ft_to_OKt = map_from_func(x->map_coefficients(F_to_OK, x; parent=OKt), Ft, OKt)

  return  _newton_lift(P, E, F_to_K, Ft_to_OKt, F_to_k, max_iterations, sing, prime)
end


function _can_reconstruct_with_reconstruction(E::EllipticCurve, padic_point, F_to_K, prec)
  @vprint :NewtonIteration 2 "trying rational reconstruction\n"
  K = codomain(F_to_K)
  # prec0 = precision(K)
  #setprecision!(F_to_K, prec) # leads to difficult bugs

  xnF, ynF, dnF = [map_coefficients(x->preimage(F_to_K,K(x); small_lift=true), a) for a in padic_point]

  #setprecision!(F_to_K, prec0)

  xF = xnF // dnF^2
  yF = ynF // dnF^3

  if is_on_curve(E, [xF, yF])
    @vprint :NewtonIteration 3 "found"
    return true, E([xF,yF])
  else
    return false, infinity(E)
  end
end

function _newton_lift(P::EllipticCurvePoint, E::EllipticCurve, F_to_K, Ft_to_OKt, F_to_k, max_iterations, sing, prime, break_condition=_can_reconstruct_with_reconstruction)
  ainvs = a_invariants(E)
  @assert P[3] == 1
  xn = P[1]
  yn = P[2]
  K = codomain(F_to_K)
  dn = sqrt(denominator(xn))
  xn = numerator(xn)
  @assert parent(dn) === parent(xn)
  yn = numerator(yn)
  kt = parent(xn)

  # find the singular points of the Weierstrass model that P passes through
  # this must be preserved by the lift
  k = codomain(F_to_k)
  F = domain(F_to_k)
  extra_points = Vector{elem_type(F)}[]
  for S in sing
    (x0,y0,t0) = F_to_k.(S)
    if evaluate(P[1], t0)==x0 && evaluate(P[2], t0)==y0
      push!(extra_points, S)
    end
  end

  # prepare the point for lifting
  OKt = codomain(Ft_to_OKt)
  OK = base_ring(OKt)
  F_to_OK = map_from_func(x->OK(F_to_K(x)), F, OK)
  point = [map_coefficients(x->F_to_OK(preimage(F_to_k,x)), i; parent=OKt) for i in [xn,yn,dn]]

  # setup the ring for bookkeeping
  @assert all(isone(denominator(a)) for a in ainvs) "model must be integral"
  names = String[]
  append!(names, ["x$(i)" for i in 0:degree(xn)])
  append!(names, ["y$(i)" for i in 0:degree(yn)])
  append!(names, ["d$(i)" for i in 0:(degree(dn)-1)])
  append!(names, ["x","y","d"])
  R,_ = polynomial_ring(OK,names; cached=false)
  Rt,t = polynomial_ring(R,"t"; cached=false)

  ainvsOKt = [Ft_to_OKt(numerator(a)) for a in ainvs]
  extra_pointsOK = [F_to_OK.(i) for i in extra_points]

  prec = 1
  minprec = 1
  for s in 1:max_iterations

    can_lift, point = _newton_step(Rt, ainvsOKt, point, extra_pointsOK, prec)
    can_lift || return false, infinity(E)
    prec = 2*prec
    s < min(max_iterations,6) && continue
    fl, result = break_condition(E, point, F_to_K, prec)
    if fl
      return true, result
    end
  end
  error("could not reconstruct point, you can increase the number of newton iterations and try again")
end

function _compute_fn(point, ainvs)
  P = parent(point[1])
  @assert all(P===parent(a) for a in ainvs)
  @assert all(P===parent(a) for a in point)
  # x = xn//dn^2
  # y = tn//dn^3
  xn,yn,dn = point
  a1,a2,a3,a4,a6 = ainvs
  return yn^2 + a1*dn*xn*yn + a3*dn^3*yn - (xn^3 + a2*dn^2*xn^2 + a4*dn^4*xn + a6*dn^6)
end

function _newton_step(Rt, ainvsOKt, point, extra_points, prec)
  @assert parent(point[1]) === parent(ainvsOKt[1])
  # increase precision to the desired output precision
  point = [setprecision!(i, 2*prec) for i in point]

  fn = _compute_fn(point, ainvsOKt)

  # check that the input has the desired precision
  @assert minimum(_valuation(i) for i in coefficients(fn);init=inf)>=prec
  @assert minimum(precision(i) for i in coefficients(fn); init=inf)>=prec
  @assert all(minimum(precision(i) for i in coefficients(a); init=inf)>=2*prec for a in ainvsOKt)
  @vprint :NewtonIteration 3 "input quality: $(prec)\n"
  @assert all(minimum(precision(i) for i in coefficients(a); init=inf)>=2*prec for a in point)

  R = base_ring(Rt)
  OK = base_ring(R)
  xn, yn, dn = point
  OKt = parent(xn)
  ainvsRt = [a(gen(Rt)) for a in ainvsOKt]
  a1,a2,a3,a4,a6 = ainvsRt
  t = gen(Rt)
  xd = degree(xn)
  yd = degree(yn)
  dd = degree(dn)

  xnt = xn(t)
  ynt = yn(t)
  dnt = dn(t)

  gensR = gens(R)
  #xt = sum(gen(R,i+1)*t^i for i in 0:xd; init = zero(Rt))
  xt = Rt(gensR[1:xd+1])
  #yt = sum(gen(R, i+xd+2)*t^i for i in 0:yd; init = zero(Rt))
  yt = Rt(gensR[xd+2:xd+yd+2])
  #dt = sum(gen(R, i+xd+1+yd+2)*t^i for i in 0:dd-1; init = zero(Rt))
  dt = Rt(gensR[xd+yd+3:xd+yd+dd+2])

  DF = (2*ynt + a1*dnt*xnt + a3*dnt^3)*yt +(a1*dnt*ynt- (3*xnt^2 + a2*dnt^2*2*xnt + a4*dnt^4))*xt + (a1*xnt*ynt + a3*3*dnt^2*ynt - (a2*2*dnt*xnt^2 + a4*4*dnt^3*xnt + a6*6*dnt^5))*dt
  eqn = fn(t) + DF

  equations = []
  push!(equations, eqn)

  EQ0 = elem_type(R)[]
  EQc0 = elem_type(OK)[]
  for (x0,y0,t0) in extra_points
    eqn0 = xn(t0) + xt(t0) - (dn(t0)^2+2*dt*dn(t0))*x0
    push!(equations, eqn0)
    eqn0 = yn(t0) + yt(t0) -(dn(t0)^3+3*dt*dn(t0)^2)*y0
    push!(equations, eqn0)
  end

  EQ = reduce(append!,[elem_type(R)[coeff(eqn, i) for i in 0:degree(eqn) if coeff(eqn, i)!=0] for eqn in equations])
  EQc = reduce(append!, [elem_type(OK)[constant_coefficient(coeff(eqn, i)) for i in 0:degree(eqn) if coeff(eqn, i)!=0] for eqn in equations])
  n = ngens(R) - 3

  # each equation is a row
  M = zero_matrix(OK, length(EQ), n)
  for i in 1:length(EQ)
    for j in 1:n
      M[i,j] = coeff(EQ[i],gen(R,j))
    end
  end


  EQc = -matrix(OK, length(EQc), 1, EQc)
  fl, v = can_solve_with_solution_mod(M, EQc, 2*prec; side=:right)

  fl || return false, point

  #@show  minimum(_valuation.(M*v - EQc))
  @assert minimum(_valuation.(M*v - EQc)) >= 2*prec
  @assert minimum(_valuation.(v)) >= prec
  t = gen(OKt)

  # xne = sum(v[i+1]*t^i for i in 0:xd; init=zero(OKt))
  xne = OKt(v[1:xd+1, 1])
  #yne = sum(v[i+xd+2]*t^i for i in 0:yd; init=zero(OKt))
  yne = OKt(v[xd+2:xd+2+yd,1])
  #dne = sum(v[i+xd+2+yd+1]*t^i for i in 0:dd-1; init=zero(OKt))
  dne = OKt(v[xd+yd+3:xd+yd+dd+2,1])

  xn1 = xn + xne
  yn1 = yn + yne
  dn1 = dn + dne
  point = [xn1,yn1,dn1]
  fn = _compute_fn(point, ainvsOKt)
  prec0 =  minimum(_valuation.(coefficients(fn)); init=precision(OK))
  prec1 =  minimum(minimum(precision.(coefficients(i)); init=precision(OK)) for i in point)
  prec2 =  minimum(minimum(precision.(coefficients(i)); init=precision(OK)) for i in ainvsOKt)
  prec_out = minimum([prec0,prec1,prec2])
  @vprint :NewtonIteration 2 "output quality: $(prec_out)\n"
  @assert prec_out >= 2*prec
  return true, (xn1, yn1, dn1)
end


"""
  _solve_mod(A::T, b::T, n::Int, side) where {T<: MatElem{<:Hecke.LocalFieldValuationRingElem}} -> T

Let `p` be the uniformizer of the coefficient ring of `A`.
If side = :right
solve A x = b mod p^n for x
If side = :left
Solve x A  = b mod p^n for x
"""
function can_solve_with_solution_mod(A::T, b::T, n::Int; side) where {T<: MatElem{<:Hecke.LocalFieldValuationRingElem}}
  OK = base_ring(A)
  @assert base_ring(b) == OK
  pi = uniformizer(OK)
  R, OK_to_R = residue_ring(OK, pi^n)

  #@show minimum(precision.(A))
  @assert minimum(precision.(A))>=n
  @assert minimum(precision.(b))>=n

  AR = OK_to_R.(A)
  bR = OK_to_R.(b)

  fl, xR = can_solve_with_solution(AR,bR; side=side)
  xOK = map_entries(x-> preimage(OK_to_R,x), xR)
  fl || return fl, xOK
  # double check the computation
  bb = A*xOK
  @assert minimum(precision.(xOK)) >= n  && minimum(precision.(bb)) >= n && bb==b
  return fl, xOK
end

