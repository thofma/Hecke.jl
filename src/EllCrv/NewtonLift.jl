import Hecke
import Hecke.AbstractAlgebra

_valuation(x) = iszero(x) ? QQ(precision(parent(x))) : valuation(x)

add_verbosity_scope(:NewtonIteration)

set_verbosity_level(:NewtonIteration, 2)


r"""
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

r"""
    newton_lift(E::EllipticCurve, P::EllipticCurvePoint, reduction_map; max_iterations=16) -> EllipticCurvePoint
"""
function newton_lift(E::EllipticCurve, P::EllipticCurvePoint, reduction_map; max_iterations::Int=16)
  # O_F -> O_F/m =: k
  # K the completion of F at m
  sing = _singular_points_weierstrass_model(E)

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
  prec0 = precision(K)
  #setprecision!(F_to_K, prec)
  #@show prec

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

function _newton_lift(P::EllipticCurvePoint, E::EllipticCurve, F_to_K, Ft_to_OKt, Ftok, max_iterations, sing, prime, break_condition=_can_reconstruct_with_reconstruction)
  ainvs = a_invars(E)
  @assert P[3] == 1
  xn = P[1]
  yn = P[2]
  K = codomain(F_to_K)
  dn = sqrt(denominator(xn))
  xn = numerator(xn)
  @assert parent(dn) === parent(xn)
  yn = numerator(yn)
  kt = parent(xn)

  # find the singular points
  # and the multiplicity that P passes through them
  extra_points = Tuple{Vector{elem_type(F)},Int,Int}[]
  k = codomain(Ftok)
  for S in sing
    (x0,y0,t0) = Ftok.(S)
    if evaluate(P[1], t0)==x0 && evaluate(P[2], t0)==y0
      lx = valuation(P[1] - x0, gen(kt) - t0)
      ly = valuation(P[2] - y0, gen(kt)-t0)
      push!(extra_points, (S,lx,ly))
    end
  end

  # prepare the point for lifting
  OKt = codomain(Ft_to_OKt)
  OK = base_ring(OKt)
  F_to_OK = map_from_func(x->OK(F_to_K(x)), F, OK)
  point = [map_coefficients(x->F_to_OK(preimage(Ftok,x)), i; parent=OKt) for i in [xn,yn,dn]]

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
  extra_pointsOK = [(F_to_OK.(i[1]),i[2],i[3]) for i in extra_points]

  prec = 1
  minprec = 1
  for s in 1:max_iterations
    # set the precision of the result

    point = _newton_step(Rt, ainvsOKt, point, extra_pointsOK, prec)
    #@show precision.(coefficients(point[1]))

    prec = 2*prec
    s < min(max_iterations,6) && continue
    fl, result = break_condition(E, point, F_to_K, prec)
    if fl
      return result
    end
  end
  error("nothing found")
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
  # make the section pass through the extra points again
  # without modifying it modulo prime^prec
  # we do this in order to perform the newton
  # iteration in a linear subspace without having
  # to write it down explicitly
  #point = _to_hyper(point, Rt, extra_points, prec)
  fn = _compute_fn(point, ainvsOKt)

  @assert minimum(_valuation(i) for i in coefficients(fn);init=inf)>=prec
  @assert minimum(precision(i) for i in coefficients(fn); init=inf)>=prec
  @assert all(minimum(precision(i) for i in coefficients(a); init=inf)>=2*prec for a in ainvsOKt)
  @assert all(minimum(precision(i) for i in coefficients(a); init=inf)>=2*prec for a in point)
  @vprint :NewtonIteration 3 "input quality: $(prec)\n"
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

  xt = sum(gen(R,i+1)*t^i for i in 0:xd; init = zero(Rt))
  yt = sum(gen(R, i+xd+2)*t^i for i in 0:yd; init = zero(Rt))
  dt = sum(gen(R, i+xd+1+yd+2)*t^i for i in 0:dd-1; init = zero(Rt))#+t^dd

  DF = (2*ynt + a1*dnt*xnt + a3*dnt^3)*yt +(a1*dnt*ynt- (3*xnt^2 + a2*dnt^2*2*xnt + a4*dnt^4))*xt + (a1*xnt*ynt + a3*3*dnt^2*ynt - (a2*2*dnt*xnt^2 + a4*4*dnt^3*xnt + a6*6*dnt^5))*dt
  eqn = fn(t) + DF

  equations = []
  push!(equations, eqn)

  EQ0 = elem_type(R)[]
  EQc0 = elem_type(OK)[]
  for ((x0,y0,t0),lx, ly) in extra_points
    eqn0 = mod(xn(t0) + xt - (dn(t0)^2+2*dt*dn(t0))*x0, (t - t0))
    push!(equations, eqn0)
    eqn0 = mod(yn(t0) + yt -(dn(t0)^3+3*dt*dn(t0)^2)*y0, (t - t0))
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
  v = _solve_mod(M, EQc, 2*prec)

  #@show  minimum(_valuation.(M*v - EQc))
  @assert minimum(_valuation.(M*v - EQc)) >= 2*prec
  @assert minimum(_valuation.(v)) >= prec
  t = gen(OKt)

  xne = sum(v[i+1]*t^i for i in 0:xd; init=zero(OKt))
  yne = sum(v[i+xd+2]*t^i for i in 0:yd; init=zero(OKt))
  dne = sum(v[i+xd+2+yd+1]*t^i for i in 0:dd-1; init=zero(OKt))

  xn1 = xn + xne
  yn1 = yn + yne
  dn1 = dn + dne
  point = [xn1,yn1,dn1]
  fn = _compute_fn(point, ainvsOKt)
  prec1 =  Int(minimum(_valuation.(coefficients(fn)); init=precision(OK)))
  prec2 = minimum([Int(minimum(precision.(coefficients(p)); init=precision(OK))) for p in point])
  prec3 = minimum([Int(minimum(precision.(coefficients(p)); init=precision(OK))) for p in ainvsOKt])
  prec0 = minimum([prec1,prec2,prec3])
  @vprint :NewtonIteration 2 "output quality: $(prec0)\n"
  @assert prec0 >= 2*prec
  return xn1, yn1, dn1
end


function _to_hyper(point, Rt, extra_points, prec)
  xn, yn, dn = point
  R = base_ring(Rt)
  t = gen(Rt)
  K = coefficient_ring(R)
  Kt = parent(xn)
  xd = degree(xn)
  yd = degree(yn)
  dd = degree(dn)
  if length(extra_points)==0
    return xn,yn,dn
  end
  @assert string(t) == "t"
  EQ0 = elem_type(R)[]
  EQc0 = elem_type(K)[]
  xt = sum(gen(R, i+1)*t^i for i in 0:xd; init=Rt(0))
  yt = sum(gen(R, i+xd+2)*t^i for i in 0:yd; init=Rt(0))
  dt = sum(gen(R, i+xd+2+yd+1)*t^i for i in 0:dd-1; init=Rt(0))#+t^dd
  for ((x0,y0,t0),lx, ly) in extra_points
    eqn0 = mod(xn(t0) + xt - (dn(t0)^2+2*dt*dn(t0))*x0, (t - t0)^lx)
    append!(EQ0, [coeff(eqn0, i) for i in 0:degree(eqn0) if coeff(eqn0, i)!=0])
    append!(EQc0, [constant_coefficient(coeff(eqn0, i)) for i in 0:degree(eqn0) if coeff(eqn0, i)!=0])

    eqn0 = mod(yn(t0) + yt -(dn(t0)^3+3*dt*dn(t0)^2)*y0, (t - t0)^ly)
    append!(EQ0, [coeff(eqn0, i) for i in 0:degree(eqn0) if coeff(eqn0, i)!=0])
    append!(EQc0, elem_type(K)[constant_coefficient(coeff(eqn0, i)) for i in 0:degree(eqn0) if coeff(eqn0, i)!=0])

  end
  # each equation is a row
  n = ngens(R) - 3
  M = zero_matrix(K, length(EQ0), n)
  for i in 1:length(EQ0)
    for j in 1:n
      M[i,j] = coeff(EQ0[i],gen(R,j))
    end
  end
  EQc0 = -matrix(K, length(EQc0), 1, EQc0)
  v = _solve_mod(M, EQc0, 2*prec)

  @assert minimum(_valuation.(M*v-EQc0))>=2*prec
  @assert minimum(_valuation.(v))>=prec
  t = gen(Kt)
  xn1 = xn + sum(v[i+1, 1]*t^i for i in 0:xd; init=zero(Kt))
  yn1 = yn + sum(v[i+xd+2, 1]*t^i for i in 0:yd; init=zero(Kt))
  dn1 = dn + sum(v[i+xd+2+yd+1, 1]*t^i for i in 0:dd-1; init=zero(Kt))
  return xn1,yn1,dn1
end

function Hecke.setprecision!(p::AbstractAlgebra.Generic.Poly{<:Hecke.LocalFieldValuationRingElem}, n::Int)
  c = coefficient_ring(p)
  @assert parent(coeff(p,0)) === c
  pp = map_coefficients(x->setprecision!(x, n), p; parent=parent(p))
  @assert parent(coeff(pp,0)) === c
  return pp
end

#=
function _setprecision!(M::MatrixElem, prec)
  for x in eachindex(M)
    M[x] = setprecision!(M[x], prec)
  end
  return M
end
=#


"""
Solve A x = b mod p^n
for x
"""
function _solve_mod(A::T, b::T, n::Int) where {T<: MatElem{<:Hecke.LocalFieldValuationRingElem}}
  OK = base_ring(A)
  @assert base_ring(b) == OK
  pi = uniformizer(OK)
  R, OK_to_R = residue_ring(OK, pi^n)

  @show minimum(precision.(A))
  @assert minimum(precision.(A))>=n
  @assert minimum(precision.(b))>=n

  AR = OK_to_R.(A)
  bR = OK_to_R.(b)

  global A1 = AR
  global b1 = bR
  xR = solve(AR,bR; side=:right)
  xOK = map_entries(x-> preimage(OK_to_R,x), xR)

  precb = minimum(precision.(b))
  bb = A*xOK
  @assert minimum(precision.(xOK)) >= n  && minimum(precision.(bb)) >= n && bb==b
  return xOK #_setprecision!(xK, prec)
end

