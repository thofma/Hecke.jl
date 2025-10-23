
function is_norm_fac_elem(K::RelSimpleNumField{AbsSimpleNumFieldElem}, a::AbsSimpleNumFieldElem)
  Ka, mKa, mkK = collapse_top_layer(K)
  Kas, KasToKa = simplify(Ka)
  Ka = Kas
  #mKa = KasToKa * mKa
  mkK = mkK * inv(KasToKa)

  ZKa = lll(maximal_order(Ka))
  C, mC = class_group(ZKa, use_aut = true)

  S = collect(keys(factor(mkK(a)*ZKa)))

  c = get_attribute(ZKa, :ClassGrpCtx)
  FB = c.FB.ideals::Vector{ideal_type(order_type(Ka))}
  i = length(FB)
  q, mq = quo(C, elem_type(C)[preimage(mC, I) for I = S], false)
  while length(q) > 1
    while FB[i] in S || iszero(mq(preimage(mC, FB[i])))
      i -= 1
    end
    push!(S, FB[i])
    q, mmq = quo(q, [mq(preimage(mC, FB[i]))], false)
    mq = mq*mmq
  end

  s = Set(ideal_type(order_type(AbsSimpleNumField))[minimum(mkK, I) for I = S])
  #make S relative Galois closed:
  PS = IdealSet(ZKa)
  S = reduce(vcat, Vector{ideal_type(ZKa)}[collect(keys(factor(PS(mkK, p)))) for p = s], init = Vector{ideal_type(ZKa)}())

  local U::FinGenAbGroup

  if length(S) == 0
    U, mU = unit_group_fac_elem(ZKa)
  else
    U, mU = sunit_group_fac_elem(collect(S))
  end

  class_group(parent(a))

  local u::FinGenAbGroup

  if length(s) == 0
    u, mu = unit_group_fac_elem(maximal_order(parent(a)))
  else
    u, mu = sunit_group_fac_elem(collect(s))
  end
  No = hom(U, u, elem_type(u)[preimage(mu, norm(mkK, mU(g))) for g = gens(U)])
  aa = preimage(mu, FacElem(a))::FinGenAbGroupElem
  fl, so = has_preimage_with_preimage(No, aa)
  fl || return fl, FacElem(one(K))

  #try to get a smaller solution, we're allowed to modify by the
  #kernel of No
  #Goal: solution should have small valuation everywhere
  #the weights are somewhat random
  # - val*norm(P) so that size of P does matter a bit
  # - scale by 1000 so that small units do not vanish to zero
  k, mk = kernel(No)
  k, _mk = snf(k)
  mk = _mk*mk
  gk = [mU(mk(g)) for g = gens(k)]
  pushfirst!(gk, mU(so))
  if length(S) > 0
    v = matrix(ZZ, length(gk), length(S), [valuation(g, P)*norm(P) for g = gk for P = S])
  else
    v = zero_matrix(ZZ, ngens(k), 0)
  end
  pr = 256
  local vv
  while true
    R = ArbField(pr)
    try 
      vv = matrix([[round(ZZRingElem, x*1000) for x = conjugates_arb_log(g, R)] for g = gk])
      break
    catch e
      if isa(e, InexactError)
        pr *= 2
        if pr >10000
          error("$pr too large")
        end
      else
        rethrow(e)
      end
    end
  end
  v = hcat(1000*v, vv)

  l, t = lll_with_transform(view(v, 2:nrows(v), :))
  _, tt = Hecke.MultDep.size_reduce_with_transform(l, view(v, 1:1, :))
  so += mk(k(tt*t))

  return true, FacElem(K, Dict{elem_type(K), ZZRingElem}([image(KasToKa * mKa, k) => v for (k,v) = (mU(so)::FacElem{elem_type(Ka), typeof(Ka)})]))
end

function is_norm(K::RelSimpleNumField{AbsSimpleNumFieldElem}, a::AbsSimpleNumFieldElem)
  fl, s = is_norm_fac_elem(K, a)
  return fl, evaluate(s)
end

function norm_equation(K::RelSimpleNumField{AbsSimpleNumFieldElem}, a::AbsSimpleNumFieldElem)
  fl, s = is_norm(K, a)
  fl || error("no solution")
  return s
end
