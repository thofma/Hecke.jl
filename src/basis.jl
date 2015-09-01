using hecke

function lll_basis_profile(rt_c::roots_ctx, A::NfMaximalOrderIdeal; prec::Int = 100)
  c = hecke.minkowski_mat(rt_c, hecke.nf(order(A)), prec)
  l = lll(basis_mat(A))
  b = FakeFmpqMat(l)*basis_mat(order(A))
  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  hecke.mult!(d, b.num, c)

  old = get_bigfloat_precision()
  set_bigfloat_precision(prec)

  g = hecke.round_scale(d, prec)
  set_bigfloat_precision(old)
  g = g*g'
  hecke.shift!(g, -prec)
  g += rows(g)*one(parent(g))

  l = lll_gram(g)

  lp = [ div(l[i,i], fmpz(2)^prec) for i=1:rows(l)]
  return lp
end

function random_ideal_with_norm_up_to(a::hecke.NfFactorBase, B::Integer)
  B = fmpz(B)
  O = order(a.ideals[1])
  K = hecke.nf(O)
  I = hecke.ideal(O, K(1))
  while B >= norm(a.ideals[end])
    J = a.ideals[rand(find(x -> (norm(x) <= B), a.ideals))]
    B = div(B, norm(J))
    I = I*J
  end
  return I
end


