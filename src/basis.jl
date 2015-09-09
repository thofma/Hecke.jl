function lll_basis_profile(rt_c::hecke.roots_ctx, A::NfMaximalOrderIdeal; prec::Int = 100)
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



##chebychev_u ... in flint
function tschebyschew(Qx::Nemo.FmpqPolyRing, n::Int)
  T = [Qx(1), gen(Qx)]
  while length(T) <= n
    push!(T, 2*T[2]*T[end] - T[end-1])
  end
  return T[end]
end

function auto_of_maximal_real(K::NfNumberField, n::Int)
  # image of zeta -> zeta^n
  # assumes K = Q(zeta+1/zeta)
  # T = tschebyschew(n), then
  # cos(nx) = T(cos(x))
  # zeta + 1/zeta = 2 cos(2pi/n)
  T = tschebyschew(parent(K.pol), n)
  i = evaluate(T, gen(K)*1//fmpz(2))*2
  Qx = parent(K.pol)
  return function(a::Nemo.nf_elem)
           return evaluate(Qx(a), i)
         end
end

function orbit(f::Function, a::Nemo.nf_elem)
  b = Set([a])
  nb = 1
  while true
    b = union(Set([f(x) for x in b]) , b)
    if nb == length(b)
      return b
    end
    nb = length(b)
  end
end


function order_of_auto(f::Function, K::NfNumberField)
  a = gen(K)
  b = f(a)
  i = 1
  while b != a
    b = f(b)
    i += 1
  end
  return i
end


