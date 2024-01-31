function lll_basis_profile(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; prec::Int = 100)
  c = Hecke.minkowski_matrix(Hecke.nf(order(A)), prec)
  l = lll(basis_matrix(A))
  b = FakeFmpqMat(l)*basis_matrix(order(A))
  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  Hecke.mult!(d, b.num, c)

  old = get_bigfloat_precision()
  set_bigfloat_precision(prec)

  g = Hecke.round_scale(d, prec)
  set_bigfloat_precision(old)
  g = g*g'
  Hecke.shift!(g, -prec)
  g += nrows(g)*one(parent(g))

  l = lll_gram(g)

  lp = [ div(l[i,i], ZZRingElem(2)^prec) for i=1:nrows(l)]
  return lp
end

#function short_elem(c::roots_ctx, A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},
#                v::ZZMatrix = matrix_space(FlintZZ, 1,1)(); prec::Int = 100)
#  l, t = lll(c, A, v, prec = prec)
#  w = window(t, 1,1, 1, ncols(t))
#  c = w*b
#  q = elem_from_mat_row(K, c, 1, b_den)
#  return q
#end

function bkz_basis(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, bs::Int;
                      v::ZZMatrix = zero_matrix(FlintZZ, 1, 1),
                      prec::Int = 100)


  K = nf(order(A))

  c = minkowski_matrix(K, prec)

  l, t1 = lll_with_transform(basis_matrix(A))
  temp = FakeFmpqMat(l)*basis_matrix(order(A))
  b = temp.num
  b_den = temp.den

  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  mult!(d, b, c)

  #ignore v

  g = round_scale(d, prec)

  #println("calling bkz")
  g, tt = bkz_trans(g, bs)  ## check: bkz_trans seems to s.t. kill the input

  c = tt*b
  q = AbsSimpleNumFieldElem[elem_from_mat_row(K, c, i, b_den) for i=1:degree(K)]

  return q
end

function fplll_basis(rt_c::Hecke.roots_ctx, A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, bs::Int;
                      v::ZZMatrix = zero_matrix(FlintZZ, 1,1),
                      prec::Int = 100)

  K = nf(order(A))

  c = minkowski_matrix(rt_c, K, prec)

  @time l, t1 = lll_with_transform(basis_matrix(A))
  @time temp = FakeFmpqMat(l)*basis_matrix(order(A))
  b = temp.num
  b_den = temp.den

  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  @time mult!(d, b, c)

  #ignore v

  @time g = round_scale(d, prec)

  println("calling lll")
  @time g, tt = FPlll.lll_trans(g)  ## check: bkz_trans seems to s.t. kill the input

  c = tt*b
  q = AbsSimpleNumFieldElem[elem_from_mat_row(K, c, i, b_den) for i=1:degree(K)]

  return q
end



function random_ideal_with_norm_up_to(a::Hecke.NfFactorBase, B::Integer)
  B = ZZRingElem(B)
  O = order(a.ideals[1])
  K = Hecke.nf(O)
  I = Hecke.ideal(O, K(1))
  while B >= norm(a.ideals[end])
    J = a.ideals[rand(find(x -> (norm(x) <= B), a.ideals))]
    B = div(B, norm(J))
    I = I*J
  end
  return I
end



##chebychev_u ... in flint
function tschebyschew(Qx::Nemo.QQPolyRing, n::Int)
  T = [Qx(1), gen(Qx)]
  while length(T) <= n
    push!(T, 2*T[2]*T[end] - T[end-1])
  end
  return T[end]
end


function auto_of_maximal_real(K::AbsSimpleNumField, n::Int)
  # image of zeta -> zeta^n
  # assumes K = Q(zeta+1/zeta)
  # T = tschebyschew(n), then
  # cos(nx) = T(cos(x))
  # zeta + 1/zeta = 2 cos(2pi/n)
  T = tschebyschew(parent(K.pol), n)
  i = evaluate(T, gen(K)*1//ZZRingElem(2))*2
  return hom(K, K, i, check = false)
end

function auto_simplify(A::Map, K::AbsSimpleNumField)
  Qx = parent(K.pol)
  b = A(gen(K))
  return hom(K, K, b, check = false)
end

function auto_power(A::Map, n::Int)
  if n==1
    return A
  end;
  B = x->A(A(x));
  C = auto_power(B, div(n, 2))
  if n%2==0
    return C
  else
    return x-> A(C(x))
  end
end

function orbit(f::Map, a::Nemo.AbsSimpleNumFieldElem)
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


function order_of_auto(f::Map, K::AbsSimpleNumField)
  a = gen(K)
  b = f(a)
  i = 1
  while b != a
    b = f(b)
    i += 1
  end
  return i
end


