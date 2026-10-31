#function short_elem(c::roots_ctx, A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},
#                v::ZZMatrix = matrix_space(ZZ, 1,1)(); prec::Int = 100)
#  l, t = lll(c, A, v, prec = prec)
#  w = window(t, 1,1, 1, ncols(t))
#  c = w*b
#  q = elem_from_mat_row(K, c, 1, b_den)
#  return q
#end

function random_ideal_with_norm_up_to(a::Hecke.NfFactorBase, B::Integer)
  B = ZZRingElem(B)
  O = order(a.ideals[1])
  K = Hecke.nf(O)
  I = Hecke.ideal(O, K(1))
  while B >= norm(a.ideals[end])
    J = a.ideals[rand(findall(x -> (norm(x) <= B), a.ideals))]
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


