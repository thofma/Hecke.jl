#TODO: verbose printing

function norm_1_generators(A::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  @assert all(is_prime, A)
  @assert all(x->x.gen_one == A[1].gen_one, A)

  f = matrix(FlintZZ, 1, length(A), [degree(x) for x = A])
  k = kernel(f, side = :right)

  id = [FacElem(A, [k[i,j] for i=1:length(A)]) for j=1:ncols(k)]
  return id
end

@doc raw"""
    norm_equation(K::AnticNumerField, a) -> AbsSimpleNumFieldElem

For $a$ an integer or rational, try to find $T \in K$ s.th.
$N(T) = a$. Raises an error if unsuccessful.
"""
function norm_equation(K::AbsSimpleNumField, a)
  fl, s = is_norm(K, a)
  if fl
    return evaluate(s)
  end
  error("no solution")
end

@doc raw"""
    is_norm(K::AbsSimpleNumField, a) -> Bool, AbsSimpleNumFieldElem

For $a$ an integer or rational, try to find $T \in K$ s.th. $N(T) = a$
holds. If successful, return true and $T$, otherwise false and some element.
The element will be returned in factored form.
"""
function is_norm(K::AbsSimpleNumField, a::Integer)
  return is_norm(K, ZZRingElem(a))
end
function is_norm(K::AbsSimpleNumField, a::QQFieldElem)
  fl, s = is_norm(K, numerator(a)*denominator(a)^(degree(K)-1))
  return fl, s * FacElem(Dict(K(denominator(a)) => ZZRingElem(-1)))
end
function is_norm(K::AbsSimpleNumField, a::Rational)
  return is_norm(K, QQFieldElem(a))
end

@doc raw"""
    is_norm(K::AbsSimpleNumField, a::ZZRingElem; extra::Vector{ZZRingElem}) -> Bool, AbsSimpleNumFieldElem

For a ZZRingElem $a$, try to find $T \in K$ s.th. $N(T) = a$
holds. If successful, return true and $T$, otherwise false and some element.
In \testtt{extra} one can pass in additional prime numbers that
are allowed to occur in the solution. This will then be supplemented.
The element will be returned in factored form.
"""
function is_norm(K::AbsSimpleNumField, a::ZZRingElem; extra::Vector{ZZRingElem}=ZZRingElem[])
  L = lll(maximal_order(K))
  C, mC = narrow_class_group(L)
#  println("narrow group is : $C")
  S = union(Set(keys(factor(a).fac)), Set(keys(factor(discriminant(L)).fac)))
  S = union(S, Set(extra))

  g = Set(elem_type(C)[])
  for p = S
    P = prime_ideals_over(L, typeof(p)[p])
    P1 = norm_1_generators(P)
    for x = P1
      push!(g, sum([e*preimage(mC, k) for (k, e) = x.fac]))
    end
  end

#  println("found $g")
  sC, msC = sub(C, collect(g))

  #think: might the better using quo, test for zero and a function
  #       that adds relations to a quo.
  if order(sC) != order(C)
    p = 2
    stable = 0
    while true
      while p in S
        p = next_prime(p)
      end
      change = false
      P1 =  norm_1_generators(prime_ideals_over(L, [p]))
      for x = P1
        y = sum([e*preimage(mC, k) for (k, e) = x.fac]) # move to log function(?)
        if !has_preimage_with_preimage(msC, y)[1]
          change = true
          push!(g, y)
          push!(S, p)
          sC, msC = sub(C, collect(g))
          if order(sC) == order(C)
#            println("groups are the same")
            break
          end
        end
      end
      p = next_prime(p)
      if change
        stable = 0
      else
        stable += 1
        if stable > 5
          break
        end
      end
    end
  else
#    println("groups are the same")
  end

  SP = prime_ideals_over(L, [x for x = S])

  U, mU = sunit_group_fac_elem(SP)
  u, mu = sunit_group_fac_elem(collect(S))

  h = elem_type(u)[]
  for i=1:ngens(U)
    x = mU(U[i])
    y = norm(x)
    push!(h, preimage(mu, y))
    #@assert norm(evaluate(x)) == evaluate(image(mu, h[end]))
  end
  s, ms = sub(u, h)
  mp = FinGenAbGroupHom(U, u, reduce(vcat, [x.coeff for x=h]))

  fl, p = has_preimage_with_preimage(mp, preimage(mu, a))
  if fl
    return true, mU(p)
  else
    return false, FacElem(one(K))
  end
end

