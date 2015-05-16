################################################################################
#
#   PrimeDecomposition.jl: prime decomposition in absolute number fields
#
################################################################################


export PrimeDecomposition, ReducePolyModp, SquareFreeFactorization,
       DistinctDegreeFactorization, IsSquareFree, CantorZassenhaus,
       Factorization

################################################################################
#
#   decomposition for odd non-index divisors
#
################################################################################

function PrimeDecomposition(O::PariMaximalOrder,p::Int)

  K = O.pari_nf.nf
  f = O.pari_nf.nf.pol
  
  R = parent(f)

  I = IdealSet(O)

  result = typeof(I())[]

  x = R([QQ(0),QQ(1)])
  
  if mod(index(O),p) == 0
    error("p divides the index")
  end

  if(iseven(p))
    error("p must be odd")
  end
  
  g = ReducePolyModp(f,p)

  FF = Factorization(g)

  for u in FF
    co = typeof(QQ(0))[]
    for i in 1:degree(u[1])+1
      push!(co,QQ(ZZ(string(coeff(u[1],i-1)))))
    end
    b = K(R(co))
    ideal = I()
    ideal.gen_one = p
    ideal.gen_two = b
    ideal.is_prime = 1
    ideal.den = 1
    ideal.parent = I
    ideal.splitting_type = u[2], degree(u[1])
    ideal.norm = p^degree(u[1])
    ideal.minimum = p

    # We have to do something to get 2-normal presentation:
    # if ramified or valuation val(b,P) == 1, (p,b)
    # is a P(p)-normal presentation
    # otherwise we need to take p+b
    # I SHOULD CHECK THAT THIS WORKS

    if !((mod(norm(b),(ideal.norm)^2) != 0) || (u[2] > 1))
      ideal.gen_two  = K(p) + b
    end

    ideal.gens_are_normal = p
    ideal.gens_are_weakly_normal = 1

    push!(result,ideal)
  end
  return result
end

################################################################################
#
#   auxillary function to reduce polynomials mod p
#   should be obsolete as soon as flint polys over finite fields are available
#
################################################################################

function ReducePolyModp{S}(f::fmpq_poly{S},p::Int)
  assert(isprime(p))
  F,a = FiniteField(p,1,"a")

  R,T = PolynomialRing(F,string(S))

  b = typeof(F(0))[]

  for i in 0:degree(f)
    push!(b,F(coeff(f,i).num))
  end
  return R(b)
end

################################################################################
#
#   Polynomial factorization using squarefree factorization,
#   distinct-degree factorization and Cantor-Zassenhaus
#   (Waiting for flint polynomials!)
#
################################################################################

function SquareFreeFactorization{T,S}(f::Nemo.Poly{Nemo.fq_nmod{T},S})
  result = (typeof(f),Int)[]

  if degree(f) == 0
    push!(result,(f,1))
    return result
  end 
  

  polyring = parent(f)
  
  F = polyring.base_ring
  
  p = F.p

  i = 1

  R = one(polyring)
  
  g = derivative(f)
  
  if !iszero(g) 
    c = gcd(f,g)
    w = divexact(f,c)
    while !isone(w)
      y = gcd(w,c)
      z = divexact(w,y)
      R = R*z^i
      if degree(z) != 0
        push!(result,(z,i))
      end
      i = i+1
      w = y
      c = divexact(c,y)
    end
    if !isone(c)
      c = TakepthRoot(c)
      SS = SquareFreeFactorization(c)
      for s in SS
        push!(result,(s[1],s[2]*p))
      end
      return result
    else
      return result
    end
  else
    f = TakepthRoot(f)
    SS = SquareFreeFactorization(f)
    for s in SS
      push!(result,(s[1],s[2]*p))
    end
    return result
  end
end 

function IsSquareFree{T,S}(f::Nemo.Poly{Nemo.fq_nmod{T},S})
  dec = SquareFreeFactorization(f)
  if length(dec) == 1 && dec[1][2] == 1
    return true
  end
  return false
end

function DistinctDegreeFactorization{T,S}(f::Nemo.Poly{Nemo.fq_nmod{T},S})
  if !IsSquareFree(f)
    error("input is not squarefree")
  end
  if !isone(coeff(f,degree(f)))
    error("input not monic")
  end 
  R = parent(f)
  F = R.base_ring
  q = F.n
  i = 1
  result = (typeof(f),Int)[]
  h = f
  while degree(h) >= 2*i
    x = R([F(0),F(1)])
    temp_pol = powermod(x,h,q^i)
    temp_pol = temp_pol - x
    g = gcd(h,temp_pol)
    if !isone(g)
      push!(result,(g,i))
      h = divexact(h,g)
    end
    i = i+1
  end 
  if degree(h) != 0
    push!(result,(h,degree(h)))
  end
  if length(result) == 0
    push!(result,(f,1))
  end
  return result
end

function CantorZassenhaus{T,S}(f::Nemo.Poly{Nemo.fq_nmod{T},S},d::Int64)
  
  if iseven(parent(f).base_ring.p)
    error("characterstic must be odd")
  end

  R = parent(f)
  F = R.base_ring
  q = F.n

  r = div(degree(f),d) # this is the number of factors we need

  result = Set{typeof(f)}([])

  push!(result,f)

  function red_mod_q(a)
    return F(a)
  end 

  i = 0
  while length(result) < r
    i += 1
    coefficients = Base.rand(1:q,degree(f))
    coefficients = map(red_mod_q,coefficients)

    if find(iszero,coefficients) == [1:degree(f);]
      continue
    end
   
    while iszero(coefficients[length(coefficients)])
      pop!(coefficients)
    end

    h =  R(coefficients)
    h = mod(h,f)
    g = powermod(h,f,(div(q^d - 1,2)))
    #g = mod(g,f)
    g = g - 1
    
    for u in result
      if degree(u) <= d
        continue
      end
      h = gcd(g,u)
      if !isone(h) &&  !(h == u)
        delete!(result,u)
        push!(result,h)
        push!(result,divexact(u,h))
      end
    end
  end
  
  return result
end

function Factorization{T,S}(f::Nemo.Poly{Nemo.fq_nmod{T},S})

  squarefree = SquareFreeFactorization(f)

  result = (typeof(f),Int)[]

  for s in squarefree
    distinct_degree  = DistinctDegreeFactorization(s[1])
    for t in distinct_degree
      factoriz = CantorZassenhaus(t[1],t[2])
      for u in factoriz
        push!(result,(u,s[2]))
      end
    end
  end
  return result
end

function TakepthRoot{T,S}(f::Nemo.Poly{Nemo.fq_nmod{T},S})
  i = 0
  j = 0
  
  R = parent(f)

  F = parent(f).base_ring

  p = F.p

  newcoeff = typeof(F(0))[]

  while i <= degree(f)
    push!(newcoeff,coeff(f,i)^(F.p^(F.n-1)))
    i = i+p
  end
  return R(newcoeff)
end

function powermod{S}(f::Nemo.Poly{S},g::Nemo.Poly{S},m::Integer) 
  if m == 1
    return mod(f,g)
  end 

  if iseven(m) 
    return mod((powermod(f,g,div(m,2)))^2,g)
  else
    return mod((f*powermod(f,g,m-1)),g)
  end
end
