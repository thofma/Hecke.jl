export SchoofApprox, SchoofApproxError, BelabasFriedmannApprox,
       BelabasFriedmannApproxError, SchoofApproxArb,
       BelabasFriedmannApproxArb,
       @with_round_up, @with_round_down

import Base: log, sqrt

################################################################################
#
# Macros to make floating point life (hopefully) easier 
#
################################################################################

macro with_round_down(expr, T)
  quote
    with_rounding($T, RoundDown) do
      $expr
    end
  end
end

macro with_round_up(expr, T)
  quote
    with_rounding($T, RoundUp) do
      $expr
    end
  end
end

################################################################################
#
# Computes the Schoof approximation A of the residue of the Dedekind zeta
# function of O using prime ideals with Norm < B
# F controls the FloatingType during the computation
# Returns (A,err) where err::Tc is the rounding error
#
################################################################################

function SchoofApprox(O::PariMaximalOrder,
                           B::Int,
                           Tc = BigFloat)
  
  if !(Tc in Any[Float32,Float64,BigFloat])
    error("Tc must be Float32, Float64 or BigFloat")
  end

  q = Rational{BigInt}(0)::Rational{BigInt}
  
  num_factors = Int(0)::Int

  li = Array{Nemo.MaximalOrderIdeal,1}

  pdown = one(Tc)::Tc
  pup = (pdown)::Tc

  num_factors = (Int64(0))::Int64

  a = (Rational{Int64}(0))::Rational{Int64}

  p = Integer(2)

  x = Float64(0)
  y = Float64(0)

  err = Tc(1)
  prod = Tc(1)

  looptime = @elapsed while p < B

    x += @elapsed li = my_prime_decomposition(O,p)
    num_factors += 1+length(li)

    a = Tc(Rational{Int64}((p-1)//p))


    (prod,err) = MultiplyWithErrorRelative(prod,err,a,ErrorWhileRoundToNearestRelative(a))

    for P in li
      a = (norm(P))::BigInt
      if a > B 
        continue
      end
      a = (Tc(Rational{Int64}(a//(a-1))))
      (prod,err) = MultiplyWithErrorRelative(prod,err,a,ErrorWhileRoundToNearestRelative(a))

    end 

    p = next_prime(p)
    #println("next prime")
  end

  print("Time for prime decompositon: ")
  println(x)
  print("Total time for product computation: ")
  println(looptime)

  println(err)
  
  prod = log(prod)

  with_rounding(Tc,RoundUp) do
    err = log(err)
  end

  # add error coming from log calculation
  err += ErrorWhileRoundToNearest(prod)

  prod,err
end

function SchoofApproxArb(O::PariMaximalOrder, B::Int)

  li = Array{Nemo.MaximalOrderIdeal,1}

  a = (Rational{BigInt}(0))::Rational{BigInt}

  p = Integer(2)

  x = Float64(0)
  y = Float64(0)

  prod = arb_t(1)

  looptime = @elapsed while p < B

    x += @elapsed li = my_prime_decomposition(O,p)

    a = arb_t(ZZ(1)) - arb_t(QQ(1)/QQ(p))

    mul(prod,prod,a)

    for P in li
      a = (norm(P))::BigInt
      if a > B 
        continue
      end
      a = arb_t(ZZ(a)//ZZ(a-1))
      
      mul(prod,prod,a)

    end 

    p = next_prime(p)
    #println("next prime")
  end

  print("Time for prime decompositon: ")
  println(x)
  print("Total time for product computation: ")
  println(looptime)

  prod = log(prod)

  return prod

end
################################################################################
#
# Compute an upper bound on the error term of the Schoof approximation
# Output is a function F : Tc -> Tc
#
################################################################################

function SchoofApproxError(O::PariMaximalOrder, Tc = BigFloat)
  return SchoofApproxError((discriminant(O))::Integer,degree(O.pari_nf.nf.pol),Tc)
end

function SchoofApproxError(d::Integer,
                                  n::Integer,
                                  Tc = BigFloat)

  C = @with_round_down(Tc(QQ(125506)//QQ(100000)),Tc)
  CC = @with_round_down(Tc(QQ(3)//QQ(2)),Tc)
  log2 = Tc(0)::Tc

  log2 = @with_round_up(log(Tc(2)),Tc)
  #  log2 = log(Tc(2))
  
  d = abs(d)
  logd = Tc(0)::Tc
  piinv = Tc(0)::Tc

  # roundup all the stuff in the denominator
  pipi = Tc(pi,RoundUp)
  with_rounding(Tc,RoundDown) do
    piinv = pipi^-1
  end

  with_rounding(Tc,RoundDown) do
    logd = log(d)
  end
  function F(X::Tc)
    A1 = (Tc(0))::Tc
    A2 = (Tc(0))::Tc
    A3 = (Tc(0))::Tc
    A4 = (Tc(0))::Tc
    A5 = (Tc(0))::Tc
    logX = (Tc(0))::Tc
    logX2 = (Tc(0))::Tc
    logX3 = (Tc(0))::Tc
    sqrtX = (Tc(0))::Tc
    XCC = (Tc(0))::Tc
    XCClog2 = (Tc(0))::Tc
    A = (Tc(0))::Tc
    
    sqrtX = @with_round_up(sqrt(X),Tc)
    logX = @with_round_up(log(X),Tc)
    logX2 = @with_round_up(log(X)^2,Tc)
    logX3 = @with_round_up(log(X)^3,Tc)
    XCClog2 = @with_round_up(X^CC*log2,Tc)

    A1 = @with_round_down(logd/sqrtX,Tc)
    A2 = @with_round_down(Tc(3)*piinv + (Tc(6)+Tc(2)*piinv)/logX + 4 / (logX2),Tc)
    A3 = @with_round_down((Tc(n+1))*log(X)/sqrtX,Tc)
    A4 = @with_round_down(3/2*piinv+(3*piinv)/logX+6/logX2 + 4 /logX3,Tc)
    A5 = @with_round_down(Tc(2) *C*(Tc(n)+1) *Tc(2)/@with_round_up(sqrtX*logX,Tc)  + (CC)/(XCClog2),Tc)
    A = @with_round_down(A1*A2+A3*A4+A5,Tc)
    return A
  end
  return F
end

################################################################################
#
# Compute the Belabas-Friedmann Approximation g(B) using primes up to norm
# power B.
# Tc controls the floating point type during the computation
# Output will be of type Tc
# I guess I should parametrize it?!
# 
################################################################################

function BelabasFriedmannApprox(O::PariMaximalOrder,
                                            B::Int64,
                                            Tc = BigFloat)

  xx0 = B

  # I want xx0 to be divisible by 9!
  # Because I want xx0/9 to be exactly representable

  while !(mod(xx0,9) == 0)
    xx0 += 1
  end

  x = Float64(0)

  xx09 = div(xx0,9)

  println("Have to use prime ideals with norm power up to ", xx0)

  sumforQ1 = BigFloat(0)
  sumforQ2 = BigFloat(0)

  p = 2

  summ = Tc(0)
  esumm = Tc(0)

  logxx0 = log(Tc(xx0))
  elogxx0 = ErrorWhileRoundToNearest(logxx0)

  logxx09 = log(Tc(div(xx0,9)))
  elogxx09 = ErrorWhileRoundToNearest(logxx09)

  sqrtxx0 = sqrt(Tc(xx0))
  esqrtxx0 = ErrorWhileRoundToNearest(sqrtxx0)

  sqrtxx09 = sqrt(Tc(div(xx0,9)))
  esqrtxx09 = ErrorWhileRoundToNearest(sqrtxx09)


  (prodx,eprodx) = MultiplyWithError(logxx0,elogxx0,sqrtxx0,esqrtxx0)

  (prodx9,eprodx9) = MultiplyWithError(logxx09,elogxx09,sqrtxx09,esqrtxx09)

  

  function comp_summand(p,m,aa,bb)
    logp = log(Tc(p))
    elogp = ErrorWhileRoundToNearest(logp)

    pm2 = Tc(p)^(Tc(m/2))
    epm2 = ErrorWhileRoundToNearest(pm2)

    (pm2inv,epm2inv) = InverseWithError(pm2,epm2)

    pro,epro= MultiplyWithError(logp,elogp,pm2inv,epm2inv)

    # Jetzt kommt p^(m/2) m log(p)
    pro2,epro2 = MultiplyWithError(logp,elogp,pm2,epm2)
    pro2,epro2 = MultiplyWithError(pro2,epro2,Tc(m),Tc(0))
    
    # Now the inverse
    inv2,einv2 = InverseWithError(pro2,epro2)

    # Now sqrt(x)log(X)/p^(m/2)*m*p 
    pro3,epro3 = MultiplyWithError(aa,bb,inv2,einv2)

    pro3,epro3 = AddWithError(pro3,epro3,-Tc(1),Tc(0))

    summand,esummand = MultiplyWithError(pro,epro,pro3,epro3)

    return summand,esummand
  end
   

  while p < xx0

    max_exp = max_power_in(p,xx0)

    for m in 1:max_exp

      summand,esummand = comp_summand(p,m,prodx,eprodx)
      
      summ,esumm = AddWithError(summ,esumm,-summand,esummand)
    end

    x += @elapsed lP = my_prime_decomposition(O,p)

    for P in lP
      if norm(P) < xx0
        max_exp = max_power_in(norm(P),xx0)
      
        for m in 1:max_exp

          summand,esummand = comp_summand(norm(P),m,prodx,eprodx)

          summ,esumm = AddWithError(summ,esumm,summand,esummand)
        end

      end

    end

    if p < xx09
      
      max_exp = max_power_in(p,xx09)

      for m in 1:max_exp
        summand,esummand = comp_summand(p,m,prodx9,eprodx9)
        summ,esumm = AddWithError(summ,esumm,summand,esummand)
      end

      for P in lP
        if (norm(P) < xx09)
          max_exp = max_power_in(norm(P),xx09)
          
          for m in 1:max_exp
            summand,esummand = comp_summand(norm(P),m,prodx9,eprodx9)
            summ,esumm = AddWithError(summ,esumm,-summand,esummand)
          end
        end
      end
    end
    p = next_prime(p)
  end

  sqrtxx0 = sqrt(Tc(xx0))
  esqrt = ErrorWhileRoundToNearest(sqrtxx0)
  
  log3xx0 = log(Tc(3*xx0))
  elog3xx0 = ErrorWhileRoundToNearest(log3xx0)

  pr,epr = MultiplyWithError(sqrtxx0,esqrt,Tc(2),Tc(0))
  pr,epr = MultiplyWithError(pr,epr,log3xx0,elog3xx0)

  pr,epr = InverseWithError(pr,epr)

  pr,epr = MultiplyWithError(pr,epr,Tc(3),Tc(0))

  pr,epr = MultiplyWithError(pr,epr,summ,esumm)

  println("Time for prime decompositon: ", x)

  return pr,epr

end

function BelabasFriedmannApproxArb(O::PariMaximalOrder, B::Int64)

  xx0 = B

  # I want xx0 to be divisible by 9!
  # Because I want xx0/9 to be exactly representable

  while !(mod(xx0,9) == 0)
    xx0 += 1
  end

  x = Float64(0)

  xx09 = div(xx0,9)

  println("Have to use prime ideals with norm power up to ", xx0)

  sumforQ1 = BigFloat(0)
  sumforQ2 = BigFloat(0)

  p = 2

  summ = arb_t(0)
  esumm = arb_t(0)

  logxx0 = log(arb_t(xx0))

  logxx09 = log(arb_t((div(xx0,9))))

  sqrtxx0 = sqrt(arb_t(xx0))

  sqrtxx09 = sqrt(arb_t(div(xx0,9)))
  
  prodx = logxx0 * sqrtxx0

  prodx9 = logxx09 * sqrtxx09

  function comp_summand(p,m,aa)
    logp = log(arb_t(p))

    pm2 = arb_t(p)^(arb_t(ZZ(m)//ZZ(2)))

    pm2inv = inv(pm2)

    pro = logp * pm2inv

    # Jetzt kommt p^(m/2) m log(p)

    pro2 = logp*pm2
    pro2 = pro2*m
    
    # Now the inverse
    inv2 = inv(pro2)

    # Now sqrt(x)log(X)/p^(m/2)*m*p 
    pro3 = aa*inv2
    pro3 = pro3 - 1

    return pro*pro3
  end
   

  while p < xx0

    max_exp = max_power_in(p,xx0)

    for m in 1:max_exp

      summand = comp_summand(p,m,prodx)
      
      summ = summ - summand
    end

    x += @elapsed lP = my_prime_decomposition(O,p)

    for P in lP
      if norm(P) < xx0
        max_exp = max_power_in(norm(P),xx0)
      
        for m in 1:max_exp

          summand = comp_summand(norm(P),m,prodx)

          summ = summ + summand
        end

      end

    end

    if p < xx09
      
      max_exp = max_power_in(p,xx09)

      for m in 1:max_exp
        summand  = comp_summand(p,m,prodx9)
        summ = summ + summand
      end

      for P in lP
        if (norm(P) < xx09)
          max_exp = max_power_in(norm(P),xx09)
          
          for m in 1:max_exp
            summand = comp_summand(norm(P),m,prodx9)
            summ = summ-summand
          end
        end
      end
    end
    p = next_prime(p)
  end

  
  log3xx0 = log(arb_t(3*xx0))

  pr = sqrtxx0*2

  pr = pr * log3xx0

  pr = inv(pr)

  pr = pr*3

  pr = pr*summ

  println("Time for prime decompositon: ", x)

  return pr

end

################################################################################
#
# Compute an upper bound on the error term of the Belabas-Friedmann
# approximation. Output is a function F : Tc -> Tc bounding the error.
#
################################################################################

function BelabasFriedmannApproxError(O::PariMaximalOrder,
                                          Tc = BigFloat)
  return BelabasFriedmannApproxError(discriminant(O),degree(O.pari_nf.nf.pol), Tc)
end

function BelabasFriedmannApproxError(disc::Integer,
                               degree::Integer,
                               Tc = BigFloat)

  logd_up = Tc(0)::Tc
  logd_down = Tc(0)::Tc
  sqrt_logd_up = Tc(0)::Tc
  
  with_rounding(Tc,RoundDown) do
    logd_down = log(Tc(abs(disc)))
  end

  with_rounding(Tc,RoundUp) do
    logd_up = log(Tc(abs(disc)))
    sqrt_logd_up = sqrt(logd_up)
  end

  n = BigFloat(degree)

  

  C1 = @with_round_down(Tc(QQ(2324)/QQ(1000)),Tc)
  C2 = @with_round_down(Tc(QQ(388)/QQ(100)),Tc)
  C3 = Tc(2) 
  C4 = @with_round_down(Tc(QQ(426)/QQ(100)),Tc)
  
  function F(X::Tc)
    A1 = @with_round_down(C1*logd_down/(@with_round_up(sqrt(X)*log(3*X),Tc)),Tc)
    A2 = @with_round_down(1 + C2/@with_round_up(log(X/9),Tc),Tc)
    A3 = @with_round_down(1 + 2/sqrt_logd_up,Tc)
    A4 = @with_round_down(C4*(n-1)/@with_round_up(sqrt(X)*logd_up,Tc),Tc)

    return A1*(A2*A3^2 + A4)
  end
  return F
end

function FindThreshold(f,C,ste,decreasing::Bool, Tc=BigFloat)
  T = Tc
  x0 =  T(70)
  x1 = x0

  y = f(x0)

  while y > C
    x0 = x1
    x1 = 2*x0
    y = f(x1)
    #println(x1)
  end
      
  dista = abs(x0-x1)

  while !( y < C && dista < ste)
    if y > C 
      x1 = x0 + 3*dista/2
      #println("increasing x1:")
      #println(x1)
    else
      x1 = x0 - dista/2
      #println("decreasing x1:")
      #println(x1)
    end

    dista = abs(x1-x0)
  
    #println(dista)

    x0 = x1
    y = f(x0)

#    print("\nhere is x0:")
#    print(x0)
#    print("\nhere is y:")
#    print(y)
#    print(y > C)

  end
  return x0
end
function AddWithError{T}(a::T,ea::T,b::T,eb::T)
  c = a+b
  ec = T(0)

  with_rounding(T,RoundUp) do
    ec = ea + eb + T(QQ(2))^(exponent(c)-Base.precision(c)-1)
  end

  return (c,ec)
end

function MultiplyWithError{T}(a::T,ea::T,b::T,eb::T)
  c = a*b
  ec = T(0)
  with_rounding(T,RoundUp) do
    ea*(b+eb)
    ec = ea*(abs(b)+eb)+eb*abs(a)+T(QQ(2))^(exponent(c)-Base.precision(c)-1)
  end
  return (c,ec)
end

function InverseWithError{T}(a::T,ea::T)
  c = a^-1
  ec = @with_round_up(ErrorWhileRoundToNearest(c) + ea*T(QQ(2))^(-2*exponent(a)+3),T)
  return (c,ec)
end

function ErrorWhileRoundToNearest{T}(a::T)
  ### There is some issue with T from IEEE (FloatXX) or T from MPFR (BigFloat)
  ### The mantissas are normalized differently (0 < m \leq 1/2 and 1/2 < m \leq 1)
  return T(QQ(2))^(exponent(a)-Base.precision(a))
end

function ErrorWhileRoundToNearestRelative{T}(a::T)
  ### There is some issue with T from IEEE (FloatXX) or T from MPFR (BigFloat)
  ### The mantissas are normalized differently (0 < m \leq 1/2 and 1/2 < m \leq 1)
  return T(1) + T(2)^(-Base.precision(T(0))+1)
end

function MultiplyWithErrorRelative{T}(a::T,ea::T,b::T,eb::T)
  c = a*b
  ec = T(1)
  with_rounding(T,RoundUp) do
    ec = ea*eb*(1+T(2)^(-Base.precision(c)+1))
  end
  return (c,ec)
end

# Compute the maximal m such that a^m < b
# b is assumed to be >= 1
function max_power_in(a::Integer,b::Integer)
  if a >= b
    return 0
  end
  m = Integer(0)
  c = a
  while c < b
    c *= a
    m = m+1
  end
  return m
end

################################################################################
#
# Approximate the residue of the Dedekind zeta function of O within an error
# of err. For reason of type-stability, the return value is _always_ a
# BigFloat with some BigFloat-precision (can be different from current prec)
#
# Tc controls the starting FloatingType used in the computation.
# Default is BigFloat with 128 bit precision.
# Note that if Tc has not sufficient precision to get error within err,
# types/precision will be changed as in the following scheme:
# Float32 -> Float64 -> BigFloat(128) -> BigFloat(256) -> ...
# Use different Tc at own risk: if type/precision is changed, _all_ prime
# ideals have to be decomposed again. (I/You really don't want to save them)
#   
# We use sick metaprogramming to produce functions
# SchoofApprox(O,error,floating_type)::BigFloat
# BelabasFriedmannApprox(O,error,floating_type)::BigFloat
#
################################################################################

for (s,approxx,approxx_error) = [("SchoofApprox", SchoofApprox, SchoofApproxError), ("BelabasFriedmannApprox", BelabasFriedmannApprox, BelabasFriedmannApproxError)]
  @eval begin
    function ($(symbol(s)))(O::PariMaximalOrder,
                                  err::Union(Float32,Float64,BigFloat),
                                  Tc = BigFloat)
      if !(Tc in Any[Float32,Float64,BigFloat])
        error("Tc must be Float32, Float64 or BigFloat")
      end

      val = Tc(0)
      cur_error = Tc(0)

      old_prec = get_bigfloat_precision()

      set_bigfloat_precision(128)

      # Compute an upper bound for the error of the Schoof approximation
      F = $approxx_error(O, BigFloat)

      err = Tc(err,RoundDown)::Tc

      # Small offset which captures inexactness of floating point operations
      epsprime = Tc(QQ(2))^(-div(Base.precision(Tc(1)),2))
      
      @assert err > epsprime

      # Find small xx0 such that F(xx0) < err-epsprime
      xx0 = FindThreshold(F,BigFloat(err-epsprime,RoundDown),Tc(10),true,BigFloat)::BigFloat

      x0 = Int(Base.ceil(xx0))

      println("Have to split prime ideals up to norm: ",x0)

      # Compute the value together with the error
      val, cur_error = $approxx(O,x0,Tc)

      # There is an additional error when rounding to BigFloat
      # (maybe from higher precision during computation to old_prec)

      while cur_error >= epsprime
        if Tc == Float32
          println("Switching from Float32 to Float64")
          Tc = Float64
          cur_error = Tc(cur_error,RoundDown)
        elseif Tc == Float64
          println("Switching from Float64 to BigFloat")
          Tc = BigFloat
          cur_error = Tc(cur_error,RoundDown)
        elseif Tc == BigFloat
          set_bigfloat_precision(2*get_bigfloat_precision())
          cur_error = Tc(cur_error,RoundDown)
          println("Increasing BigFloat precision to ", get_bigfloat_precision())
        end
        
        val, cur_error = $approxx(O,x0,Tc)
        println("target error:", epsprime)
        println("current error:", cur_error)
      end

      # Don't forget to reset the global parameters!
      val = BigFloat(val)
      cur_error = BigFloat(cur_error)

      set_bigfloat_precision(old_prec)

      return val
    end
  end
end

for (s,approxx,approxx_error) = [("SchoofApproxArb", SchoofApproxArb, SchoofApproxError), ("BelabasFriedmannApproxArb", BelabasFriedmannApproxArb, BelabasFriedmannApproxError)]
  @eval begin
    function ($(symbol(s)))(O::PariMaximalOrder,
                                  err::Union(Float32,Float64,BigFloat))
      val = arb_t(0)
      cur_error = arb_t(0)

      old_prec = get_arb_precision()

      set_arb_precision(128)

      # Compute an upper bound for the error of the Schoof approximation
      F = $approxx_error(O, BigFloat)


      # Small offset which captures inexactness of floating point operations
      epsprime = BigFloat(QQ(2))^(-div(get_arb_precision(),2))
      epsprimeexponent = -div(get_arb_precision(),2)
      
      # Find small xx0 such that F(xx0) < err-epsprime
      xx0 = FindThreshold(F,BigFloat(err-epsprime,RoundDown),BigFloat(10),true,BigFloat)::BigFloat

      x0 = Int(Base.ceil(xx0))

      println("Have to split prime ideals up to norm: ",x0)

      # Compute the value together with the error
      val = $approxx(O,x0)

      # There is an additional error when rounding to BigFloat
      # (maybe from higher precision during computation to old_prec)

      while gttwopower(radius(val), epsprimeexponent)
        set_arb_precision(2*get_arb_precision())
        println("Increasing Arb precision to ", get_arb_precision())
        
        val = $approxx(O,x0)
        println("target error:", epsprime)
        println("current error:", radius(val))
      end

      # Don't forget to reset the global parameters!

      set_bigfloat_precision(old_prec)

      return BigFloat(midpoint(val))
    end
  end
end


