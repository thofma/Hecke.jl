



#See Gerald J. Janusz (1980) Crossed product orders and the schur index,
#Communications in Algebra, 8:7, 697-706
function is_split_at_p(O::NfOrd, GC::Array{NfToNfMor, 1}, Coc::Function, p::Int, n::Int, Rx::GFPPolyRing)

  lp = prime_decomposition(O, p, cached = true)
  e = gcd(length(GC), lp[1][2])
  if e == 1
    return true
  end
  P = lp[1][1]
  f = gcd(length(GC), degree(P))
  if f == 1 && iszero(mod(norm(P)-1, e*n))
    return true
  end
  if length(lp) != 1
    @vtime :BrauerObst 1  Gp = decomposition_group(P, G = GC, orderG = e*f) 
    #I don't really want the decomposition group of the p-sylow, but the p-sylow of the decomposition group.
    #Therefore, if the p-sylow is not normal, I have to try different primes.
    i = 1
    while length(Gp) != e*f
      i += 1
      P = lp[i][1]
      Gp = decomposition_group(P, G = GC, orderG = e*f) 
    end
  else
    Gp = GC
  end
  f1 = divexact(degree(P), f)
  q = p^f1 #Cardinality of the residue field
  
  F, mF = Hecke.ResidueFieldSmall(O, P)
  theta1 = _find_theta(Gp, F, mF, e)
  theta = Rx(theta1.prim_img)
  
  K = nf(O)
  fmod = Rx(K.pol)
  #I have found my generators. Now, we find the elements to test if it splits.
  @assert divisible(norm(P)-1, e)
  c = divexact(norm(P)-1, e)
  if !iszero(mod(c, n))
    powtheta = theta
    zeta = 0
    for k = 1:e-1
      zeta += Coc(powtheta, theta)::Int
      powtheta = compose_mod(powtheta, theta, fmod)
    end
    zeta = mod(zeta * c, n)
    if !iszero(zeta)
      return false
    end
  end
  
    
  #The second element is a little more complicated. 
  if f == 1
    return true
  end
  frob1 = _find_frob(Gp, F, mF, e, f, q, theta1)
  frob = Rx(frob1.prim_img)

  
  if iszero(mod(q-1, e*n))
    lambda = mod(Coc(frob, theta)- Coc(theta, frob), n)::Int
    return iszero(lambda)
  end
  lambda = Coc(frob, theta)::Int
  powtheta = theta
  s, t = divrem(q-1, e)
  if !iszero(mod(s+1, n))
    for k = 1:t
      lambda -= (s+1) * Coc(powtheta, theta)::Int
      powtheta = compose_mod(powtheta, theta, fmod)
    end
  else
    powtheta = _pow_as_comp(theta, t+1, fmod)
  end
  if !iszero(mod(s, n))
    for k = t+1:(e-1)
      lambda -= s * Coc(powtheta, theta)::Int
      powtheta = compose_mod(powtheta, theta, fmod)
    end
  end
  powtheta = _pow_as_comp(theta, mod(q, e), fmod)
  lambda = mod(lambda - Coc(powtheta, frob), n)::Int
  return iszero(lambda)
end


################################################################################
#
#  IsSplit for crossed product algebras: prime power case
#
################################################################################


function cpa_issplit(K::AnticNumberField, G::Vector{NfToNfMor}, Stab::Vector{NfToNfMor}, Coc::Function, p::Int, v::Int, Rx::GFPPolyRing)

  O = maximal_order(K)
  r, s = signature(O)
  @vtime :BrauerObst 1 if p == 2 && r != degree(K) && !is_split_at_infinity(K, Coc, Rx)
    return false    
  end
  # Now, the finite primes.
  # The crossed product algebra is ramified at the ramified primes of the field (and at the primes dividing the values
  # of the cocycle, but our cocycle has values in the roots of unity...
  # I only need to check the tame ramification.
  # The exact sequence on Brauer groups and completion tells me that I have one degree of freedom! :)
  
  lp = Hecke.ramified_primes(O)
  if p in lp
    for q in lp
      if q != p 
        @vtime :BrauerObst 1 fl = is_split_at_p(O, G, Stab, Coc, Int(q), p^v, Rx)
        if !fl
          return false
        end
      end
    end
  else
    for i = 1:length(lp)-1
      @vtime :BrauerObst 1 fl = is_split_at_p(O, G, Stab, Coc, Int(lp[i]), p^v, Rx)
      if !fl
        return false
      end
    end
  end
  return true
  
end

function is_split_at_p(O::NfOrd, GC::Vector{NfToNfMor}, Stab::Vector{NfToNfMor}, Coc::Function, p::Int, n::Int, Rx::GFPPolyRing)

  lp = prime_decomposition(O, p, cached = true)
  e = gcd(length(GC), lp[1][2])
  if e == 1
    return true
  end
  
  P = lp[1][1]
  @assert divisible(norm(P)-1, e)
  c = divexact(norm(P)-1, e)
  f = gcd(length(GC), degree(P))
  if f == 1 && iszero(mod(c, n))
    return true
  end 
  if length(lp) != 1
    @vtime :BrauerObst 1  Gp = decomposition_group(P, G = GC, orderG = e*f)
    #I don't really want the decomposition group of the p-sylow, but the p-sylow of the decomposition group.
    #Therefore, if the p-sylow is not normal, I have to try different primes.
    i = 1
    while length(Gp) != e*f
      i += 1
      P = lp[i][1]
      Gp = decomposition_group(P, G = GC, orderG = e*f)
    end
  else
    Gp = GC
  end
  GpStab = NfToNfMor[]
  for i = 1:length(Gp)
    if Gp[i] in Stab
      push!(GpStab, Gp[i])
    end
  end
  #I need the inertia subgroup to determine e and f
  InGrp = inertia_subgroup(P, G = GpStab)
  e = length(InGrp)
  if e == 1
    return true
  end
  f = divexact(length(GpStab), e)
  c = divexact(norm(P)-1, e)
  if f == 1 && iszero(mod(c, n))
    return true
  end 
  f1 = divexact(degree(P), f)
  q = p^f1 #Cardinality of the residue field

  F, mF = Hecke.ResidueFieldSmall(O, P)
  theta1 = _find_theta(GpStab, F, mF, e)
  theta = Rx(theta1.prim_img)
  fmod = Rx(nf(O).pol)
  #I have found my generators. Now, we find the elements to test if it splits.
  if !iszero(mod(c, n))
    powtheta = theta
    zeta = 0
    for k = 1:e-1
      zeta += Coc(powtheta, theta)
      powtheta = compose_mod(powtheta, theta, fmod)
    end
    zeta = mod(zeta * c, n)
    if !iszero(zeta)
      return false
    end
  end
    
  if f == 1
    return true
  end
  frob1 = _find_frob(GpStab, F, mF, e, f, q, theta1)
  frob = Rx(frob1.prim_img)
  if iszero(mod(q-1, e*n))
    lambda = mod(Coc(frob, theta)- Coc(theta, frob), n)
    return iszero(lambda)
  end
  lambda = Coc(frob, theta)
  powtheta = theta
  s, t = divrem(q-1, e)
  if !iszero(mod(s+1, n))
    for k = 1:t
      lambda -= (s+1) * Coc(powtheta, theta)
      powtheta = compose_mod(powtheta, theta, fmod)
    end
  else
    powtheta = _pow_as_comp(theta, t+1, fmod)
  end
  if !iszero(mod(s, n))
    for k = t+1:(e-1)
      lambda -= s * Coc(powtheta, theta)
      powtheta = compose_mod(powtheta, theta, fmod)
    end
  end
  powtheta = _pow_as_comp(theta, mod(q, e), fmod)
  lambda = mod(lambda - Coc(powtheta, frob), n)
  return iszero(lambda)

end

