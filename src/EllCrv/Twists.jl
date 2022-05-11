###############################################################################
#
#  Twists
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################


export quadratic_twist, quadratic_twists, is_twist, twists

@doc Markdown.doc"""
    quadratic_twist(E::EllCrv{T}}, d::T) -> EllCrv{T}

Compute the quadratic twist of $E$ by $d$.
"""
#Needs more testing over characteristic 2. (Magma's twists don't always work over char 2.
#Adapted from Connell's Handbook of elliptic curves.
function quadratic_twist(E::EllCrv{T}, d) where T<: FieldElem

  a1, a2, a3, a4, a6 = a_invars(E)
  K = base_field(E)
  if characteristic(K) != 2 
    return EllipticCurve(K, [a1, a2*d + a1^2*(d-1)//4, a3, a4*d^2 + a1*a3*(d^2-1)//2, a6*d^3 + a3^2*(d^3 -1)//4])
  end
  
  return EllipticCurve(K, [a1, a2+a1^2*d, a3, a4, a6 + a3^2])

end


@doc Markdown.doc"""
    quadratic_twist(E::EllCrv{FinFieldElem}}) -> EllCrv{FinFieldElem}

Compute the unique quadratic twist of $E$.
"""
function quadratic_twist(E::EllCrv{T}) where T<: FieldElem

  K = base_field(E)
  char = characteristic(K)
 
 if char == 2
   f, h = hyperelliptic_polynomials(E)
   if iseven(degree(K))
     u = normal_basis(GF(Int(char), 1),K)
   else
     u = one(K)
   end
   
   return EllipticCurve(f + u*h^2, h)
 end 
  
  a = gen(K)
  return quadratic_twist(E, a)

end

#Test if we can't sometimes get two isomorphic curves
@doc Markdown.doc"""
    quadratic_twists(E::EllCrv{FinFieldElem}}) -> Vector{EllCrv{FinFieldElem}}

Compute all quadratic twists of $E$.
"""
function quadratic_twists(E::EllCrv{T}) where T<: FinFieldElem

  return [E, quadratic_twist(E)]

end

function supersingular_twists2(E::EllCrv{T}) where T<: FinFieldElem
#Adapted from Magma code
  K = base_field(E)
  if isodd(degree(K))
    return EllCrv{T}[EllipticCurve(K, [0, 0, 1, 0, 0]), EllipticCurve(K, [0, 0, 1, 1, 0]), EllipticCurve(K, [0, 0, 1, 1, 1]) ]
  end
    
  u = gen(K);
  c = u
  while absolute_tr(c) == 0 
    c = rand(K) 
  end
  #First three curves
  part_1 = EllCrv{T}[EllipticCurve(K, [0, 0, 1, 0, 0]), EllipticCurve(K, [0, 0, 1, c, 0]), EllipticCurve(K, [0, 0, 1, 0, c]) ]
  #The other four
  part_2 = EllCrv{T}[EllipticCurve(K, [0, 0, a, 0, a^2*b]) for (a, b) in [[u, 0], [inv(u), 0], [u, c], [inv(u), c]]]
  return vcat(part_1, part_2)
end


function supersingular_twists3(E::EllCrv{T}) where T<: FinFieldElem
#Adapted from Magma code
    K = base_field(E)
    d = degree(K)

    if mod(d, 3) != 0
        c = one(K)
    else
      c = gen(K)
      while absolute_tr(c) == 0
        c = rand(K)
      end
    end

    if isodd(d)
      return EllCrv{T}[EllipticCurve(K, [1,0]), EllipticCurve(K, [-1, 0]), EllipticCurve(K, [-1, c]), EllipticCurve(K, [-1, -c]) ];
    end
    u = gen(K);
    #First four curves
    part_1 = EllCrv{T}[EllipticCurve(K, [-u^i,0]) for i in (0:3)]
    part_2 = EllCrv{T}[EllipticCurve(K, [-1,c]), EllipticCurve(K, [-u^2,(u^3)*c])]
    return vcat(part_1, part_2) 

end

@doc Markdown.doc"""
    twists(E::EllCrv{FinFieldElem}}) -> Vector{EllCrv{FinFieldElem}}

Compute all twists of $E$.
"""
function twists(E::EllCrv{T}) where T<: FinFieldElem
#Adapted from Magma code
   K = base_field(E);
   p = characteristic(K)
   j = j_invariant(E)
   if j != 0 && j != 1728
      return EllCrv{T}[E, quadratic_twist(E)]
   elseif p == 2
      return supersingular_twists2(E)
   elseif p == 3 
      return supersingular_twists3(E)
   elseif j == 0
      a = gen(K)
      c4, c6 = c_invars(E)
      c = -c6//864
      n = gcd(6, order(K)-1)
      return EllCrv{T}[ EllipticCurve(K, [0,c*a^i]) for i in (0:n-1) ]
   elseif j == 1728 
      a = gen(K)
      c4, c6 = c_invars(E)
      c = -c4//48;
      n = gcd(4, order(K)-1)
      return EllCrv{T}[ EllipticCurve(K, [c*a^i,0]) for i in (0:n-1)]
   end
   #This can never happen:
   error("There is a bug in twists.")
end

@doc Markdown.doc"""
    is_twist(EEllCrv, EllCrv) -> Bool

Return true if $F$ is a twist of $E$
"""
function is_twist(E::EllCrv, F::EllCrv)

  return j_invariant(E) == j_invariant(F)
end



