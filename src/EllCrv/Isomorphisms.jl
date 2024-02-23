###############################################################################
#
#  Isomorphisms
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

###############################################################################
#
#  Isomorphisms
#
###############################################################################


mutable struct EllCrvIso{T} <: Map{EllipticCurve, EllipticCurve, HeckeMap, EllCrvIso} where T<:RingElem
  header::MapHeader{EllipticCurve{T}, EllipticCurve{T}}
  domain::EllipticCurve{T}
  codomain::EllipticCurve{T}
  data::Tuple{T, T, T, T}

  function EllCrvIso(E::EllipticCurve{T}, data::Vector{T}) where T <:RingElem
    f = new{T}()
    f.domain = E

    if length(data)!= 4
      throw(DomainError(T, "Array needs to have length 4"))
    end
    r, s, t, u = data[1], data[2], data[3], data[4]
    f.data = (r, s, t, u)
    a1, a2, a3, a4, a6 = a_invariants(E)

    a1new = divexact(a1 + 2*s, u)
    a2new = divexact(a2 - s*a1 + 3*r - s^2, u^2)
    a3new = divexact(a3 + r*a1 + 2*t, u^3)
    a4new = divexact(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t, u^4)
    a6new = divexact(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1, u^6)

    F = elliptic_curve([a1new, a2new, a3new, a4new, a6new])
    f.codomain = F
    f.header = MapHeader(E, F)
    return f
  end

end

@doc raw"""
    identity_map(E::EllipticCurve) -> EllCrvIso

Return the identity isomorphism on the elliptic curve $E$.
"""
function identity_map(E::EllipticCurve)
  return isomorphism(E, [0, 0, 0, 1])
end

@doc raw"""
    negation_map(E::EllipticCurve) -> EllCrvIso

Return the negation isomorphism on the elliptic curve $E$.
"""
function negation_map(E::EllipticCurve)
  a1, a2, a3, a4, a6 = a_invariants(E)
  return isomorphism(E, [0, -a1, -a3, -1])
end

@doc raw"""
    isomorphism_data(f::EllCrvIso) -> (T, T, T, T)

Return the tuple $(r, s, t, u)$ that defines the isomorphism which is of the form
[x : y : 1] -> [(x - r)//u^2 : (y - s*(x-r) - t)//u^3 : 1]
"""
function isomorphism_data(f::EllCrvIso)
  return f.data
end

@doc raw"""
    inv(f::EllCrvIso) -> EllCrvIso
Return the inverse of the isomorphism $f$.
"""
function inv(f::EllCrvIso{T}) where T<:RingElem
  r, s, t, u = isomorphism_data(f)
  newr = -r//u^2
  news = -s//u
  newt = (r*s-t)//u^3
  newu = 1//u

  g = EllCrvIso(codomain(f),[newr, news, newt, newu])
  return g
end

@doc raw"""
    isomorphism_to_isogeny(f::EllCrvIso) -> Isogeny
Return the isomorphism $f$ as an isogeny.
"""
function isomorphism_to_isogeny(f::EllCrvIso)
  r, s, t, u = f.data
  E = f.domain
  phi = Isogeny(E)
  phi.codomain = f.codomain
  phi.degree = 1

  R = base_field(E)
  Rx, x = polynomial_ring(R, "x")
  phi.psi = one(Rx)


  phi.coordx = (x - r)//Rx(u^2)
  Rxy, y = polynomial_ring(Rx, "y")
  phi.coordy = (y - s*(x-r) - t)//Rxy(u^3)
  phi.header = f.header
  return phi
end


function compose(f::Isogeny, g::EllCrvIso)
  return compose(f, isomorphism_to_isogeny(g))
end

function compose(g::EllCrvIso, f::Isogeny)
  return compose(isomorphism_to_isogeny(g), f)
end


#Following Connell's Handbook for Elliptic Curves Chapter 4.4
@doc raw"""
    is_isomorphic(E1::EllipticCurve, E2::EllipticCurve) -> Bool
Return true when $E1$ and $E2$ are isomorphic
"""
function is_isomorphic(E1::EllipticCurve{T}, E2::EllipticCurve{T}) where T
  K = base_field(E1)
  char = characteristic(K)
  j1 = j_invariant(E1)
  j2 = j_invariant(E2)

  #First check the j-invariants
  if j1 != j2
    return false
  end

  if char == 2
    E1, phi1 = simplified_model(E1)
    E2, phi2 = simplified_model(E2)
    a1, a2, a3, a4, a6 = a_invariants(E1)
    _a1, _a2, _a3, _a4, _a6 = a_invariants(E2)
    Rx, x = polynomial_ring(K, "x")
    # j-invariant non-zero
    if j1!=0
      f = x^2 + x + a2 + _a2
      return !isempty(roots(f))
    end
    # j-invariant is 0
    us = roots(x^3 - a3//_a3)
    for u in us
      g = x^4 + a3*x + a4 + u^4*_a4
      ss = roots(g)
      for s in ss
        h = x^2 + a3*x + s^6 + a4*s^2 + a6 + u^6*_a6
        ts = roots(h)
        if !isempty(ts)
          return true
        end
      end
    end
    return false
  end

  if char == 3 && j1 == 0
    E1, phi1 = simplified_model(E1)
    E2, phi2 = simplified_model(E2)
    a1, a2, a3, a4, a6 = a_invariants(E1)
    _a1, _a2, _a3, _a4, _a6 = a_invariants(E2)
    Rx, x = polynomial_ring(K, "x", cached = false)
    us = roots(x^4 - a4//_a4)
    for u in us
      g = x^3 + a4*x + a6 - u^6*_a6
      rs = roots(g)
      if !isempty(rs)
        return true
      end
    end
    return false
  end

  c4, c6 = c_invariants(E1)
  _c4, _c6 = c_invariants(E2)


  if j1!=0 && j1!=1728
    return is_square(c6//_c6)
  else
    Rx, x = polynomial_ring(K, "x")
    if j1 == 1728
      us = roots(x^4 - c4//_c4)
      return !isempty(us)
    end
    if j1 == 0
      us = roots(x^6 - c6//_c6)
      return !isempty(us)
    end
  end
  error("There is a bug in is_isomorphism")
end


#Following Connell's Handbook for Elliptic Curves Chapter 4.4
@doc raw"""
    isomorphism(E1::EllipticCurve, E2::EllipticCurve) -> EllCrvIso
Return an isomorphism between $E1$ and $E2$ if they are isomorphic.
Otherwise return an error.
"""
function isomorphism(E1::EllipticCurve, E2::EllipticCurve)
  K = base_field(E1)
  char = characteristic(K)
  j1 = j_invariant(E1)
  j2 = j_invariant(E2)

  #First check the j-invariants
  j1 == j2 || error("Curves are not isomorphic")

  E1s, pre_iso = simplified_model(E1)
  E2s, _, post_iso = simplified_model(E2)
  a1, a2, a3, a4, a6 = a_invariants(E1s)
  _a1, _a2, _a3, _a4, _a6 = a_invariants(E2s)


  if char == 2
    Rx, x = polynomial_ring(K, "x")
    # j-invariant non-zero
    if j1!=0
      f = x^2 + x + a2 + _a2
      ss = roots(f)
      !isempty(ss) || error("Curves are not isomorphic")

      s = ss[1]
      phi = isomorphism(E1s, [0, s, 0, 1])
      F = codomain(phi)
      @assert F == E2s "There is a bug in isomorphism"
      return pre_iso*phi * post_iso
    end
    # j-invariant is 0
    us = roots(x^3 - a3//_a3)
    for u in us
      g = x^4 + a3*x + a4 + u^4*_a4
      ss = roots(g)
      for s in ss
        h = x^2 + a3*x + s^6 + a4*s^2 + a6 + u^6*_a6
        ts = roots(h)
        !isempty(ts) || error("Curves are not isomorphic")

        t = ts[1]
        phi = isomorphism(E1s, [s^2, s, t, u])
        F = codomain(phi)
        @assert F == E2s "There is a bug in isomorphism"
        return pre_iso * phi * post_iso
      end
    end
  end

  if char == 3 && j1 == 0
    Rx, x = polynomial_ring(K, "x")
    us = roots(x^4 - a4//_a4)
    for u in us
      g = x^3 + a4*x + a6 - u^6*_a6
      rs = roots(g)
      !isempty(rs) || error("Curves are not isomorphic")

      r = rs[1]
      phi = isomorphism(E1s, [r, 0, 0, u])
      F = codomain(phi)
      @assert F == E2s "There is a bug in isomorphism"
      return pre_iso * phi * post_iso
    end
  end

  c4, c6 = c_invariants(E1)
  _c4, _c6 = c_invariants(E2)

  if j1 == 0 #Then c4 and _c4 are equal to 0
    Rx, x = polynomial_ring(K, "x")
    us = roots(x^6 - c6//_c6)
    !isempty(us) || error("Curves are not isomorphic")
    u = us[1]
    phi = isomorphism(E1s, [0, 0, 0, u])
    F = codomain(phi)
    @assert F == E2s "There is a bug in isomorphism"
    return pre_iso * phi * post_iso
  end

  if j1 == 1728 #Then c6 and _c6 are equal to 0
    Rx, x = polynomial_ring(K, "x")
    us = roots(x^4 - c4//_c4)
    !isempty(us) || error("Curves are not isomorphic")
    u = us[1]
    phi = isomorphism(E1s, [0, 0, 0, u])
    F = codomain(phi)
    @assert F == E2s "There is a bug in isomorphism"
    return pre_iso * phi * post_iso
  end

  #Characteristic != 2 and j!= 0, 1728
  c4, c6 = c_invariants(E1)
  _c4, _c6 = c_invariants(E2)
  usq = (c6//_c6)//(c4//_c4)

  is_square(usq) || error("Curves are not isomorphic")
  u = sqrt(usq)
  phi = isomorphism(E1s, [0, 0, 0, u])
  F = codomain(phi)
  @assert F == E2s "There is a bug in isomorphism"
  return pre_iso * phi * post_iso
end
#=
function isomorphism(E::EllipticCurve, E2::EllipticCurve)
  char = characteristic(base_field(E))
  if char!= 2 && char!= 3
    if is_isomorphic(E, E2)
      a1, a2, a3 = a_invariants(E)
      _a1, _a2, _a3 = a_invariants(E2)

      c4, c6 = c_invariants(E)
      _c4, _c6 = c_invariants(E2)
      usq = (c6//_c6)//(c4//_c4)

      u = sqrt(usq)
      s = (_a1*u-a1)//2
      r = (_a2*u^2-a2+s*a1+s^2)//3
      t = (_a3*u^3-a3-r*a1)//2
      return isomorphism(E,[r,s,t,u])
    else
      throw(DomainError(E, "Curves are not isomorphic over the base field"))
    end
  else
    throw(DomainError(E, "Isomorphism test only implemented for characteristic not equal to 2 or 3"))
  end
end
=#

################################################################################
#
# T(r, s, t, u) transformation
#
################################################################################

# transformation T(r,s,t,u) as in Connell's handbook
@doc raw"""
    transform_rstu(E::EllipticCurve, [r, s, t, u]::Vector{T})
    -> EllipticCurve, EllCrvIso, EllCrvIso
Return the transformation of E under the isomorphism given by
[(x - r)//u^2 : (y - s*(x-r) - t)//u^3 : 1], the isomorphism and the inverse of
the isomorphism
"""
function transform_rstu(E::EllipticCurve, T::Vector{S}) where S

  phi = isomorphism(E, T)

  return codomain(phi), phi, inv(phi)
end


@doc raw"""
    isomorphism(E::EllipticCurve, [r, s, t, u]::Vector{T}) -> EllCrvIso
Return the isomorphism with domain E given by
[(x - r)//u^2 : (y - s*(x-r) - t)//u^3 : 1]. The codomain
is calculated automatically.
"""
function isomorphism(E::EllipticCurve{T}, isodata::Vector{T}) where T

  if length(isodata)!= 4
    throw(DomainError(data, "Array needs to have length 4"))
  end
  return EllCrvIso(E, isodata)
end

function isomorphism(E::EllipticCurve, data::Vector)

  if length(data)!= 4
    throw(DomainError(data, "Array needs to have length 4"))
   end

  K = base_field(E)
  isodata = map(K, data)
  return EllCrvIso(E, isodata)
end

function degree(f::EllCrvIso)
  return 1
end

@doc raw"""
    image(f::EllCrvIso, P::EllipticCurvePoint) -> EllipticCurvePoint
Return the image of $P$ under the isomorphism $f$.
"""
function image(f::EllCrvIso, P::EllipticCurvePoint)
  @assert domain(f) == parent(P)
  F = codomain(f)
  if !is_finite(P)
    return infinity(F)
  end
  r, s, t, u = isomorphism_data(f)
  xnew = divexact(1, u^2)*(P.coordx - r)
  ynew = divexact(1, u^3)*(P.coordy - s*u^2*xnew - t)
  Q = F([xnew, ynew])
  return Q
end

@doc raw"""
    preimage(f::EllCrvIso, P::EllipticCurvePoint) -> EllipticCurvePoint
Return the preimage of $P$ under the isomorphism $f$.
"""
function preimage(f::EllCrvIso, P::EllipticCurvePoint)
  @assert codomain(f) == parent(P)
  E = domain(f)
  if !is_finite(P)
    return infinity(E)
  end
  r, s, t, u = isomorphism_data(f)
  xnew = u^2*P.coordx + r
  ynew = u^3*P.coordy + s*u^2*P.coordx + t
  Q = E([xnew, ynew])
  return Q
end

function compose(f::EllCrvIso, g::EllCrvIso)
  @req codomain(f) == domain(g) "Codomain and domain must be identitcal"
  r1, s1, t1, u1 = f.data
  r2, s2, t2, u2 = g.data

  r3 = r1 + u1^2*r2
  s3 = s1 + u1*s2
  t3 = t1 + u1^2*s1*r2 + u1^3*t2
  u3 = u1*u2

  return isomorphism(domain(f), [r3, s3, t3, u3])

end

@doc raw"""
    automorphism_group_generators(E::EllipticCurve) -> Vector{EllCrvIso}
Return generators of the automorphism group of $E$.
"""
function automorphism_group_generators(E::EllipticCurve{T}) where {T}
  K = base_field(E)
  char = characteristic(K)
  j = j_invariant(E)

  if j!= 0 && j!=1728
    return [negation_map(E)]
  end

  Kx, x = polynomial_ring(K, cached = false)
  Es, pre_iso, post_iso = simplified_model(E)
  a1, a2, a3, a4, a6 = a_invariants(Es)

  if char != 2 && char != 3
    if j == 1728
      f = x^2+1
      a = roots(f)
      if !isempty(roots(f))
        #Group is Z/4Z
        i = a[1]
        return [pre_iso * isomorphism(Es, [0, 0, 0, i]) * post_iso]
      end
    elseif j == 0
      f = x^2+x+1
      a = roots(f)
      if !isempty(roots(f))
        #Group is Z/6Z
        zeta3 = a[1]
        return [pre_iso * isomorphism(Es, [0, 0, 0, -zeta3]) * post_iso]
      end
    end
    #Group is Z/2Z
    return [negation_map(E)]
  end

  if char == 3 #And j-invariant is 0.
    us = roots(x^2 + 1)  #See if x^4 + 1 = (x^2 +1)*(x^2 -1) has a root that induces an element of order 4
    rs = roots(x^2 +a4)

    test = !isempty(us)

    if test
      r2s = roots(x^3 + a4*x + 2*a6)
      i = us[1]
      test = !isempty(r2s)
    end

    if test && !isempty(rs)
      # Group is dicyclic group of order 12. <a, b | a^6 = b^4 = id, a^3 = b^2, bab^(-1) = a^(-1)>
      m = something(findfirst(!iszero, r2s))
      r = r2s[m]
      return [pre_iso * isomorphism(Es, [r, 0, 0, -1]) * post_iso, pre_iso * isomorphism(Es, [r, 0, 0, i]) * post_iso]
    elseif test
      #Group is Z/4Z
      r = r2s[1]
      return [pre_iso * isomorphism(Es, [r, 0, 0, i]) * post_iso]
    elseif !isempty(rs)
      #Group is Z/6Z
      r = rs[1]
      return [pre_iso * isomorphism(Es, [r, 0, 0, -1]) * post_iso]
    end
    #Group is Z/2Z
    return [negation_map(E)]
  end

  if char == 2 #And j-invariant is 0
    auts = EllCrvIso{T}[]
    us = roots(x^2 + x +1) #Check if there are us other than u = 1.
    if !isempty(us)
      u = us[1]
      g = x^4 + a3*x + (1+u)*a4
      ss = roots(g)
      for s in ss
        h = x^2 + a3*x + s^6 + a4*s^2
        ts = roots(h)
        for t in ts
          push!(auts, pre_iso * isomorphism(Es, [s^2, s, t, u]) * post_iso)
        end
      end
    end
    size = length(auts)

    if size == 8 #Group is SL(2,3)
      #Search for generators. One element of order 3 and one element of order 4 should suffice.
      #Element of order 3
      for phi in auts
        phi3 = phi * phi * phi
        if phi3 == identity_map(Es)
          g1 = phi
        end
      end
      #Element of order 4. Need to take u = 1.
      g = x^3 + a3
      s = roots(g)[1]
      h = x^2 + a3*x + s^6 + a4*s^2
      t = roots(h)[1]

      g2 = pre_iso * isomorphism(Es, [s^2, s, t, 1]) * post_iso

      return [g1, g2]
    elseif size == 2 #Group is Z/6Z
      g1 = auts[1]
      g2 = auts[2]
      if (g1 * g1 * g1) != identity_map(Es)
        return [g1]
      else
        return [g2]
      end
    end
    #u = 1
    auts = EllCrvIso{T}[]
    g = x^3 + a3
    ss = roots(g)

    for s in ss
      h = x^2 + a3*x + s^6 + a4*s^2
      ts = roots(h)
      for t in ts
        push!(auts, pre_iso * isomorphism(Es, [s^2, s, t, 1]) * post_iso)
      end
    end
    size = length(auts)

    if size == 6 #Group isomorphic to Quaternions
      if auts[1] == inv(auts[2])
        return [auts[1], auts[3]]
      else
        return [auts[1], auts[2]]
      end
    elseif size == 2 # Group isomorphic to Z/4Z
      return [auts[1]]
    end

  #Group is Z/2Z
  return [negation_map(E)]
  end
end

@doc raw"""
    rational_maps(f::EllCrvIso) -> Vector{Poly}
Return the rational maps defining the isomorphism.
"""
function rational_maps(f::EllCrvIso)
  K = base_field(domain(f))
  Kxy, (x, y) = polynomial_ring(K, ["x","y"])
  #Kxy, y = polynomial_ring(Kx, "y")
  r, s, t, u = f.data
  xnew = divexact(1, u^2)*(x - r)
  ynew = divexact(1, u^3)*(y - s*u^2*xnew - t)
  return [xnew, ynew, Kxy(1)]
end

function Base.getindex(f::EllCrvIso, i::Int)
  @req 1 <= i <= 3 "Index must be 1, 2 or 3"

  return rational_maps(f)[i]
end

@doc raw"""
    ==(f::EllCrvIso, g::EllCrvIso) -> Bool

Return true if $f$ and $g$ define the same map over the same field.
"""
function ==(f::EllCrvIso, g::EllCrvIso)
  Ef = domain(f)
  Eg = domain(g)
  return f.data == g.data && Ef == Eg && base_field(Ef) == base_field(Eg)
end


################################################################################
#
#  Show
#
################################################################################


function show(io::IO, f::EllCrvIso)
  E1 = domain(f)
  E2 = codomain(f)
  fx, fy, fz = rational_maps(f)
  print(io, "Isomorphism from
  $(E1) to \n
  $(E2) given by \n
  (x : y : 1) -> ($(fx) : $(fy) : $(fz) )")
end

################################################################################
#
#  Automorphism group
#
################################################################################

# Need a parent object for the morphisms
struct EllCrvIsoSet{T}
  crv::T
end

parent(f::EllCrvIso{T}) where {T} = EllCrvIsoSet{EllipticCurve{T}}(domain(f))

mutable struct EllCrvAutMap{S, T} <: Map{MultTableGroup, EllCrvIsoSet{T}, HeckeMap, EllCrvAutMap}
  G::MultTableGroup
  auts::Vector{T}
  header::MapHeader{MultTableGroup, EllCrvIsoSet{S}}

  function EllCrvAutMap(E::S, G::MultTableGroup, auts::Vector{T}) where {S, T}
    return new{S, T}(G, auts, MapHeader(G, EllCrvIsoSet{S}(E)))
  end
end

function image(f::EllCrvAutMap, g::MultTableGroupElem)
  return f.auts[g[]]
end

function preimage(f::EllCrvAutMap, m::EllCrvIso)
  @req parent(m) == codomain(f) "Isomorphism has wrong elliptic curve"
  for g in domain(f)
    if f(g) == m
      return g
    end
  end
  error("This should not happen")
end

function automorphism_group(E::EllipticCurve)
  gens = automorphism_group_generators(E)
  cl = closure(gens, *)
  G, Gtocl, cltoG = generic_group(cl, *)
  m = EllCrvAutMap(E, G, cl)
  return domain(m), m
end

function automorphism_list(E::EllipticCurve)
  gens = automorphism_group_generators(E)
  cl = closure(gens, *)
  return cl
end
