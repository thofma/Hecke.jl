################################################################################
#
#   Roots
#
################################################################################

function roots(f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(f)
  e = absolute_ramification_index(K)
  k, mk = ResidueField(K)
  fk = map_coefficients(mk, f)
  #TODO: We don't need a full Hensel factorization.
  lH = Hensel_factorization(f)
  rt = elem_type(K)[]
  Kx = parent(f)
  for (phi, g) in lH
    if isone(degree(phi))
      if isone(degree(g))
        push!(rt, -constant_coefficient(g)//leading_coefficient(g))
      else
        #TODO: We don't need a full slope factorization.
        lS = slope_factorization(g)
        for (h, mh) in lS
          if isone(degree(h))
            r = -constant_coefficient(h)//leading_coefficient(h)
            for j = 1:mh
              push!(rt, r)
            end
          elseif divides(numerator(e*valuation(constant_coefficient(h))), degree(h))[1]
            rth = _roots(h)
            for j = 1:mh
              append!(rt, rth)
            end
          end
        end
      end
    end
  end
  #the roots need to be refined.
  #rt = refine_roots(f, rt)
  return rt
end

function refine_roots(f::Generic.Poly{T}, rt::Vector{T}) where T <: Union{padic, qadic, LocalFieldElem}
  Rx = parent(f)
  x = gen(Rx)
  factors = typeof(f)[x-y for y in rt]
  push!(factors, divexact(f, prod(factors)))
  factors = lift_factorization(f, factors)
  res = Vector{T}(undef, length(rt))
  for i = 1:length(rt)
    res[i] = -constant_coefficient(factors[i])
  end
  return res
end


function refine_roots1(f::Generic.Poly{T}, rt::Vector{T}) where T <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(f)
  v = numerator(absolute_ramification_index(K)*valuation(reduced_discriminant(f)))
  target_prec = precision(f)
  starting = minimum(Int[precision(x) for x in rt])  
  chain = [target_prec]
  i = target_prec
  while i > starting
    i = div(i+1, 2)
    pushfirst!(chain, i)
  end
  der = derivative(f)
  wvect = [inv(der(rt[i])) for i = 1:length(rt)]
  rtnew = copy(rt)
  for i in 1:length(chain)
    for j = 1:length(rtnew)
      wvect[j]*f(rtnew[j])
      rtnew[j] = rtnew[j] - wvect[j]*f(rtnew[j])
      wvect[j] = wvect[j]*(2-wvect[j]*der(rtnew[j]))
    end
  end
  return rtnew
end


function _roots(f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(f)
  k, mk = ResidueField(K)
  fk = map_coefficients(mk, f)
  rts = roots(fk)
  x = gen(parent(f))
  #TODO: Is this setprecision call ok?
  r = setprecision(lift(rts[1], K), precision(f))
  pi = uniformizer(K)
  g = f(pi*x+r)
  g = divexact(g, _content(g))
  rtg = roots(g)
  rts = elem_type(K)[setprecision(r, precision(y)) + pi*y for y in rtg]
  return rts
end