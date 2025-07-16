function _primitive_element(a::Vector{QQBarFieldElem})
  pe = a[1]
  f = minpoly(Globals.Qx, pe)
  Qx = parent(f)
  local k, f
  for i = 2:length(a)
    g = minpoly(Globals.Qx, a[i])
    f = minpoly(Globals.Qx, pe)
    k, _ = number_field(f, check = false, cached = false)
    lf = collect(keys(factor(k, g).fac))
    for j = 1:length(lf)
      h = map_coefficients(x->Qx(x)(pe), lf[j])
      if is_zero(h(a[i]))
        d = degree(f) * degree(h)
        mu = 0
        while degree(minpoly(Globals.Qx, pe+mu*a[i])) != d
          mu += 1
          if mu > 10
            error("too bad")
          end
        end
        pe += mu*a[i]
      end
    end
  end
  return pe
end

function _map_to_common_number_field(a::Vector{QQBarFieldElem})
  res = Vector{SimpleNumFieldElem}(undef, length(a))
  if length(a) == 0
    return res
  end
  pe = _primitive_element(a)
  f = minpoly(Globals.Qx, pe)
  k, = number_field(f; cached = false, check = false )
  f = minpoly(Globals.Qx, pe)
  for i in 1:length(a)
    g = minpoly(Globals.Qx, a[i])
    rts = roots(k, g)
    for r in rts
      if evaluate(Globals.Qx(r), pe) == a[i]
        res[i] = r
        break
      end
    end
  end
  return res, pe
end

# TODO: use _qqbar_roots_poly_squarefree as soon as available in FLINT_jll

function factor(f::PolyRingElem{QQBarFieldElem})
  # the roots of f in Qbar are contained in the roots of norm(f) in Qbar
  @req !is_zero(f) "Polynomial must be non-zero"
  rts = roots(f)
  facts = [gen(parent(f)) - r for r in rts]
  fac = Fac(parent(f)(leading_coefficient(f)), Dict(facts[i] => valuation(f, facts[i]) for i in 1:length(facts)))
  @assert degree(f) == sum(e for (_,e) in fac)
  return fac
end

function roots(f::PolyRingElem{QQBarFieldElem})
  # the roots of f in Qbar are contained in the roots of norm(f) in Qbar
  @req !is_zero(f) "Polynomial must be non-zero"
  QQbar = base_ring(f)
  no_0 = 0
  while is_zero(coeff(f, no_0))
    no_0 += 1
  end
  f = shift_right(f, no_0)

  cfs, pe = _map_to_common_number_field(collect(coefficients(f)))
  K = parent(cfs[1])
  Kt, t = polynomial_ring(K; cached = false)
  fK = Kt(cfs)
  rts = unique!(roots(QQbar, norm(fK)::dense_poly_type(QQ)))
  if no_0 > 0
    push!(rts, zero(base_ring(f)))
  end
  if degree(K) == 1
    return rts
  end
  #the norm will have added spurious roots...
  rts = QQBarFieldElem[r for r in rts if is_zero(f(r))]
  return rts
end

@doc doc"""
    is_integral(a::QQBarFieldElem) -> Bool

Returns whether $a$ is integral, that is, whether the minimal polynomial of $a$
has integral coefficients.
"""
is_integral(a::QQBarFieldElem) = is_algebraic_integer(a)
