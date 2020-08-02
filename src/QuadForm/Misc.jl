# Return an element Delta, such that K_p(\sqrt{Delta}) is the unique quadratic unramified extension.

@doc Markdown.doc"""
    kummer_generator_of_local_unramified_quadratic_extension(p::Idl) -> NumFieldElem

Given a dyadic prime ideal $\mathfrak p$ of a number field $K$, return a local
unit $\Delta$, such that $K(\sqrt(\Delta))$ is unramified at $\mathfrak p$.
"""
function kummer_generator_of_local_unramified_quadratic_extension(p)
  @assert isdyadic(p)
  K = nf(order(p))
  k, h = ResidueField(order(p), p)
  kt, t = PolynomialRing(k, "t", cached = false)
  a = rand(k)
  f = t^2 - t + a
  while !isirreducible(f)
    a = rand(k)
    f = t^2 - t + a
  end
  Kt, t = PolynomialRing(K, "t", cached = false)
  g = t^2 - t + elem_in_nf(h\a)
  aa = elem_in_nf(h\a)
  gg = evaluate(g, inv(K(2)) * (t + 1))
  @assert iszero(coeff(gg, 1))
  D = -coeff(gg, 0) * 4
  @assert quadratic_defect(D, p) == valuation(4, p)
  DD = -4 * aa + 1
  @assert D == DD
  @assert quadratic_defect(DD, p) == valuation(4, p)
  return DD
end

# {Given a unit at the prime p, find a local unit v in the same square class such that v-1 generates the quadratic defect of u}

function _find_special_class(u, p)
  R = order(p)
  K = nf(R)
  @assert valuation(u, p) == 0
  k, _h = ResidueField(R, p)
  h = extend(_h, K) 
  fl, s = issquare(h(u))
  @assert fl
  u = divexact(u, (h\s)^2)
  @assert isone(h(u))
  e = valuation(2, p)
  pi = elem_in_nf(uniformizer(p))
  val = isone(u) ? inf : valuation(u - 1, p)
  while val < 2 * e 
    if isodd(val)
      return u
    end
    fl, s = issquare(h((u - 1)//pi^val))
    @assert fl 
    # TODO:FIXME the div is wrong for negative valuations I think
    @assert val >= 0
    u = divexact(u, (1 + (h\s) * pi^(div(val, 2)))^2)
    val = valuation(u - 1, p) 
  end
  kt, t = PolynomialRing(k, "t", cached = false)
  return val == 2 * e && isirreducible(kt([h(divexact(u - 1, 4)), one(k), one(k)])) ? u : one(K)
end


