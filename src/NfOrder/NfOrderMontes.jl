export MType, zerotype, montes_initial, phi_expansion, valuationf, extend_valuation

type MType
  phi
  f
  m
  F
  z
  NewtonOp
  ResOp
end

valuation{T <: Integer}(x::fmpz, y::T) = valuation(x, ZZ(y))

function phi_expansion(f::fmpz_poly, phi::fmpz_poly)
  (lead(f) != 1) && (lead(phi) != 1) && error("must be monic")
  q,r = pseudodivrem(f,phi)
  arr = [r]

  while degree(q) >= degree(phi)
    q,r = pseudodivrem(q,phi)
    push!(arr,r)
  end
  q,r = pseudodivrem(q,phi)
  push!(arr,r)
  return arr
end

function valuationf(p::Int)
  function v(x::fmpz)
    return valuation(x,p)[1]
  end
  return v
end
    

function extend_valuation(v::Function)
  function vext(f::fmpz_poly)
    a = Array(Int, length(f))
    for i in 1:length(f)
      a[i] = v(coeff(f,i-1))
    end
    return minimum(a)
  end
  return vext
end



function montes_initial(f::fmpz_poly, p::Int)
  kx,x = PolynomialRing(ResidueRing(ZZ, p), "x")
  fac = factor(kx(f))

  res = Array(MType, length(fac))

  for i in 1:length(fac)
    phi = fac[i][1]

    F = NmodPolyRingResField(phi, :x)
    z = F(gen(parent(phi)))

    res[i] = MType(phi,degree(phi),degree(phi), F, z, 1, 1)
  end

  return res
end




function zerotype(f::nmod_poly)
end
