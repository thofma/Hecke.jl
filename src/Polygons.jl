import Base: length, GMP

export SortPoints, lowerconvexhull, newtonpolygon, Line, Polygon, PartialPolygon

mutable struct Line
  points :: Tuple{Tuple{fmpz, fmpz},Tuple{fmpz, fmpz}}
  slope :: fmpq
  
  function Line(points::Tuple{Tuple{fmpz, fmpz}, Tuple{fmpz, fmpz}})
    line = new()
    line.points = points
    line.slope = slope(points[1],points[2])
    return line
  end
  
  function Line(a::Tuple{fmpz,fmpz},b::Tuple{fmpz,fmpz})
    return Line([a,b])
  end
end

mutable struct Polygon
  lines :: Array{Line,1}
  slopes :: Array{fmpq ,1}

  function Polygon(lines::Array{Line,1}; sorted = false)
    polygon = new()
    if sorted
      polygon.lines = lines
    else
      for j = 1:length(lines)-1
        iMin = j
        for i = j+1:length(lines)
          if (lines[i]).points[1][1] < lines[iMin].points[1][1]
            iMin = i
          end
        end
        if iMin != j
          lines[j],lines[iMin] = lines[iMin],lines[j]
        end
      end
      polygon.lines = lines
    end
          
    polygon.slopes = Array{fmpq}(length(lines))

    for i in 1:length(lines)
      polygon.slopes[i] = lines[i].slope
    end
    return polygon
  end
end 


function length(L::Line)
  return L.points[2][1]-L.points[1][1]
end

function heigth(L::Line)
  return L.points[2][1]-L.points[1][1]
end


function sortpoints(x::Array{Tuple{fmpz,fmpz},1})
  for j = 1:length(x)-1
    iMin = j
    for i = j+1:length(x)
      if x[i][1] < x[iMin][1]
        iMin = i
      end
    end
    if iMin != j
      x[j],x[iMin] = x[iMin],x[j]
    end 
  end
  return x
end

function lowerconvexhull(points::Array{Tuple{fmpz, fmpz},1})

  points = sortpoints(points)

  # Take care of trivial case with 1 or 2 elements

  if length(points) == 1
    error("Lower convex hull of 1 point is not defined")
  elseif length(points) == 2
    return Line(points)
  end

  pointsonconvexhull = [ points[length(points)-1], points[length(points)] ]

  n = length(points)-2

  oldslope = slope(pointsonconvexhull[1],pointsonconvexhull[2])

  for i = 1:n
    newslope = slope(points[n-i+1], pointsonconvexhull[1])
    if newslope >= oldslope
      pointsonconvexhull[1] = points[n-i+1]
    else
      unshift!(pointsonconvexhull,points[n-i+1])
    end
    oldslope = newslope
  end

  t = Line[]
  for i=1:length(pointsonconvexhull)-1
    push!(t,Line((pointsonconvexhull[i], pointsonconvexhull[i+1])))
  end
  return Polygon(t)
end

function slope(L::Line)
  return slope(L.points[1], L.points[2])
end

function slope(a::Tuple{fmpz,fmpz},b::Tuple{fmpz,fmpz})
  return (b[2]-a[2])//(b[1]-a[1])
end

function phi_development(f::fmpz_poly, phi::fmpz_poly)
  dev=Array{fmpz_poly, 1}()
  g=f
  while degree(g)>=degree(phi)
    g, r = divrem(g, phi)
    push!(dev, r)
  end
  push!(dev, g)
  return dev
end

function valuation(f::fmpz_poly, p::fmpz)
  return minimum([valuation(coeff(f,i), p) for i= 0:degree(f)])
end


function newton_polygon(dev::Array{fmpz_poly, 1}, p::fmpz)
  a = Tuple{fmpz, fmpz}[]
  for i = 1:length(dev)
    push!(a, (i,valuation(dev[i],p)))
  end 
  return lowerconvexhull(a)
end

function newton_polygon(f::fmpz_poly, phi::fmpz_poly, p::fmpz)
  a = Tuple{fmpz, fmpz}[]
  if !(isprime(p))
    error("Not a prime")
  end
  #Compute the development
  dev=phi_development(f,phi)
  for i = 0:degree(f)
    if iszero(coeff(f,i))
      continue
    end
    push!(a, (i,valuation(dev[i+1],p)))
  end 
  return lowerconvexhull(a)
end

function degree(L::Line)
  return divexact(L.points[2][1]-L.points[1][1], denominator(L.slope))
end

function residual_polynomial(F::FqNmodFiniteField, L::Line, dev::Array{fmpz_poly, 1}, p::fmpz)

  cof=Array{fq_nmod,1}()
  R=ResidueRing(FlintZZ, p, cached=false)
  Rx,x=PolynomialRing(R,"y", cached=false)
  s=L.points[1][1]
  e=denominator(L.slope)
  for i=0:degree(L)
    if !iszero(dev[Int(s+e*i+1)])
      el=Rx(divexact(dev[Int(s+e*i+1)], p^(Int(L.points[1][2]-i))))
      push!(cof, F(el))
    end 
  end
  Fx, x=PolynomialRing(F,"x", cached=false)
  return Fx(cof)

end


# Remove all lines where the slop is <= t

function PartialPolygon(P::Polygon,t::Rational{BigInt})
  
  function tem(s::Line)
    if s.slope > t 
      return true
    end
    return false
  end

  m = findfirst(tem,P.lines)
  println(m)
  return true
end

function gens_overorder_polygons(O::NfOrd, p::fmpz)

  K=nf(O)
  f=K.pol
  els=nf_elem[]
  R=ResidueRing(FlintZZ, p, cached=false)
  Rx, y= PolynomialRing(R, "y", cached=false)
  f1=Rx(K.pol)
  fac=factor(f)
  for g in keys(fac)
    phi=lift(g)
    dev=phi_development(f,phi)
    N=newton_polygon(dev, p)
    F,a=FiniteField(phi, "a", cached=false)
    for L in N.lines
      h=residue_polynomial(F, L, dev, p)
      fac1=factor(h)
      #Now, we have to lift the factorization. Resultants?
    end
  end
  
end
  
