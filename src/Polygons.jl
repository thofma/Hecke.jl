import Base: length, GMP

export SortPoints, lowerconvexhull, newtonpolygon, Line, Polygon, PartialPolygon

#using Nemo.Fields

type Line
  points :: Array{Tuple{fmpq, fmpq},1}
  slope :: fmpq

  function Line(points::Array{Tuple{fmpq, fmpq},1})
    line = new()
    line.points = points
    line.slope = slope(points[1],points[2])
    return line
  end
  
  function Line(a::Tuple{fmpq,fmpq},b::Tuple{fmpq,fmpq})
    return Line([a,b])
  end
end

type Polygon
  lines :: Array{Line,1}
  slopes :: Array{fmpq ,1}

  function Polygon(lines::Array{Line,1}; sorted = false)
    polygon = new()
    if sorted
      polyon.lines = lines
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


function sortpoints(x::Array{Tuple{fmpq,fmpq},1})
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

function lowerconvexhull(points::Array{Tuple{fmpq, fmpq},1})

  points = sortpoints(points)

  # Take care of trivial case with 1 or 2 elements

  if length(points) == 1
    println("ups")
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
    push!(t,Line(pointsonconvexhull[i],pointsonconvexhull[i+1]))
  end
  return Polygon(t)
end

function slope(a::Tuple{fmpq,fmpq},b::Tuple{fmpq,fmpq})
  return (b[2]-a[2])//(b[1]-a[1])
end

function newtonpolygon(f::Union(fmpz_poly,fmpq_poly),p::fmpz)
  a = Array{Tuple{fmpq, fmpq}}(degree(f)+1)
  if !(isprime(p))
    #throw some error
  end
  for i = 0:degree(f)
    iszero(coeff(f,i)) ? continue : a[i+1] = (i,valuation(coeff(f,i),p)[1])
  end 
  return lowerconvexhull(a)
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
  

function valuation(m::BigInt,p::BigInt)

  a = mod(m,p)
  i=ZZ(0)
  while a == 0
    i = i+1
    m = div(m,p)
    a = mod(m,p)
  end
  return i
end
