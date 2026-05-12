mutable struct RiemannSurfaceDivisor
  points::Vector{RiemannSurfacePoint}
  mults::Vector{Int}
  degree::Int
  abel_jacobi_value::AcbMatrix
  riemann_surface::RiemannSurface


  function RiemannSurfaceDivisor(RS::RiemannSurface) 
    D = new()
    D.RiemannSurface = RS
    D.degree = 0
    D.points = []
    D.mults = []
    return D
  end

  function RiemannSurfaceDivisor(S::Vector{RiemannSurfacePoint}, V::Vector{Int}) 
    D = new()
    number_of_points = length(S)
    @req number_of_points == length(V) "Length of the array of points should match the array of multiplicities."
    @req number_of_points >= 0 "Array of points should not be empty."

    D.riemann_surface = parent(S[1])

    D.degree = sum(V;init = 0)
    D.points = []
    D.mults = []
    for k in (1:number_of_points)
      if V[k] != 0
        i = findfirst(x -> x == S[k], D.points)
        if i == nothing
          push!(D.points, S[k])
          push!(D.mults,V[k])
        else
          D.mults[i]+=V[k]
        end
      end
    end
    return D
  end
end

function divisor(S::Vector{RiemannSurfacePoint}, V::Vector{Int}) 
  return RiemannSurfaceDivisor(S, V)
end

function zero_divisor(RS::RiemannSurface)
  D = RiemannSurfaceDivisor(RS)
  D.RiemannSurface = RS
  return D
end

function riemann_surface(D::RiemannSurfaceDivisor)
  return D.riemann_surface
end

function support(D::RiemannSurfaceDivisor)
  return D.points, D.mults
end

function degree(D::RiemannSurfaceDivisor)
  return D.degree
end

function ==(D1::RiemannSurfaceDivisor, D2::RiemannSurfaceDivisor)
  points1, mults1 = support(D1)
  points2, mults2 = support(D2)

  n = length(points1)
  if n != length(points2)
    return false
  end

  for k in (1:n)
    i = findfirst(x -> x == points2[k], points1)
    if i == nothing
      return false
    else
      if mults1[i] != mults2[k]
        return false
      end
    end
  end

  return true
end

function +(P1::RiemannSurfacePoint, P2::RiemannSurfacePoint)
  return RiemannSurfaceDivisor([P1,P2],[1,1])
end

function -(P1::RiemannSurfacePoint, P2::RiemannSurfacePoint)
  return RiemannSurfaceDivisor([P1,P2],[1,-1])
end

function +(D::RiemannSurfaceDivisor, P::RiemannSurfacePoint)
  return D + 1*P
end

function -(D::RiemannSurfaceDivisor, P::RiemannSurfacePoint)
  return D - 1*P
end

function +(D1::RiemannSurfaceDivisor, D2::RiemannSurfaceDivisor)
  @req riemann_surface(D1) == riemann_surface(D2) "Divisors have to be defined on the same Riemann surface."
  points1, mults1 = support(D1);
  points2, mults2 = support(D2);
  D = RiemannSurfaceDivisor(vcat(points1, points2), vcat(mults1, mults2))
  if isdefined(D1, :abel_jacobi_value) && isdefined(D2, :abel_jacobi_value)
    D.abel_jacobi_value = D1.abel_jacobi_value + D2.abel_jacobi_value
  end
  return D
end

function -(D1::RiemannSurfaceDivisor, D2::RiemannSurfaceDivisor)
  return D1 + (-1)*D2
end
function *(k::Int, P::RiemannSurfacePoint)
  return RiemannSurfaceDivisor([P],[k])
end

function *(k::Int, D::RiemannSurfaceDivisor)
  if k == 0 then
    return zero_divisor(RiemannSurface(D))
  end
  points, mults = support(D)
  kD = RiemannSurfaceDivisor(points, k*mults)
    if isdefined(D, :abel_jacobi_value)
      kD.abel_jacobi_value = k * D.abel_jacobi_value
    end
  return kD
end

function show(D::RiemannSurfaceDivisor)
  CC = AcbField(30)
  X = riemann_surface(D)
  points, mults = support(D)
  output = ""
  for k in (1:length(points))
    point = points[k]
    mult = mults[k]
    if sign(mult) == 1
      if k > 1
        output *= " + "
      end
    else
      if k > 1
        output *= " - "
      else
        S *= "-"
      end
    end

    abs_mult = abs(mult)
    if abs_mult != 1
      output *= "$(abs_mult)*"
    end
    if point.is_finite
      if !point.is_singular
        S *="($(CC(point.coordx))), $(CC(point.coordy))))"
      else
       S *="($(CC(point.coordx))), sheet $(point.sheets))"
      end
    else
      S *="($(CC(point.coordx))), sheet $(point.sheets))"
    end
  end
print(io, output)
end