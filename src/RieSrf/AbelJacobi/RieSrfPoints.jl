@doc raw"""
    (RS::RiemannSurfaceModel)(coords::Vector{AcbFieldElem})

Return the point $P$ of $RS$ with coordinates specified by `coords`, which can
be either affine coordinates (`length(coords) == 2`) or projective coordinates
(`length(coords) == 3`).
"""
function (RS::RiemannSurfaceModel)(coords::Vector{AcbFieldElem})
  _ensure_special_points!(RS)
  f = complex_defining_polynomial(RS)
  CC = base_ring(parent(f))
  RR = ArbField(precision(CC))
  @req 2<=length(coords)<=3 "Points need to be given in either affine coordinates (x, y) or projective coordinates (x : y : z)"
  if length(coords) == 2
    x_coord = CC(coords[1])
    y_coord = CC(coords[2])
    v = abs(f(x_coord, y_coord))
    if contains(v, RR(0))
      for s in RS.finite_singularities
        if contains(x_coord, s[1]) && contains(y_coord, s[2]) && contains(CC(1), s[3])
          error("Singular point of defining polynomial. Not a point on the Riemann surface.")
        end
      end
      point = RiemannSurfacePoint(RS)
      point.coordx = coords[1]
      point.coordy = coords[2]
      point.is_singular = false
      point.homog_coords = [point.coordx, point.coordy, CC(1)]
      point.is_finite = true
      for s in ramification_points(RS)
        if contains(x_coord, s.coordx) && contains(y_coord, s.coordy)
          return s
        end
      end
      point.ramification_index = 1
      return point
    else
      error("Not a point on the Riemann surface.")
    end
  elseif length(coords) == 3
    homog_coords = [CC(coords[1]), CC(coords[2]), CC(coords[3])]
    if homog_coords[3] != CC(0)
      return RS([homog_coords[1]/homog_coords[3], homog_coords[2]/homog_coords[3]])
    else
      point = RiemannSurfacePoint(RS)
      point.is_finite = false
      point.homog_coords = homog_coords
      for s in RS.singular_points
        if contains(homog_coords, s)
          error("Singular point of projective closure. Not a point on the Riemann surface.")
        end
      end
      for s in RS.infinite_points
        if contains(homog_coords, s.homog_coords)
          return s
        end
      end
      error("Not on a point the Riemann surface.")
    end
  end
end

@doc raw"""
    is_finite(P::RiemannSurfacePoint)

Return true if the point is a finite point of the Riemann surface.
"""
function is_finite(P::RiemannSurfacePoint)
  return P.is_finite
end

function show(io::IO, P::RiemannSurfacePoint)
  CC = parent(P.coordx)
  infty = CC(1/0)
  CC = AcbField(30)
  if is_finite(P)
    if !P.is_singular
      print(io, "Point  ($(CC(P.homog_coords[1])) : $(CC(P.homog_coords[2])) : $(CC(P.homog_coords[3])))  of $(P.parent)")
    else
      print(io, "Point lying in the desingularization of singular point $(CC(P.coordx)), $(CC(P.coordy)) in sheets $(P.sheets) of $(P.parent)")
    end
  else
    if P.coordx == CC(1/0) && isdefined(P, :sheets)
      print(io, "Point at infinity on sheets $(P.sheets) of $(P.parent)")
    elseif P.is_singular
      print(io, "Point lying in the desingularization of singular point with x-coordinate $(CC(P.coordx)) in sheets $(P.sheets) of $(P.parent)")
    elseif P.coordy == CC(1/0)
      print(io,"Y-infinite point over x = $(CC(P.coordx)) on sheets $(P.sheets) of $(P.parent)")
    else
      error("Error in show function")
    end
  end
end

function ==(P::RiemannSurfacePoint, Q::RiemannSurfacePoint)
  RS = parent(P)
  prec = precision(RS)
  CC = AcbField(prec)
  RR = ArbField(prec)
  if RS != parent(Q)
    return false
  end

  if is_finite(P) && is_finite(Q)
    if !contains(abs(P.coordx - Q.coordx), RR(0))
      return false
    else
      if !P.is_singular && !Q.is_singular
        return  contains(abs(P.coordy - Q.coordy), RR(0))
      elseif isdefined(P, :sheets) && isdefined(Q, :sheets)
        return Set(P.sheets) == Set(Q.sheets)
      else
        return false
      end
    end
  end

  if !is_finite(P) && !is_finite(Q)
    if isdefined(P, :coordx) && isdefined(Q, :coordx)
      if P.coordx == CC(1/0) && Q.coordx == CC(1/0)
        return Set(P.sheets) == Set(Q.sheets)
      else
        if contains(abs(P.coordx - Q.coordx), RR(0))
          return Set(P.sheets) == Set(Q.sheets)
        end
      end
    else
      if isdefined(P, :homog_coords) && isdefined(Q, :homog_coords)
        @req P.homog_coords[3] == CC(0) "This should not happen. There is a bug in the code."
        @req Q.homog_coords[3] == CC(0) "This should not happen. There is a bug in the code."
        if P.homog_coords[1] != 0
          if Q.homog_coords[1] != 0
            return contains(abs(P.homog_coords[2]/P.homog_coords[1]-Q.homog_coords[2]/Q.homog_coords[1]), zero(RR))
          else
            return false
          end
        else
          return Q.homog_coords[1] == 0
        end
      end
    end
  end
  return false
end

function parent(P::RiemannSurfacePoint)
  return P.parent
end
