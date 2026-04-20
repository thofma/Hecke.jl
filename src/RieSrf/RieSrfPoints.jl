mutable struct RiemannSurfacePoint
  coordx::AcbFieldElem 
  coordy::AcbFieldElem 
  coordz::AcbFieldElem
  riemann_surface::RiemannSurface 
  is_finite::Bool
  is_singular::Bool

  function RiemannSurfacePoint(RS::RiemannSurface, coords::Vector{AcbFieldElem}) 
    f = complex_defining_polynomial(RS)
    if length(coord) == 2
        result = evaluate(f, [coords[1], coords[2]])
        if result < RS.weak_error
          P = new()
          P.x = coords[1]
          P.y = coords[2]
          P.z = one(RS.complex_field)
          P.riemann_surface = RS
          P.is_finite = true
        else
          error("Point is not on the curve")
        end
    end


  end

end
