###########################################################
##
## MAPS
##
## maps between residue rings of polynomials and in general
##
###########################################################


preimage_function(f) = a -> preimage(f, a)
image_function(f) = a -> image(f, a)


#function _compose(f, g)
#  return AbstractAlgebra.Generic.compose(g, f)
#end

#function compose(f::Map(HeckeMap){R, C}, g::Map(HeckeMap){D, R}) where {D, C, R}
#  return CompositeMap{D, C, R}(f, g)
#end


mutable struct InverseMap{D, C} <: Map{D, C, HeckeMap, InverseMap}
  header::MapHeader{D, C}
  origin::Map{C, D}

  function InverseMap{D, C}(f::Map{C, D}) where {D, C}
    z = new{D, C}()
    z.header = MapHeader(codomain(f), domain(f), preimage_function(f), image_function(f))
    z.origin = f
    return z
  end
end

function InverseMap(f::Map{C, D}) where {D, C}
  return InverseMap{D, C}(f)
end
