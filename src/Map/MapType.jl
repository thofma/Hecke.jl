###########################################################
##
## MAPS
##
## maps between residue rings of polynomials and in general
##
###########################################################


# preimage_function(f) = a -> preimage(f, a)
# image_function(f) = a -> image(f, a)


#function _compose(f, g)
#  return AbstractAlgebra.Generic.compose(g, f)
#end

#function compose(f::Map(HeckeMap){R, C}, g::Map(HeckeMap){D, R}) where {D, C, R}
#  return CompositeMap{D, C, R}(f, g)
#end
