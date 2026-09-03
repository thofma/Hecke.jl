#function image_func(M::Map)
#  return M.header.image
#end
#
#function preim_func(M::Map)
#  return M.header.preim
#end


function show(io::IO, M::InverseMap)
  @show_name(io, M)
  println(io, "inverse of")
  print(io, " ", M.origin)
end

function pseudo_inv(a::Map)
  return InverseMap(a)
end

#function show(io::IO, M::CoerceMap)
#  println(io, "Coerce: $(domain(M)) -> $(codomain(M))")
#end


##

function extend_domain_to_fraction_field(phi::Map{<:MPolyRing, <:Ring})
  ext_dom = fraction_field(domain(phi))
  return map_from_func(ext_dom, codomain(phi), x->phi(numerator(x))*inv(phi(denominator(x))))
end
