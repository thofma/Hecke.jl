function domain(M::Map)
  return M.header.domain
end

function codomain(M::Map)
  return M.header.codomain
end

function image_function(f::Map)
  return f.header.image
end

function preimage_function(f::Map)
  return f.header.preimage
end

#function image_func(M::Map)
#  return M.header.image
#end
#
#function preim_func(M::Map)
#  return M.header.preim
#end

function show(io::IO, M::Map)
  println(io, "Map $(domain(M)) -> $(codomain(M))")
end

function preimage{D, C}(M::Map{D, C}, a)
  if isdefined(M.header, :preimage)
    p = M.header.preimage(a)::elem_type(D)
    @assert parent(p) == domain(M)
    return p
  end
  error("No preimage function known")
end

elem_type(::Type{AnticNumberField}) = Hecke.nf_elem

elem_type(::Type{FqNmodFiniteField}) = Hecke.fq_nmod

elem_type{T}(::Type{ResidueRing{T}}) = Hecke.Residue{T}

function image{D, C}(M::Map{D, C}, a)
  if isdefined(M.header, :image)
    return M.header.image(a)::elem_type(C)
  else
    error("No image function known")
  end
end

function Base.call{D, C}(M::Map{D, C}, a)
  return image(M, a)
end

function show(io::IO, M::InverseMap)
  println(io, "inverse of")
  println(io, " ", M.a)
end

function inv(a::Map)
  return InverseMap(a)
end

function show(io::IO, M::CoerceMap)
  println(io, "Coerce: $(domain(M)) -> $(codomain(M))")
end
#######################################################

elem_type{T}(::Type{ResidueRing{T}}) = Residue{T}
