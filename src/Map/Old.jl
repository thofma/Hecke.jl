mutable struct ResidueRingPolyMap{D, C, T} <: Map{D, C, HeckeMap, ResidueRingPolyMap}
  header::MapHeader{D, C}
  gen_image::Generic.ResidueRingElem{T}
  coeff_map::Map # can be missing if domain and codomain have the same
                 # base_ring(base_ring())
  function ResidueRingPolyMap{D, C, T}(domain::D, codomain::C, gen_image::Generic.ResidueRingElem{T}, coeff_map::Map) where {D, C, T}
    z = new{D, C, T}()
    z.gen_image = gen_image
    z.coeff_map = coeff_map

    image = function(a::Generic.ResidueRingElem)
      #a should be in the domain of M...
      I = codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + z.coeff_map(coeff(a.data, i))
      end
      return I::elem_type(C)
    end

    # I need to call preimage in _preimage
    _preimage = function(a::Generic.ResidueRingElem)
      R = codomain
      parent(a) == R || error("mixed rings in preimage")
      g = gens(domain)
      im_gen = map(z, g) # apply x -> z(x) to the generatotrs ## possibly should be cached and stored
          ## need to write the elements in a matrix, solve the eqn for a
      Mt = zero_matrix(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))

      for i=1:degree(R.modulus)
        elem_to_mat_row!(Mt, i, im_gen[i])
      end
      b = zero_matrix(base_ring(base_ring(R)), 1, degree(R.modulus))
      elem_to_mat_row!(b, 1, a)
      s = solve_rational(Mt', b') # why, oh why is solve operating on columns????
      # This is the worst
      if isa(s, Tuple) ## again, why, oh why is solve doing things differently
                   ## over rings than fields?
        s = s[1] * inv(s[2]) # all rings here (type) are actually fields (math)
      end

      s = sum([preimage(z.coeff_map, s[i,1])*g[i] for i=1:length(g)])
      @assert parent(s) == domain
      return s::elem_type(domain)
    end

    z.header = MapHeader(domain, codomain, image, _preimage)
    return z
  end

  function ResidueRingPolyMap{D, C, T}(domain::D, codomain::C, gen_image::Generic.ResidueRingElem{T}) where {D, C, T}
    z = new{D, C, T}()
    z.gen_image = gen_image

    image = function(a::Generic.ResidueRingElem)
      I = z.codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + coeff(a.data, i)
      end
      return I::elem_type(C)
    end

    preimage = function(a::Generic.ResidueRingElem)
      R = z.codomain
      parent(a) == R || error("mixed rings in preimage")
      g = gens(domain)
      im_gen = map(x -> z(x), g) # apply x -> z(x) to the generatotrs ## possibly should be cached and stored
          ## need to write the elements in a matrix, solve the eqn for a
      Mt = zero_matrix(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))

      for i=1:degree(R.modulus)
        elem_to_mat_row!(Mt, i, im_gen[i])
      end
      b = zero_matrix(base_ring(base_ring(R)), 1, degree(R.modulus))
      elem_to_mat_row!(b, 1, a)
      s = solve_rational(Mt', b') # why, oh why is solve operating on columns????
      # This is the worst
      if isa(s, Tuple) ## again, why, oh why is solve doing things differently
                   ## over rings than fields?
        s = s[1] * inv(s[2]) # all rings here (type) are actually fields (math)
      end

      s = sum([s[i,1]*g[i] for i=1:length(g)])

      @assert parent(s) == domain
      return s::elem_type(domain)
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end
end

function ResidueRingPolyMap(domain::D, codomain::C, i::Generic.ResidueRingElem{T}) where {D, C, T}
  return ResidueRingPolyMap{D, C, T}(domain, codomain, i)
end

function ResidueRingPolyMap(domain::D, codomain::C, i::Generic.ResidueRingElem{T}, coeff_map::Map) where {D, C, T}
  return ResidueRingPolyMap{D, C, T}(domain, codomain, i, coeff_map)
end

mutable struct CoerceMap{D, C} <: Map{D, C, HeckeMap, CoerceMap}
  header::MapHeader{D, C}

  function CoerceMap{D, C}(domain::D, codomain::C) where {D, C}
    z = new{D, C}()
    z.header = MapHeader(domain, codomain)
    return z
  end

  function CoerceMap(domain::Generic.ResidueRing{S}, codomain::Generic.ResidueRing{T}) where {S, T <: PolyElem}
    z = new{Generic.ResidueRing{S}, Generic.ResidueRing{T}}()

    image = function(a::Generic.ResidueRingElem)
      return codomain(a)::elem_type(codomain)
    end

    preimage = function(a::Generic.ResidueRingElem)
      while parent(a) != domain
        degree(a.data)>0 && error("Element not in subfield")
        a = coeff(a.data, 0)
      end
      return a::elem_type(domain)
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end
end

function CoerceMap(domain::Generic.ResidueRing{ZZRingElem}, codomain::fqPolyRepField)
  z = CoerceMap{Generic.ResidueRing{ZZRingElem}, fqPolyRepField}()

  image = function(a::Generic.ResidueRingElem{ZZRingElem})
      parent(a) != domain && error("Element not in domain")
      return codomain(ZZRingElem(a))
  end

  preimage = function(a::fqPolyRepFieldElem)
    parent(a) != codomain && error("Element not in codomain")
    a.length > 1 && error("Element not in image")
    return domain(coeff(a, 0))::Generic.ResidueRingElem{ZZRingElem}
  end

  z.header = MapHeader(domain, codomain, image, preimage)
  return z
end

function CoerceMap(domain::fqPolyRepField, codomain::Generic.ResidueRing{fqPolyRepPolyRingElem})
  z = CoerceMap{fqPolyRepField, Generic.ResidueRing{fqPolyRepPolyRingElem}}()

  image = function(a::fqPolyRepFieldElem)
    parent(a) != domain && error("Element not in domain")
    return codomain(a)::Generic.ResidueRingElem{fqPolyRepPolyRingElem}
  end

  preimage = function(a::Generic.ResidueRingElem{fqPolyRepPolyRingElem})
    degree(a.data) > 0 && error("Element not in subfield")
    return domain(coeff(a.data, 0))::fqPolyRepFieldElem
  end

  z.header = MapHeader(domain, codomain, image, preimage)
  return z
end



function CoerceMap(domain::D, codomain::C) where {D, C}
  return CoerceMap{D, C}(domain, codomain)
end


