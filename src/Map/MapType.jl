###########################################################
## 
## MAPS
##
## maps between residue rings of polynomials and in general
##
###########################################################

export Map, CoerceMap, ResidueRingPolyMap

type MapHeader{D, C}
  domain::D
  codomain::C
  image::Function
  preimage::Function

  function MapHeader(domain::D, codomain::C)
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    return z
  end

  function MapHeader(domain::D, codomain::C, image::Function)
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    z.image = image
    return z
  end

  function MapHeader(domain::D, codomain::C, image::Function, preimage::Function)
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    z.image = image
    z.preimage = preimage
    return z
  end
end

function MapHeader{D, C}(domain::D, codomain::C, image::Function)
  return MapHeader{D, C}(domain, codomain, image)
end

function MapHeader{D, C}(domain::D, codomain::C, image::Function, preimage::Function)
  return MapHeader{D, C}(domain, codomain, image, preimage)
end
# this type represents a -> f(g(a))
type CompositeMap{D, C, R} <: Map{D, C}
  header::MapHeader{D, C}
  f::Map{R, C}
  g::Map{D, R}

  function CompositeMap(f::Map{R, C}, g::Map{D, R})
    codomain(f) == domain(g) || throw("maps not compatible")
    z = new{D, C, R}()
    z.domain = domain(g)
    z.codomain = codomain(f)

    image = function(x::elem_type(domain(z)))
      parent(x) != domain(z) && error("Element not in domain of map")
      return f(g(x))::elem_type(codomain(z))
    end

    if isdefined(f, :preimage) && isdefined(g, :preimage)
      preimage = function(x::elem_type(codomain(z)))
        return codomain(g, codomain(f, x))::elem_type(domain(z))
      end
      z.header = MapHeader(domain(g), codomain(f), image, preimage)
    else
      z.header = MapHeader(domain(g), codomain(f), image)
    end

    return z
  end
end

type InverseMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}
  origin::Map{C, D}

  function InverseMap(f::Map{C, D})
    z = new{D, C}()
    z.header = MapHeader(codomain(f), domain(g), preimage_function(f), image_function(f))
    return z
  end
end

type ResidueRingPolyMap{D, C, T} <: Map{D, C}
  header::MapHeader{D, C}
  gen_image::Residue{T}
  coeff_map::Map # can be missing if domain and codomain have the same
                 # base_ring(base_ring())
  function ResidueRingPolyMap(domain::D, codomain::C, gen_image::Residue{T}, coeff_map::Map)
    z = new{D, C, T}()
    z.gen_image = gen_image
    z.coeff_map = coeff_map

    image = function(a::Residue)
      #a should be in the domain of M...
      I = codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + z.coeff_map(coeff(a.data, i))
      end
      return I::elem_type(C)
    end
    
    # I need to call preimage in _preimage
    _preimage = function(a::Residue{T})
      R = codomain
      parent(a) == R || throw("mixed rings in preimage")
      g = gens(domain)
      im_gen = map(z, g) # apply x -> z(x) to the generatotrs ## possibly should be cached and stored
          ## need to write the elements in a matrix, solve the eqn for a
      Mt = MatrixSpace(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))()

      for i=1:degree(R.modulus)
        elem_to_mat_row!(Mt, i, im_gen[i])
      end
      b = MatrixSpace(base_ring(base_ring(R)), 1, degree(R.modulus))()
      elem_to_mat_row!(b, 1, a)
      s = solve(Mt', b') # why, oh why is solve operating on columns????
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

  function ResidueRingPolyMap(domain::D, codomain::C, gen_image::Residue{T})
    z = new{D, C, T}()
    z.gen_image = gen_image

    image = function(a::Residue)
      I = z.codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + coeff(a.data, i)
      end
      return I::elem_type(C)
    end

    preimage = function(a::Residue{T})
      R = z.codomain
      parent(a) == R || throw("mixed rings in preimage")
      g = gens(domain)
      im_gen = map(x -> z(x), g) # apply x -> z(x) to the generatotrs ## possibly should be cached and stored
          ## need to write the elements in a matrix, solve the eqn for a
      Mt = MatrixSpace(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))()

      for i=1:degree(R.modulus)
        elem_to_mat_row!(Mt, i, im_gen[i])
      end
      b = MatrixSpace(base_ring(base_ring(R)), 1, degree(R.modulus))()
      elem_to_mat_row!(b, 1, a)
      s = solve(Mt', b') # why, oh why is solve operating on columns????
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

function ResidueRingPolyMap{D, C, T}(domain::D, codomain::C, i::Residue{T})
  return ResidueRingPolyMap{D, C, T}(domain, codomain, i)
end

function ResidueRingPolyMap{D, C, T}(domain::D, codomain::C, i::Residue{T}, coeff_map::Map)
  return ResidueRingPolyMap{D, C, T}(domain, codomain, i, coeff_map)
end

type IdentityMap{D} <: Map{D, D}
  header::MapHeader{D, D}

  function IdentityMap(domain::D)
    z = new{D}()

    image = function(x::elem_type(D))
      return x::elem_type(D)
    end
    preimage = image

    z.header = MapHeader(domain, domain, image, preimage)
    return z
  end
end

type CoerceMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}

  function CoerceMap(domain::D, codomain::C)
    z = new{D, C}()
    z.header = MapHeader(domain, codomain)
    return z
  end

  function CoerceMap(domain::ResidueRing{fmpz}, codomain::FqNmodFiniteField)
    z = new{ResidueRing{fmpz}, FqNmodFiniteField}()

    image = function(a::Residue{fmpz})
        parent(a) != domain && error("Element not in domain")
        return codomain(ZZ(a))
    end

    preimage = function(a::fq_nmod)
      parent(a) != codomain && error("Element not in codomain")
      a.length > 1 && throw("Element not in image")
      return domain(coeff(a, 0))::Residue{fmpz}
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end

  function CoerceMap(domain::FqNmodFiniteField, codomain::ResidueRing{fq_nmod_poly})
    z = new{FqNmodFiniteField, ResidueRing{fq_nmod_poly}}()

    image = function(a::fq_nmod)
      parent(a) != domain && error("Element not in domain")
      return codomain(a)::Residue{fq_nmod_poly}
    end

    preimage = function(a::Residue{fq_nmod_poly})
      degree(a.data) > 0 && throw("Element not in subfield")
      return domain(coeff(a.data, 0))::fq_nmod
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end

  function CoerceMap{S, T <: Poly}(domain::ResidueRing{S}, codomain::ResidueRing{T})
    z = new{ResidueRing{S}, ResidueRing{T}}()

    image = function(a::Residue)
      return codomain(a)::elem_type(codomain)
    end

    preimage = function(a::Residue)
      while parent(a) != domain
        degree(a.data)>0 && throw("Element not in subfield")
        a = coeff(a.data, 0)
      end
      return a::elem_type(domain)
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end
end

function CoerceMap{D, C}(domain::D, codomain::C)
  return CoerceMap{D, C}(domain, codomain)
end
