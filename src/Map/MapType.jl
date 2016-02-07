###########################################################
## 
## MAPS
##
## maps between residue rings of polynomials and in general
##
###########################################################

export Map, CoerceMap, ResidueRingPolyMap

abstract Map{D, C}

type MapHeader{D, C}
  domain::D
  codomain::C
  preim::Function
  image::Function

  function MapHeader(a::D, b::C)
    r = new{D, C}()
    r.domain = a
    r.codomain = b
    return r
  end

  function MapHeader(a::D, b::C, i::Function, p::Function)
    r = new{D, C}()
    r.domain = a
    r.codomain = b
    r.image = i
    r.preim = p
    return r
  end
end

# this type represents a -> f(g(a))
type CompositeMap2{D, C, R} <: Map{D, C}
  domain::D
  codomain::C
  image::Function
  preimage::Function
  f::Map{R, C}
  g::Map{D, R}

  function CompositeMap2(f::Map{R, C}, g::Map{D, R})
    codomain(f) == domain(g) || throw("maps not compatible")
    z = new{D, C, R}()
    z.domain = domain(g)
    z.codomain = codomain(f)

    z.image = function(x::elem_type(domain(z)))
      parent(x) != domain(z) && error("Element not in domain of map")
      return f(g(x))::elem_type(codomain(z))
    end

    if isdefined(f, :preimage) && isdefined(g, :preimage)
      z.preimage = function(x::elem_type(codomain(z)))
        return codomain(g, codomain(f, x))
      end
    end

    return z
  end
end

type CompositeMap{D, C, R} <: Map{D, C}
  header::MapHeader{D, C}
  a::Map{R, C}
  b::Map{D, R}

  function CompositeMap(a::Map{R, C}, b::Map{D, R})
    codomain(a) == domain(b) || throw("maps not compatible")
    r = new{D, C, R}()
    r.a = a
    r.b = b

    image = function(M::CompositeMap, a::Any)
      return M.a(M.b(a))::elem_type(M.a.header.codomain)
    end

    preim = function(M::CompositeMap, a::Any)
      return preimage(M.b, preimage(M.a, a))::elem_type(M.a.codomain)
    end

    r.header = MapHeader{D, C}(a.header.domain, b.header.codomain, image, preim)
    return r
  end
end

type InverseMap2{D, C} <: Map{D, C}
  domain::D
  codomain::C
  image::Function
  preimage::Function
  origin::Map{C, D}

  function InverseMap2(f::Map{C, D})
    z = new{D, C}()
    z.domain = codomain(f)
    z.codomain = domain(f)
    z.origin = f

    z.image = function(x::elem_type(domain(z)))
      return preimage(f, x)
    end

    z.preimage = function(x::elem_type(codomain(z)))
      return image(f, x)
    end
    return z
  end
end

type InverseMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}
  a::Map

  function InverseMap(a::Map{C, D})
    r = new{D, C}()
    r.a = a
    image = function(M::Map, a::Any)
      return preimage(M.a, a)
    end
    preim = function(M::Map, a::Any)
      return image(M.a, a)
    end
    r.header = MapHeader{D, C}(a.codomain, a.domain, image, preim)
    return r
  end
end

type ResidueRingPolyMap{D, C, T} <: Map{D, C}
  domain::D
  codomain::C
  image::Function
  preimage::Function
  gen_image::Residue{T}
  coeff_map::Map # can be missing if domain and codomain have the same
                 # base_ring(base_ring())
  function ResidueRingPolyMap(domain::D, codomain::C, gen_image::Residue{T}, coeff_map::Map)
    z = new{D, C, T}()
    z.domain = domain
    z.codomain = codomain
    z.gen_image = gen_image
    z.coeff_map = coeff_map

    z.image = function(a::Residue)
      #a should be in the domain of M...
      I = z.codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + z.coeff_map(coeff(a.data, i))
      end
      return I::elem_type(C)
    end
    
    z.preimage = function(a::Residue{T})
      R = z.codomain
      parent(a) == R || throw("mixed rings in preimage")
      g = gens(z.domain)
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
      @assert parent(s) == z.domain
      return s::elem_type(z.domain)
    end
    return z
  end

  function ResidueRingPolyMap(domain::D, codomain::C, gen_image::Residue{T})
    z = new{D, C, T}()
    z.domain = domain
    z.codomain = codomain
    z.gen_image = gen_image

    z.image = function(a::Residue)
      I = z.codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + coeff(a.data, i)
      end
      return I::elem_type(C)
    end

    z.preimage = function(a::Residue{T})
      R = z.codomain
      parent(a) == R || throw("mixed rings in preimage")
      g = gens(z.domain)
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

      @assert parent(s) == z.domain
      return s::elem_type(z.domain)
    end

    return z
  end
end

function ResidueRingPolyMap{D, C, T}(d::D, c::C, i::Residue{T})
  return ResidueRingPolyMap{D, C, T}(d::D, c::C, i::Residue{T})
end

function ResidueRingPolyMap{D, C, T}(d::D, c::C, i::Residue{T}, coeff_map::Map)
  return ResidueRingPolyMap{D, C, T}(d::D, c::C, i::Residue{T}, coeff_map)
end

type IdentityMap{D} <: Map{D, D}
  domain::D
  codomain::D
  image::Function
  preimage::Function

  function IdentityMap(domain::D)
    z = new{D}()
    z.domain = domain
    z.codomain = domain
    z.image = function(x::elem_type(D))
      return x::elem_type(D)
    end
    z.preimage = z.image
    return z
  end
end

type CoerceMap{D, C} <: Map{D, C}
  domain::D
  codomain::C
  image::Function
  preimage::Function

  function CoerceMap(domain::D, codomain::C)
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    return z
  end

  function CoerceMap(domain::ResidueRing{fmpz}, codomain::FqNmodFiniteField)
    z = new{ResidueRing{fmpz}, FqNmodFiniteField}()
    z.domain = domain
    z.codomain = codomain

    z.image = function(a::Residue{fmpz})
        parent(a) != z.domain && error("Element not in domain")
        return z.codomain(ZZ(a))
    end

    z.preimage = function(a::fq_nmod)
      parent(a) != z.codomain && error("Element not in codomain")
      a.length > 1 && throw("Element not in image")
      return z.domain(coeff(a, 0))::Residue{fmpz}
    end
    return z
  end

  function CoerceMap(domain::FqNmodFiniteField, codomain::ResidueRing{fq_nmod_poly})
    z = new{FqNmodFiniteField, ResidueRing{fq_nmod_poly}}()
    z.domain = domain
    z.codomain = codomain

    z.image = function(a::fq_nmod)
      parent(a) != z.domain && error("Element not in domain")
      return z.codomain(a)::Residue{fq_nmod_poly}
    end

    z.preimage = function(a::Residue{fq_nmod_poly})
      degree(a.data) > 0 && throw("Element not in subfield")
      return z.domain(coeff(a.data, 0))::fq_nmod
    end
    return z
  end

  function CoerceMap{S, T <: Poly}(domain::ResidueRing{S}, codomain::ResidueRing{T})
    z = new{ResidueRing{S}, ResidueRing{T}}()
    z.domain = domain
    z.codomain = codomain

    z.image = function(a::Residue)
      return c(a)::elem_type(z.domain)
    end

    z.preimage = function(a::Residue)
      while parent(a) != z.domain
        degree(a.data)>0 && throw("Element not in subfield")
        a = coeff(a.data, 0)
      end
      return a::elem_type(z.domain)
    end

    return z
  end
end

function CoerceMap{D, C}(d::D, c::C)
  return CoerceMap{D, C}(d, c)
end
