import Nemo.characteristic, Nemo.gen, Nemo.size
export gen, characteristic, size, elem_to_mat_row!, rand

function gen(R::Generic.ResRing{T}) where T<:PolyElem  
  return R(gen(base_ring(R)))
end

function gen(R::Generic.ResRing{fq_nmod_poly}) ## this is not covered by above
  return R(gen(base_ring(R)))              ## and I don't know why
end

function gen(R::Generic.ResRing{nmod_poly}) 
  return R(gen(base_ring(R)))     
end

function characteristic(R::Generic.ResRing{Nemo.fmpz})
  return modulus(R)
end

function characteristic(R::Generic.ResRing{nmod_poly})
  return characteristic(base_ring(base_ring(R)))
end

function characteristic(R::Generic.ResRing{T}) where T<:PolyElem
  return characteristic(base_ring(base_ring(R)))
end

# discuss: size = order? order = size?
function size(R::Nemo.Generic.ResRing{Nemo.nmod_poly})
  return characteristic(R)^degree(modulus(R))
end

function size(R::Nemo.Generic.ResRing{T}) where T <: ResElem
  return size(base_ring(base_ring(R)))^degree(modulus(R))
end

function size(R::Nemo.Generic.ResRing{fmpz})
  return modulus(R)
end

function size(R::Nemo.Generic.ResRing{T}) where T<:PolyElem
  return size(base_ring(base_ring(R)))^degree(R.modulus)
end

function size(R::Nemo.Generic.ResRing{fq_nmod_poly})
  return size(base_ring(base_ring(R)))^degree(R.modulus)
end

function size(R::FqFiniteField)
  return order(R)
end

function size(R::FqNmodFiniteField)
  return order(R)
end

function order(R::Nemo.NmodRing)
  return fmpz(R.n)
end

function characteristic(R::Nemo.NmodRing)
  return fmpz(R.n)
end

#################################################
# in triplicate.... and probably cases missing...
function elem_to_mat_row!(M::MatElem, i::Int, a::ResElem{T}) where T <: PolyElem 
  z = zero(parent(M[1,1]))
  for j=0:degree(a.data)
    M[i,j+1] = coeff(a.data, j)
  end
  for j=degree(a.data)+2:ncols(M)
    M[i,j] = z
  end
end
function elem_to_mat_row!(M::MatElem, i::Int, a::ResElem{fq_poly}) 
  z = zero(parent(M[1,1]))
  for j=0:degree(a.data)
    M[i,j+1] = coeff(a.data, j)
  end
  for j=degree(a.data)+2:ncols(M)
    M[i,j] = z
  end
end
function elem_to_mat_row!(M::MatElem, i::Int, a::ResElem{fq_nmod_poly}) 
  z = zero(parent(M[1,1]))
  for j=0:degree(a.data)
    M[i,j+1] = coeff(a.data, j)
  end
  for j=degree(a.data)+2:ncols(M)
    M[i,j] = z
  end
end

function rand(R::Generic.ResRing{fmpz})
  return R(rand(fmpz(0):(size(R)-1)))
end

function rand(R::Generic.ResField{fmpz})
  return R(rand(fmpz(0):(order(R)-1)))
end

function rand(R::Generic.ResRing{T}) where T<:PolyElem
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::Generic.ResRing{fq_nmod_poly})
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::Generic.ResRing{fq_poly})
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::Generic.ResRing{nmod_poly})
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end


#######################################################
##
##
##
#######################################################

function gens(R::Generic.ResRing{T}) where T<:PolyElem ## probably needs more cases
                                          ## as the other residue functions
  g = gen(R)
  r = Array{typeof(g), 1}()
  push!(r, one(R))
  if degree(R.modulus)==1
    return r
  end
  push!(r, g)
  for i=2:degree(R.modulus)-1
    push!(r, r[end]*g)
  end
  return r
end

function gens(R::Generic.ResRing{nmod_poly}) 
  g = gen(R)
  r = Array{typeof(g), 1}()
  push!(r, one(R))
  if degree(R.modulus)==1
    return r
  end
  push!(r, g)
  for i=2:degree(R.modulus)-1
    push!(r, r[end]*g)
  end
  return r
end

function rem!(f::Nemo.nmod_poly, g::Nemo.nmod_poly, h::Nemo.nmod_poly)
  ccall((:nmod_poly_rem, :libflint), Nothing, (Ref{Nemo.nmod_poly}, Ref{Nemo.nmod_poly}, Ref{Nemo.nmod_poly}), f, g, h)
  return f
end

function gcd!(f::Nemo.nmod_poly, g::Nemo.nmod_poly, h::Nemo.nmod_poly)
  ccall((:nmod_poly_gcd, :libflint), Nothing, (Ref{Nemo.nmod_poly}, Ref{Nemo.nmod_poly}, Ref{Nemo.nmod_poly}), f, g, h)
  return f
end

function gcd!(f::Nemo.gfp_poly, g::Nemo.gfp_poly, h::Nemo.gfp_poly)
  ccall((:nmod_poly_gcd, :libflint), Nothing, (Ref{Nemo.gfp_poly}, Ref{Nemo.gfp_poly}, Ref{Nemo.gfp_poly}), f, g, h)
  return f
end

function (R::Nemo.NmodPolyRing)(g::fmpq_poly)
  return fmpq_poly_to_nmod_poly(R, g)
end

function (R::Nemo.GFPPolyRing)(g::fmpq_poly)
  return fmpq_poly_to_gfp_poly(R, g)
end

function (R::Nemo.FmpzModPolyRing)(g::fmpq_poly)
  return fmpq_poly_to_fmpz_mod_poly(R, g)
end

function (R::Nemo.GFPFmpzPolyRing)(g::fmpq_poly)
  return fmpq_poly_to_gfp_fmpz_poly(R, g)
end
