import Nemo.characteristic, Nemo.gen, Nemo.size
export gen, characteristic, size, elem_to_mat_row!, rand

function gen{T<:Poly}(R::ResidueRing{T})  
  return R(gen(base_ring(R)))
end

function gen(R::ResidueRing{fq_nmod_poly}) ## this is not covered by above
  return R(gen(base_ring(R)))              ## and I don't know why
end

function gen(R::ResidueRing{nmod_poly}) 
  return R(gen(base_ring(R)))     
end

function characteristic(R::ResidueRing{Nemo.fmpz})
  return modulus(R)
end

function characteristic(R::ResidueRing{nmod_poly})
  return characteristic(base_ring(base_ring(R)))
end

function characteristic{T<:Poly}(R::ResidueRing{T})
  return characteristic(base_ring(base_ring(R)))
end

# discuss: size = order? order = size?
function size(R::Nemo.ResidueRing{Nemo.nmod_poly})
  return characteristic(R)^degree(modulus(R))
end

function size(R::Nemo.ResidueRing{Nemo.Residue})
  return size(base_ring(base_ring(R)))^degree(modulus(R))
end

function size(R::Nemo.ResidueRing{fmpz})
  return modulus(R)
end

function size{T<:Poly}(R::Nemo.ResidueRing{T})
  return size(base_ring(base_ring(R)))^degree(R.modulus)
end

function size(R::Nemo.ResidueRing{fq_nmod_poly})
  return size(base_ring(base_ring(R)))^degree(R.modulus)
end

function size(R::FqFiniteField)
  return order(R)
end

function size(R::FqNmodFiniteField)
  return order(R)
end

#################################################
# in triplicate.... and probably cases missing...
function elem_to_mat_row!{T <: Poly}(M::MatElem, i::Int, a::Residue{T}) 
  z = zero(parent(M[1,1]))
  for j=0:degree(a.data)
    M[i,j+1] = coeff(a.data, j)
  end
  for j=degree(a.data)+2:cols(M)
    M[i,j] = z
  end
end
function elem_to_mat_row!(M::MatElem, i::Int, a::Residue{fq_poly}) 
  z = zero(parent(M[1,1]))
  for j=0:degree(a.data)
    M[i,j+1] = coeff(a.data, j)
  end
  for j=degree(a.data)+2:cols(M)
    M[i,j] = z
  end
end
function elem_to_mat_row!(M::MatElem, i::Int, a::Residue{fq_nmod_poly}) 
  z = zero(parent(M[1,1]))
  for j=0:degree(a.data)
    M[i,j+1] = coeff(a.data, j)
  end
  for j=degree(a.data)+2:cols(M)
    M[i,j] = z
  end
end

function rand(R::ResidueRing{fmpz})
  return R(rand(fmpz(0):(size(R)-1)))
end

function rand{T<:Poly}(R::ResidueRing{T})
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::ResidueRing{fq_nmod_poly})
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::ResidueRing{fq_poly})
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::ResidueRing{nmod_poly})
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

function gens{T<:Poly}(R::ResidueRing{T}) ## probably needs more cases
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

function gens(R::ResidueRing{nmod_poly}) 
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
  ccall((:nmod_poly_rem, :libflint), Void, (Ptr{Nemo.nmod_poly}, Ptr{Nemo.nmod_poly}, Ptr{Nemo.nmod_poly}), &f, &g, &h)
  return f
end

function gcd!(f::Nemo.nmod_poly, g::Nemo.nmod_poly, h::Nemo.nmod_poly)
  ccall((:nmod_poly_gcd, :libflint), Void, (Ptr{Nemo.nmod_poly}, Ptr{Nemo.nmod_poly}, Ptr{Nemo.nmod_poly}), &f, &g, &h)
  return f
end

function Base.call(R::Nemo.NmodPolyRing, g::fmpq_poly)
  return fmpq_poly_to_nmod_poly(R, g)
end

