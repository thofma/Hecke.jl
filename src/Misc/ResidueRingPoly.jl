import Nemo.characteristic, Nemo.gen, Nemo.size
export gen, characteristic, size, elem_to_mat_row!, rand

function gen(R::Union{Generic.ResRing{T},Generic.ResField{T}}) where T<:PolyElem
  return R(gen(base_ring(R)))
end

function gen(R::Union{Generic.ResRing{fqPolyRepPolyRingElem},Generic.ResField{fqPolyRepPolyRingElem}}) ## this is not covered by above
  return R(gen(base_ring(R)))              ## and I don't know why
end

function gen(R::Union{Generic.ResRing{zzModPolyRingElem},Generic.ResField{zzModPolyRingElem}})
  return R(gen(base_ring(R)))
end

function characteristic(R::Union{Generic.ResRing{Nemo.ZZRingElem},Generic.ResField{Nemo.ZZRingElem}})
  return modulus(R)
end

function characteristic(R::Union{Generic.ResRing{zzModPolyRingElem},Generic.ResField{zzModPolyRingElem}})
  return characteristic(base_ring(base_ring(R)))
end

function characteristic(R::Union{Generic.ResRing{T},Generic.ResField{T}}) where T<:PolyElem
  return characteristic(base_ring(base_ring(R)))
end

# discuss: size = order? order = size?
function size(R::Nemo.Union{Generic.ResRing{Nemo.zzModPolyRingElem},Generic.ResField{Nemo.zzModPolyRingElem}})
  return characteristic(R)^degree(modulus(R))
end

function size(R::Nemo.Union{Generic.ResRing{T},Generic.ResField{T}}) where T <: ResElem
  return size(base_ring(base_ring(R)))^degree(modulus(R))
end

function size(R::Nemo.Union{Generic.ResRing{ZZRingElem},Generic.ResField{ZZRingElem}})
  return modulus(R)
end

function size(R::Nemo.Union{Generic.ResRing{T},Generic.ResField{T}}) where T<:PolyElem
  return size(base_ring(base_ring(R)))^degree(R.modulus)
end

function size(R::Nemo.Union{Generic.ResRing{fqPolyRepPolyRingElem},Generic.ResField{fqPolyRepPolyRingElem}})
  return size(base_ring(base_ring(R)))^degree(R.modulus)
end

function size(R::FqPolyRepField)
  return order(R)
end

function size(R::fqPolyRepField)
  return order(R)
end

function size(F::fpField)
  return order(F)
end

function size(F::Nemo.FpField)
  return order(F)
end

function order(R::Nemo.zzModRing)
  return ZZRingElem(R.n)
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
function elem_to_mat_row!(M::MatElem, i::Int, a::ResElem{FqPolyRepPolyRingElem})
  z = zero(parent(M[1,1]))
  for j=0:degree(a.data)
    M[i,j+1] = coeff(a.data, j)
  end
  for j=degree(a.data)+2:ncols(M)
    M[i,j] = z
  end
end
function elem_to_mat_row!(M::MatElem, i::Int, a::ResElem{fqPolyRepPolyRingElem})
  z = zero(parent(M[1,1]))
  for j=0:degree(a.data)
    M[i,j+1] = coeff(a.data, j)
  end
  for j=degree(a.data)+2:ncols(M)
    M[i,j] = z
  end
end

function rand(R::Union{Generic.ResRing{ZZRingElem},Generic.ResField{ZZRingElem}})
  return R(rand(ZZRingElem(0):(size(R)-1)))
end

function rand(R::Generic.ResField{ZZRingElem})
  return R(rand(ZZRingElem(0):(order(R)-1)))
end

function rand(R::Union{Generic.ResRing{T},Generic.ResField{T}}) where T<:PolyElem
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::Union{Generic.ResRing{fqPolyRepPolyRingElem},Generic.ResField{fqPolyRepPolyRingElem}})
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::Union{Generic.ResRing{FqPolyRepPolyRingElem},Generic.ResField{FqPolyRepPolyRingElem}})
  r = rand(base_ring(base_ring(R)))
  g = gen(R)
  for i=1:degree(R.modulus)
    r = r*g + rand(base_ring(base_ring(R)))
  end
  return r
end

function rand(R::Union{Generic.ResRing{zzModPolyRingElem},Generic.ResField{zzModPolyRingElem}})
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

function gens(R::Union{Generic.ResRing{T},Generic.ResField{T}}) where T<:PolyElem ## probably needs more cases
                                          ## as the other residue functions
  g = gen(R)
  r = Vector{typeof(g)}()
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

function gens(R::Union{Generic.ResRing{zzModPolyRingElem},Generic.ResField{zzModPolyRingElem}})
  g = gen(R)
  r = Vector{typeof(g)}()
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

function rem!(f::Nemo.zzModPolyRingElem, g::Nemo.zzModPolyRingElem, h::Nemo.zzModPolyRingElem)
  ccall((:nmod_poly_rem, libflint), Nothing, (Ref{Nemo.zzModPolyRingElem}, Ref{Nemo.zzModPolyRingElem}, Ref{Nemo.zzModPolyRingElem}), f, g, h)
  return f
end

function gcd!(f::Nemo.zzModPolyRingElem, g::Nemo.zzModPolyRingElem, h::Nemo.zzModPolyRingElem)
  ccall((:nmod_poly_gcd, libflint), Nothing, (Ref{Nemo.zzModPolyRingElem}, Ref{Nemo.zzModPolyRingElem}, Ref{Nemo.zzModPolyRingElem}), f, g, h)
  return f
end

function gcd!(f::Nemo.fpPolyRingElem, g::Nemo.fpPolyRingElem, h::Nemo.fpPolyRingElem)
  ccall((:nmod_poly_gcd, libflint), Nothing, (Ref{Nemo.fpPolyRingElem}, Ref{Nemo.fpPolyRingElem}, Ref{Nemo.fpPolyRingElem}), f, g, h)
  return f
end

function (R::Nemo.zzModPolyRing)(g::QQPolyRingElem)
  return fmpq_poly_to_nmod_poly(R, g)
end

function (R::Nemo.fpPolyRing)(g::QQPolyRingElem)
  return fmpq_poly_to_gfp_poly(R, g)
end

function (R::Nemo.ZZModPolyRing)(g::QQPolyRingElem)
  return fmpq_poly_to_fmpz_mod_poly(R, g)
end

function (R::Nemo.FpPolyRing)(g::QQPolyRingElem)
  return fmpq_poly_to_gfp_fmpz_poly(R, g)
end

function (R::Nemo.FqPolyRing)(g::QQPolyRingElem)
  return fmpq_poly_to_fq_default_poly(R, g)
end
