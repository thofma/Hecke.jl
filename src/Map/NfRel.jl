################################################################################
#
#  Map/RelSimpleNumField.jl : Types for maps with domains of type RelSimpleNumField
#
################################################################################

mutable struct NfRelToFqMor{T} <: Map{RelSimpleNumField{T}, FqField, HeckeMap, NfRelToFqMor}
  header::MapHeader{RelSimpleNumField{T}, FqField}

  function NfRelToFqMor{T}() where {T}
    z = new{T}()
    z.header = MapHeader{RelSimpleNumField{T}, FqField}()
    return z
  end
end

function _automorphisms(L::RelSimpleNumField{T}) where T
  if degree(L) == 1
    return morphism_type(L)[id_hom(L)]
  end
  f = L.pol
  Lt, t = polynomial_ring(L, "t", cached = false)
  f1 = change_base_ring(L, f, parent = Lt)
  divpol = Lt([ -gen(L), L(1) ])
  f1 = divexact(f1, divpol)
  lr = roots(f1)
  auts = Vector{morphism_type(L, L)}(undef, length(lr) + 1)
  for i = 1:length(lr)
    auts[i] = hom(L, L, lr[i], check = false)
  end
  auts[end] = id_hom(L)
  return auts
end

function automorphism_list(L::T; copy::Bool = true) where {T <: RelSimpleNumField}
  auts = get_attribute!(L, :automorphisms) do
    return _automorphisms(L)
  end::Vector{morphism_type(T, T)}

  if copy
    v = Vector{morphism_type(T, T)}(undef, length(auts))
    for i = 1:length(v)
      v[i] = auts[i]
    end
    return v::Vector{morphism_type(T, T)}
  else
    return auts::Vector{morphism_type(T, T)}
  end
end

# Embedding of a relative number field into an algebra over the base field.
# S is the type of the field, T the type of the algebra and Mat the dense matrix
# type of the base ring of either
mutable struct NfRelToAbsAlgAssMor{S, T, Mat} <: Map{S, T, HeckeMap, NfRelToAbsAlgAssMor}
  header::MapHeader{S, T}
  mat::Mat
  t::Mat

  function NfRelToAbsAlgAssMor{S, T, Mat}(K::S, A::T, M::Mat) where { S <: RelSimpleNumField, T <: AbstractAssociativeAlgebra, Mat <: MatElem }
    @assert base_ring(A) == base_field(K)
    z = new{S, T, Mat}()
    z.mat = M
    z.t = zero_matrix(base_field(K), 1, degree(K))

    function _image(x::RelSimpleNumFieldElem)
      for i = 1:degree(K)
        z.t[1, i] = coeff(x, i - 1)
      end
      s = z.t*z.mat
      return A([ s[1, i] for i = 1:dim(A) ])
    end

    z.header = MapHeader{S, T}(K, A, _image)
    return z
  end
end

function NfRelToAbsAlgAssMor(K::S, A::T, M::Mat) where { S <: RelSimpleNumField, T <: AbstractAssociativeAlgebra, Mat <: MatElem }
  return NfRelToAbsAlgAssMor{S, T, Mat}(K, A, M)
end

function has_preimage_with_preimage(m::NfRelToAbsAlgAssMor, a::AbstractAssociativeAlgebraElem)
  A = parent(a)
  t = matrix(base_ring(A), 1, dim(A), coefficients(a))
  b, p = can_solve_with_solution(m.mat, t, side = :left)
  if b
    return true, domain(m)([ p[1, i] for i = 1:nrows(m.mat) ])
  else
    return false, zero(domain(m))
  end
end

