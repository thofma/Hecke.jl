export local_field

################################################################################
#
#  Show function
#
################################################################################

function show(io::IO, a::LocalField{S, EisensteinLocalField}) where S
  print(io, "Eisenstein extension with defining polynomial ", defining_polynomial(a))
  print(io, " over ", base_field(a))
end

function show(io::IO, a::LocalField{S, UnramifiedLocalField}) where S
  print(io, "Unramified extension with defining polynomial ", defining_polynomial(a))
  print(io, " over ", base_field(a))
end

function show(io::IO, a::LocalField{S, GenericLocalField}) where S
  print(io, "Extension with defining polynomial ", defining_polynomial(a))
  print(io, " over ", base_field(a))
end

################################################################################
#
#  Characteristic
#
################################################################################

characteristic(K::LocalField) = characteristic(base_field(K))
prime(K::LocalField) = prime(base_field(K))

################################################################################
#
#  Type derivation
#
################################################################################

elem_type(K::LocalField{S, T}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}
elem_type(::Type{LocalField{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

dense_matrix_type(K::LocalField{S, T}) where {S <: FieldElem, T <: LocalFieldParameter} =  Generic.MatSpaceElem{LocalFieldElem{S, T}}
dense_matrix_type(::Type{LocalField{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} =  Generic.MatSpaceElem{LocalFieldElem{S, T}}

dense_poly_type(K::LocalField{S, T}) where {S <: FieldElem, T <: LocalFieldParameter} = Generic.Poly{LocalFieldElem{S, T}}
dense_poly_type(::Type{LocalField{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = Generic.Poly{LocalFieldElem{S, T}}

################################################################################
#
#  Basic predicates
#
################################################################################

isdomain_type(::Type{S}) where S <: LocalField = true

isexact_type(::Type{S}) where S <: LocalField = false


################################################################################
#
#  Generating polynomials properties 
#
################################################################################


function iseisenstein(f::PolyElem{S}) where S <: Union{padic, qadic, LocalFieldElem}
  if !iszero(valuation(leading_coefficient(f)))
    return false
  end
  if !isone(ramification_index(base_ring(f))*valuation(constant_coefficient(f)))
    return false
  end
  for i = 1:degree(f)-1
    if valuation(coeff(f, i)) <= 0
      return false
    end
  end
  return true
end

function _generates_unramified_extension(f::PolyElem{S}) where S <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(f)
  F, mF = ResidueField(K)
  g = map_coeffs(mF, f)
  return isirreducible(g)
end

var(a::LocalField) = a.S


function gen(K::LocalField)
  g = gen(parent(defining_polynomial(K)))
  setprecision!(g, precision(K))
  return K(g)
end


################################################################################
#
#  Subfields
#
################################################################################

function prime_field(L::LocalField)
  return FlintRationalField
end


function base_field(L::LocalField)
  return base_ring(L.defining_polynomial)
end

################################################################################
#
#  Degree
#
################################################################################

function degree(K::LocalField)
  return degree(defining_polynomial(K))
end

function absolute_degree(::FlintPadicField)
  return 1
end

function absolute_degree(K::FlintQadicField)
  return degree(K)
end
function absolute_degree(K::LocalField)
  return degree(K)*absolute_degree(base_field(K))
end

################################################################################
#
#  Traces
#
################################################################################

function assure_traces(K::LocalField{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  if isdefined(K, :traces_basis)
    return nothing
  end
  res = S[base_field(K)(degree(K))]
  append!(res, polynomial_to_power_sums(defining_polynomial(K), degree(K)-1))
  K.traces_basis = res
  return nothing
end

################################################################################
#
#  Ramification index
#
################################################################################

function ramification_index(K::FlintPadicField)
  return 1
end

function ramification_index(K::FlintQadicField)
  return 1
end

function ramification_index(K::LocalField{S, EisensteinLocalField}) where S <: FieldElem
  return degree(K)
end

function ramification_index(K::LocalField{S, UnramifiedLocalField}) where S <: FieldElem
  return 1
end


absolute_ramification_index(K::PadicField) = 1
absolute_ramification_index(K::QadicField) = 1

function absolute_ramification_index(K::LocalField{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  return ramification_index(K)*ramification_index(base_field(K))
end

function ramification_index(L::LocalField, K::LocalField)
  if base_field(L) === K
    return ramification_index(L)
  else
    return ramification_index(L)*ramification_index(base_field(L), K)
  end
end

################################################################################
#
#  Inertia degree
#
################################################################################

function inertia_degree(K::FlintPadicField)
  return 1
end

function inertia_degree(K::LocalField{S, EisensteinLocalField}) where S
  return 1
end

function inertia_degree(K::LocalField{S, UnramifiedLocalField}) where S
  return degree(K)
end

function inertia_degree(L::LocalField, K::LocalField)
  if base_field(L) === K
    return inertia_degree(L)
  else
    return inertia_degree(L)*inertia_degree(base_field(L), K)
  end
end

function absolute_inertia_degree(L::LocalField)
  return inertia_degree(L)*inertia_degree(base_field(L))
end

absolute_inertia_degree(::PadicField) = 1
absolute_inertia_degree(K::QadicField) = degree(K)

################################################################################
#
#  Basis
#
################################################################################

function basis(K::LocalField)
  return powers(gen(K), degree(K)-1)
end

function absolute_basis(K::LocalField)
  Bk = absolute_basis(base_field(K))
  BKr = basis(K)
  BK = Vector{elem_type(K)}()
  for i = 1:length(BKr)
    for j = 1:length(Bk)
      push!(BK, Bkr[i]*Bk[j])
    end
  end
  return BK
end

################################################################################
#
#  Constructors
#
################################################################################

#=
function find_irreducible_polynomial(K, n::Int)
  Zx, x = PolynomialRing(FlintZZ, "x", cached = false)
  f = cyclotomic(ppio(degree(K), n)*n, x)
  lf = factor(f, K)
  return first(keys(lf[1]))
end

function unramified_extension(L::LocalField, n::Int, prec::Int, s::String = "z")
  K, mK = ResidueField(L)
  f = find_irreducible_polynomial(K, n)
  coeffs = 
  return local
end
=#

function eisenstein_extension(f::Generic.Poly{S}, s::String = "a"; check::Bool = true, cached::Bool = true) where S
  return local_field(f, s, EisensteinLocalField, check = check, cached = cached)
end

function unramified_extension(f::Generic.Poly{S}, s::String = "a"; check::Bool = true, cached::Bool = true) where S
  return local_field(f, s, UnramifiedLocalField, check = check, cached = cached)
end

function local_field(f::Generic.Poly{S},::Type{T}; check::Bool = true, cached::Bool = true) where {S <: FieldElem, T <: LocalFieldParameter}
  return local_field(f, "a", T, check = check, cached = cached)
end

function local_field(f::Generic.Poly{S}, s::String, ::Type{EisensteinLocalField}; check::Bool = true, cached::Bool = true) where {S <: FieldElem}
  symb = Symbol(s)
  if check && !iseisenstein(f)
    error("Defining polynomial is not Eisenstein")
  end
  K = LocalField{S, EisensteinLocalField}(f, symb)
  return K, gen(K)
end

function local_field(f::Generic.Poly{S}, s::String, ::Type{UnramifiedLocalField}; check::Bool = true, cached::Bool = true) where {S <: FieldElem}
  symb = Symbol(s)
  if check && !_generates_unramified_extension(f)
    error("Defining polynomial is not irreducible over the residue field!")
  end
  K = LocalField{S, UnramifiedLocalField}(f, symb)
  return K, gen(K)
end

function local_field(f::Generic.Poly{S}, s::String, ::Type{T} = GenericLocalField; check::Bool = true, cached::Bool = true) where {S <: FieldElem, T <: LocalFieldParameter}
  symb = Symbol(s)
  if check && !isirreducible(f)
    error("Defining polynomial is not irreducible")
  end
  K = LocalField{S, T}(f, symb)
  return K, gen(K)
end

function local_field(f::fmpq_poly, p::Int, precision::Int, s::String, ::Type{T} = GenericLocalField; check::Bool = true, cached::Bool = true) where T <: LocalFieldParameter
  @assert isprime(p)
  K = PadicField(p, precision)
  fK = map_coeffs(K, f)
  return local_field(fK, s, T, cached = cached, check = check)
end

function defining_polynomial(K::LocalField)
  return K.defining_polynomial
end

function precision(K::LocalField)
  return precision(defining_polynomial(K))
end

################################################################################
#
#  Uniformizer
#
################################################################################

function uniformizer(K::LocalField{S, EisensteinLocalField}) where S <: FieldElem
  return gen(K)
end

function uniformizer(K::LocalField{S, UnramifiedLocalField}) where S <: FieldElem
  return K(uniformizer(base_field(K)))
end

function uniformizer(K::LocalField{S, GenericLocalField}) where S <: FieldElem
  error("Not yet implemented")
end

################################################################################
#
#  ResidueField
#
################################################################################

function ResidueField(K::LocalField{S, EisensteinLocalField}) where {S <: FieldElem}
  k = base_field(K)
  ks, mks = ResidueField(k)

  function proj(a::LocalFieldElem)
    @assert parent(a) === K
    for i = 1:degree(a.data)
      if valuation(coeff(a, i)) < 0
        error("The projection is not well defined!")
      end
    end
    return mks(coeff(a, 0))
  end

  function lift(a::fq)
    @assert parent(a) === ks
    return setprecision(K(mks\(a)), 1)
  end

  return MapFromFunction(proj, lift, K, ks)
end