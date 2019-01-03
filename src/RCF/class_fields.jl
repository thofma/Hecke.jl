#TODO: create an interface using characters

mutable struct BadPrime <: Exception
  p
end

function Base.show(io::IO, E::BadPrime)
  if isdefined(E, :p)
    println("Bad prime $(E.p) encountered")
  else
    println("Unknown bad prime encountered")
  end
end

mutable struct ClassField_pp
  mq::Map
  rayclassgroupmap::Map#MapRayClassGrp
  quotientmap::Map#GrpAbFinGenMap
  a::FacElem#Generator of the Kummer Extension

  sup::Array{NfOrdIdl, 1} # the support of a - if known
  sup_known::Bool

  K::NfRel{nf_elem} # the target with the roots of unity
  A::NfRel{nf_elem} # the target
  o::Int # the degree of K - note, in general this is a divisor of the degree of A
  defect::Int # div(degree(A), degree(K)) = div(degree(A), o)
  pe::NfRelElem{nf_elem} #The image of the generator of A in K
  AutG::Array
  AutR::fmpz_mat
  bigK::KummerExt
  degree::Int # The degree of the relative extension we are searching for.
              # In other words, the order of the codomain of quotientmap

  function ClassField_pp()
    z = new()
    z.degree = -1
    return z
  end
end

function Base.show(io::IO, C::ClassField_pp)
  println(IOContext(io, :compact => true), "Cyclic class field of degree $(degree(C)) defined modulo $(defining_modulus(C))")
  if isdefined(C, :a)
    println(io, "Kummer generator ", C.a)
  end
  if isdefined(C, :K)
    println(io, "Kummer extension: ", C.K)
  end
  if isdefined(C, :A)
    println(io, "Defining  polynomial ", C.A.pol)
  end
end


mutable struct ClassField
  mq::Map
  rayclassgroupmap::Map
  quotientmap::Map#GrpAbFinGenMap

  conductor::Tuple{NfOrdIdl, Array{InfPlc, 1}}
  relative_discriminant::Dict{NfOrdIdl, Int}
  absolute_discriminant::Dict{fmpz,Int}
  cyc::Array{ClassField_pp, 1}
  A::NfRel_ns{nf_elem}
  degree::Int # The degree of the relative extension we are searching for.
              # In other words, the order of the codomain of quotientmap

  function ClassField()
    z = new()
    z.degree = -1
    return z
  end
end

function Base.show(io::IO, CF::ClassField)
  print(IOContext(io, :compact => true), "Class field defined mod ", 
                   defining_modulus(CF), " of structure ",
                   codomain(CF.quotientmap))
end

###############################################################################
#
#  Modulus function
#
###############################################################################

@doc Markdown.doc"""
    defining_modulus(CF::ClassField)
> The modulus, ie. an ideal the the set of real places, used to create the
> class field.
"""
function defining_modulus(CF::ClassField)
  return _modulus(CF.rayclassgroupmap)
end 

function defining_modulus(CF::ClassField_pp)
  return _modulus(CF.rayclassgroupmap)
end 

function _modulus(mq::MapRayClassGrp)
  return mq.defining_modulus
end

function _modulus(mq::MapClassGrp)
  return (ideal(order(codomain(mq)), 1), InfPlc[])
end

###############################################################################
#
#  Base ring and Base field
#
###############################################################################

@doc Markdown.doc"""
  base_ring(A::ClassField)
> The maximal order of the field that $A$ is defined over.
"""
function base_ring(A::ClassField)
  return order(defining_modulus(A)[1])
end

@doc Markdown.doc"""
  base_field(A::ClassField)
> The number field that $A$ is defined over.
"""
function base_field(A::ClassField)
  return number_field(base_ring(A))
end

function base_ring(A::ClassField_pp)
  return order(defining_modulus(A)[1])
end

function base_field(A::ClassField_pp)
  return number_field(base_ring(A))
end

###############################################################################
#
#  Degree
#
###############################################################################

@doc Markdown.doc"""
  degree(A::ClassField)
> The degree of $A$ over its base field, ie. the size of the defining ideal group.
"""
function degree(A::ClassField)
  if A.degree == -1
    A.degree = Int(order(codomain(A.quotientmap)))
  end
  return A.degree
end

function degree(A::ClassField_pp)
  if A.degree == -1
    A.degree = Int(order(codomain(A.quotientmap)))
  end
  return A.degree
end

###############################################################################
#
#  Compositum
#
###############################################################################

@doc Markdown.doc"""
    compositum(a::ClassField, b::ClassField) -> ClassField
             *(a::ClassField, b::ClassField) -> ClassField
> The compositum of $a$ and $b$ as a (formal) class field.
"""
function compositum(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  d = lcm(degree(a), degree(b))
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  @assert domain(C.rayclassgroupmap) == r
  h = norm_group_map(C, [a,b])
  U = intersect(kernel(h[1])[1], kernel(h[2])[1])
  q, mq = quo(codomain(C.quotientmap), U)
  return ray_class_field(mr, GrpAbFinGenMap(C.quotientmap * mq))
end

@doc Markdown.doc"""
  *(A::ClassField, B::ClassField) -> ClassField
> The compositum of $a$ and $b$ as a (formal) class field.
"""
*(a::ClassField, b::ClassField) = compositum(a, b)

###############################################################################
#
#  Intersection
#
###############################################################################

@doc Markdown.doc"""
    intersect(a::ClassField, b::ClassField) -> ClassField
> The intersect of $a$ and $b$ as a class field.
"""
function Base.intersect(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  d = lcm(degree(a), degree(b))

  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  h = norm_group_map(C, [a,b])
  U = kernel(h[1])[1] + kernel(h[2])[1]
  q, mq = quo(codomain(C.quotientmap), U)
  return ray_class_field(mr, GrpAbFinGenMap(C.quotientmap * mq))
end

###############################################################################
#
#  Subfield
#
###############################################################################

@doc Markdown.doc"""
    issubfield(a::ClassField, b::ClassField) -> Bool
> Determines of $a$ is a subfield of $b$.
"""
function issubfield(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  d = lcm(degree(a), degree(b))

  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  h = norm_group_map(C, [a,b])
  return issubset(kernel(h[2])[1], kernel(h[1])[1])
end

###############################################################################
#
#  Equality
#
###############################################################################

@doc Markdown.doc"""
    ==(a::ClassField, b::ClassField)
> Tests if $a$ and $b$ are equal.
"""
function ==(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  mq1 = a.quotientmap
  mq2 = b.quotientmap
  if !isisomorphic(codomain(mq1), codomain(mq2))
    return false
  end
  expo = Int(exponent(codomain(mq1)))
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  r, mr = ray_class_group(c, c_inf, n_quo = expo)
  C = ray_class_field(mr)
  @assert defining_modulus(C) == (c, c_inf)
  h = norm_group_map(C, [a,b])
  return iseq(kernel(h[2])[1], kernel(h[1])[1])
end


###############################################################################
#
#  IsCyclic
#
###############################################################################

@doc Markdown.doc"""
    iscyclic(C::ClassField)
> Tests if the (relative) automorphism group of $C$ is cyclic (by checking
> the defining ideal group).
"""
function iscyclic(C::ClassField)
  mp = C.quotientmap
  return iscyclic(codomain(mp))
end

###############################################################################
#
#  Maximal p-subfield
#
###############################################################################

@doc Markdown.doc"""
    maximal_p_subfield(C::ClassField, p::Int)
> Returns the class field corresponding to the maximal subextension of
> prime power degree
"""
function maximal_p_subfield(C::ClassField, p::Int)
  mg = C.quotientmap
  v = valuation(degree(C), p)
  q, mq = quo(codomain(mg), p^v)
  s, ms = snf(q)
  mg1 = GrpAbFinGen(mg*mq*ms)
  return ray_class_field(C.rayclassgroupmap, mg1)
end
