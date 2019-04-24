################################################################################
#
#  Basic field access
#
################################################################################

base_ring(A::AlgGrp{T}) where {T} = A.base_ring::parent_type(T)

Generic.dim(A::AlgGrp) = size(multiplication_table(A, copy = false), 1)

elem_type(::Type{AlgGrp{T, S, R}}) where {T, S, R} = AlgGrpElem{T, AlgGrp{T, S, R}}

group(A::AlgGrp) = A.group

has_one(A::AlgGrp) = true

function (A::AlgGrp{T, S, R})(c::Array{T, 1}) where {T, S, R}
  length(c) != dim(A) && error("Dimensions don't match.")
  return AlgGrpElem{T, typeof(A)}(A, c)
end

function multiplication_table(A::AlgGrp; copy::Bool = true)
  if copy
    return deepcopy(A.mult_table)
  else
    return A.mult_table
  end
end

################################################################################
#
#  Commutativity
#
################################################################################

iscommutative_known(A::AlgGrp) = (A.iscommutative != 0)

function iscommutative(A::AlgGrp)
  if iscommutative_known(A)
    return A.iscommutative == 1
  end
  for i in 1:dim(A)
    for j in 1:dim(A)
      if multiplication_table(A, copy = false)[i, j] != multiplication_table(A, copy = false)[j, i]
        A.iscommutative = 2
        return false
      end
    end
  end
  A.iscommutative = 1
  return true
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::AlgGrp)
  compact = get(io, :compact, false)
  if compact
    print(io, "Group algebra of dimension ", dim(A), " over ", base_ring(A))
  else
    print(io, "Group algebra of group\n", group(A), "\nover\n", base_ring(A))
  end
end

################################################################################
#
#  Deepcopy
#
################################################################################

# TODO: This is broken. I have to copy everything carefully by hand.
#function Base.deepcopy_internal(A::AlgGrp, dict::IdDict) 
#  B = AlgGrp(base_ring(A), group(A))
#  for x in fieldnames(typeof(A))
#    if x != :base_ring && x != :group && isdefined(A, x)
#      setfield!(B, x, Base.deepcopy_internal(getfield(A, x), dict))
#    end
#  end
#  B.base_ring = A.base_ring
#  B.group = A.group
#  return B
#end

################################################################################
#
#  Equality
#
################################################################################

function ==(A::AlgGrp{T}, B::AlgGrp{T}) where {T}
  return base_ring(A) == base_ring(B) && group(A) == group(B)
end

###############################################################################
#
#  Trace Matrix
#
###############################################################################

function _assure_trace_basis(A::AlgGrp{T}) where {T}
  if !isdefined(A, :trace_basis_elem)
    A.trace_basis_elem = Vector{T}(undef, dim(A))
    A.trace_basis_elem[1] = base_ring(A)(dim(A))
    for i=2:length(A.trace_basis_elem)
      A.trace_basis_elem[i] = zero(base_ring(A))
    end
  end
  return nothing
end

function trace_matrix(A::AlgGrp)
  _assure_trace_basis(A)
  F = base_ring(A)
  n = dim(A)
  M = zero_matrix(F, n, n)
  for i = 1:n
    M[i,i] = tr(A[i]^2)  
  end
  for i = 1:n
    for j = i+1:n
      x = tr(A[i]*A[j])
      M[i,j] = x
      M[j,i] = x
    end
  end
  return M
end

################################################################################
#
#  Center
#
################################################################################

@doc Markdown.doc"""
    center(A::AlgGrp{T}) where T

Returns the center C of A and the inclusion C \to A.
"""
function center(A::AlgGrp{T}) where {T}
  if iscommutative(A)
    B, mB = AlgAss(A)
    return B, mB
  end

  if isdefined(A, :center)
    return A.center::Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}
  end

  B, mB = AlgAss(A)
  C, mC = center(B)
  mD = compose_and_squash(mB, mC)
  A.center = C, mD
  return C, mD
end

################################################################################
#
#  Conversion to AlgAss
#
################################################################################

function AlgAss(A::AlgGrp{T, S, R}) where {T, S, R}
  K = base_ring(A)
  mult = Array{T, 3}(undef, dim(A), dim(A), dim(A))
  B = basis(A)
  d = dim(A)
  for i in 1:d
    for j in 1:d
      l = multiplication_table(A, copy = false)[i, j]
      for k in 1:d
        if k == l
          mult[i, j, k] = one(K)
        else
          mult[i, j, k] = zero(K)
        end
      end
    end
  end
  B = AlgAss(K, mult, one(A).coeffs)
  return B, hom(B, A, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
end

################################################################################
#
#  Misc
#
################################################################################

Base.enumerate(G::Generic.PermGroup) = enumerate(AllPerms(G.n))
