export group_algebra

################################################################################
#
#  Basic field access
#
################################################################################

base_ring(A::AlgGrp{T}) where {T} = A.base_ring::parent_type(T)

Generic.dim(A::AlgGrp) = size(multiplication_table(A, copy = false), 1)

elem_type(::Type{AlgGrp{T, S, R}}) where {T, S, R} = AlgGrpElem{T, AlgGrp{T, S, R}}

order_type(::AlgGrp{fmpq, S, R}) where { S, R } = AlgAssAbsOrd{AlgGrp{fmpq, S, R}, elem_type(AlgGrp{fmpq, S, R})}
order_type(::Type{AlgGrp{fmpq, S, R}}) where { S, R } = AlgAssAbsOrd{AlgGrp{fmpq, S, R}, elem_type(AlgGrp{fmpq, S, R})}

order_type(::AlgGrp{T, S, R}) where { T <: NumFieldElem, S, R } = AlgAssRelOrd{T, frac_ideal_type(order_type(parent_type(T)))}
order_type(::Type{AlgGrp{T, S, R}}) where { T <: NumFieldElem, S, R } = AlgAssRelOrd{T, frac_ideal_type(order_type(parent_type(T)))}

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
#  Construction
#
################################################################################

group_algebra(K::Ring, G; op = *) = AlgGrp(K, G, op = op)

group_algebra(K::Ring, G::GrpAbFinGen) = AlgGrp(K, G)

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
  B.iscommutative = A.iscommutative
  B.issimple = A.issimple
  B.issemisimple = A.issemisimple
  return B, hom(B, A, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
end

################################################################################
#
#  Misc
#
################################################################################

Base.enumerate(G::Generic.PermGroup) = enumerate(AllPerms(G.n))

################################################################################
#
#  Generators
#
################################################################################

# Helper function for gens, changes mid in place
function _merge_elts_in_gens!(left::Vector{Tuple{Int, Int}}, mid::Vector{Tuple{Int, Int}}, right::Vector{Tuple{Int, Int}})
  nl = length(left)
  if length(mid) == 0
    mid = deepcopy(left)
  elseif nl != 0
    if left[nl][1] == mid[1][1]
      t = popfirst!(mid)
      prepend!(mid, left)
      tt = (t[1], mid[nl][2] + t[2])
      mid[nl] = tt
    else
      prepend!(mid, left)
    end
  end
  nm = length(mid)
  if nm == 0
    return deepcopy(right)
  end
  if length(right) == 0
    return mid
  end
  if mid[nm][1] == right[1][1]
    t = pop!(mid)
    append!(mid, right)
    tt = (t[1], mid[nm][2] + t[2])
    mid[nm] = tt
  else
    append!(mid, right)
  end
  return mid
end

function gens(A::AlgGrp, return_full_basis::Type{Val{T}} = Val{false}) where T
  G = group(A)
  group_gens = gens(G)

  return_full_basis == Val{true} ? nothing : return map(A, group_gens)

  full_group = elem_type(G)[ id(G) ]
  elts_in_gens = Vector{Tuple{Int, Int}}[ Tuple{Int, Int}[] ]
  constructed_elements = falses(BigInt(order(G)))
  constructed_elements[A.group_to_base[id(G)]] = true
  new_elements = Set{Int}()
  for i = 1:length(group_gens)
    g = group_gens[i]
    push!(full_group, g)
    push!(elts_in_gens, Tuple{Int, Int}[ (i, 1) ])
    constructed_elements[A.group_to_base[g]] = true
    push!(new_elements, length(full_group))
  end
  k = 1 + length(group_gens) # == number of constructed elements, i. e. #{ i | constructed_elements[i] == true }

  while k != dim(A) || !isempty(new_elements)
    i = pop!(new_elements)
    g = full_group[i]

    n = length(full_group)
    for r = 1:n
      s = op(g, full_group[r])
      for l = 1:n
        if !iscommutative(A)
          t = op(full_group[l], s)
        else
          t = s
        end
        if constructed_elements[A.group_to_base[t]]
          continue
        end
        constructed_elements[A.group_to_base[t]] = true
        k += 1
        push!(full_group, t)
        coord = _merge_elts_in_gens!(elts_in_gens[l], deepcopy(elts_in_gens[i]), elts_in_gens[r])
        push!(elts_in_gens, coord)
        push!(new_elements, length(full_group))
        if iscommutative(A)
          break
        end
        k == dim(A) ? break : nothing
      end
      k == dim(A) ? break : nothing
    end
  end

  return map(A, group_gens), map(A, full_group), elts_in_gens
end

################################################################################
#
#  Isomorphisms to number fields
#
################################################################################

# Assumes that Gal(K/k) == group(A), where k = base_field(K) and that group(A) is
# abelian.
# Returns a k-linear map from K to A and one from A to K
function _find_isomorphism(K::Union{ AnticNumberField, NfRel{nf_elem} }, A::AlgGrp)
  G = group(A)
  aut = automorphisms(K)

  aut_dict = Dict{elem_type(K), Int}()
  n = length(aut)
  identity = 0
  for i = 1:n
    b = aut[i].prim_img
    aut_dict[b] = i
    if b == gen(K)
      identity = i
    end
  end

  op_array = zeros(Int, n, n)
  for i = 1:n
    for j = i:n
      if i == identity
        k = j
      elseif j == identity
        k = i
      else
        b = aut[i](aut[j].prim_img)
        k = aut_dict[b]
      end
      op_array[i, j] = k
      # It is assumed, that the group is abelian
      op_array[j, i] = k
    end
  end

  function op(i::Int, j::Int)
    return op_array[i, j]
  end

  auttoG, Gtoaut = find_isomorphism([ i for i in 1:n ], op, G)

  alpha = normal_basis(K)
  basis_alpha = Vector{elem_type(K)}(undef, dim(A))
  for (i, g) in enumerate(G)
    f = aut[Gtoaut[g]]
    basis_alpha[A.group_to_base[g]] = f(alpha)
  end

  M = zero_matrix(base_field(K), degree(K), degree(K))
  for i = 1:degree(K)
    a = basis_alpha[i]
    for j = 1:degree(K)
      M[i, j] = coeff(a, j - 1)
    end
  end

  invM = inv(M)

  function KtoA(x::Union{ nf_elem, NfRelElem })
    t = zero_matrix(base_field(K), 1, degree(K))
    for i = 1:degree(K)
      t[1, i] = coeff(x, i - 1)
    end
    y = t*invM
    return A([ y[1, i] for i = 1:degree(K) ])
  end

  function AtoK(x::AlgGrpElem)
    t = matrix(base_field(K), 1, degree(K), coeffs(x))
    y = t*M
    return K(parent(K.pol)([ y[1, i] for i = 1:degree(K) ]))
  end

  return KtoA, AtoK
end
