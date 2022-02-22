export group_algebra, galois_module, group

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

order_type(::AlgGrp{T, S, R}) where { T <: NumFieldElem, S, R } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T)))}
order_type(::Type{AlgGrp{T, S, R}}) where { T <: NumFieldElem, S, R } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T)))}

@doc Markdown.doc"""
    group(A::AlgGrp) -> Group

Returns the group defining $A$.
"""
group(A::AlgGrp) = A.group

has_one(A::AlgGrp) = true

function (A::AlgGrp{T, S, R})(c::Vector{T}; copy::Bool = false) where {T, S, R}
  length(c) != dim(A) && error("Dimensions don't match.")
  return AlgGrpElem{T, typeof(A)}(A, copy ? deepcopy(c) : c)
end

@doc Markdown.doc"""
    multiplication_table(A::AlgGrp; copy::Bool = true) -> Matrix{RingElem}

Given a group algebra $A$ this function returns the multiplication table of
$A$: If the function returns $M$ and the basis of $A$ is $g_1,\dots, g_n$ then
it holds $g_i \cdot g_j = g_{M[i, j]}$.
"""
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

@doc Markdown.doc"""
    group_algebra(K::Ring, G; op = *) -> AlgGrp

Returns the group ring $K[G]$.
$G$ may be any set and `op` a group operation on $G$.
"""
group_algebra(K::Ring, G; op = *) = AlgGrp(K, G, op = op)

group_algebra(K::Ring, G::GrpAbFinGen) = AlgGrp(K, G)

function group_algebra(K::Field, G; op = *)
  A = AlgGrp(K, G, op = op)
  if iszero(characteristic(K))
    A.issemisimple = 1
  else
    A.issemisimple = isone(gcd(characteristic(K), order(G))) ? 1 : 2
  end
  return A
end

function group_algebra(K::Field, G::GrpAbFinGen)
  A = group_algebra(K, G, op = +)
  A.iscommutative = true
  return A
end

@doc Markdown.doc"""
    (K::Ring)[G::Group] -> AlgGrp
    (K::Ring)[G::GrpAbFinGen] -> AlgGrp

Returns the group ring $K[G]$.
"""
getindex(K::Ring, G::Group) = group_algebra(K, G)
getindex(K::Ring, G::GrpAbFinGen) = group_algebra(K, G)

################################################################################
#
#  Commutativity
#
################################################################################

iscommutative_known(A::AlgGrp) = (A.iscommutative != 0)

@doc Markdown.doc"""
    iscommutative(A::AlgGrp) -> Bool

Returns `true` if $A$ is a commutative ring and `false` otherwise.
"""
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

###############################################################################
#
#  Trace basis
#
###############################################################################

function _assure_trace_basis(A::AlgGrp{T}) where {T}
  if isdefined(A, :trace_basis_elem)
    return nothing
  end

  A.trace_basis_elem = Vector{T}(undef, dim(A))
  A.trace_basis_elem[1] = base_ring(A)(dim(A))
  for i = 2:dim(A)
    A.trace_basis_elem[i] = zero(base_ring(A))
  end
  return nothing
end

################################################################################
#
#  Center
#
################################################################################

@doc Markdown.doc"""
    center(A::AlgGrp) -> AlgAss, AbsAlgAssMor

Returns the center $C$ of $A$ and the inclusion $C \to A$.
"""
function center(A::AlgGrp{T}) where {T}
  if isdefined(A, :center)
    return A.center::Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}
  end

  # Unlike for AlgAss, we should cache the centre even if A is commutative
  # since it is of a different type, so A !== center(A)[1].
  # Otherwise center(A)[1] !== center(A)[1] which is really annoying.
  B, mB = AlgAss(A)
  C, mC = center(B)
  mD = compose_and_squash(mB, mC)
  A.center = C, mD
  return (C, mD)::Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}
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
  AtoB = hom(A, B, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
  if isdefined(A, :center)
    Z, ZtoA = center(A)
    B.center = (Z, compose_and_squash(AtoB, ZtoA))
  end
  if isdefined(A, :decomposition)
    dec = Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(B))}[]
    for (C, CtoA) in A.decomposition::Vector{Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}}
      CtoB = compose_and_squash(AtoB, CtoA)
      push!(dec, (C, CtoB))
    end
    B.decomposition = dec
  end
  if isdefined(A, :maps_to_numberfields)
    NF = A.maps_to_numberfields::Vector{Tuple{_ext_type(T),_abs_alg_ass_to_nf_abs_mor_type(A)}}
    fields_and_maps = Tuple{AnticNumberField,_abs_alg_ass_to_nf_abs_mor_type(B)}[]
    for (K, AtoK) in NF
      BtoK = AbsAlgAssToNfAbsMor(B, K, AtoK.mat, AtoK.imat)
      push!(fields_and_maps, (K, BtoK))
    end
    B.maps_to_numberfields = fields_and_maps
  end
  return B, hom(B, A, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
end

################################################################################
#
#  Misc
#
################################################################################

Base.enumerate(G::Generic.SymmetricGroup{T}) where T <: Integer = enumerate(Generic.AllPerms(G.n))

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

@doc Markdown.doc"""
    gens(A::AlgGrp, return_full_basis::Type{Val{T}} = Val{false})
      -> Vector{AlgGrpElem}

Returns a subset of `basis(A)`, which generates $A$ as an algebra over
`base_ring(A)`.
If `return_full_basis` is set to `Val{true}`, the function also returns a
`Vector{AbsAlgAssElem}` containing a full basis consisting of monomials in
the generators and a `Vector{Vector{Tuple{Int, Int}}}` containing the
information on how these monomials are built. E. g.: If the function returns
`g`, `full_basis` and `v`, then we have
`full_basis[i] = prod( g[j]^k for (j, k) in v[i] )`.
"""
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
    b = image_primitive_element(aut[i])
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
        b = aut[i](image_primitive_element(aut[j]))
        k = aut_dict[b]
      end
      op_array[i, j] = k
      # It is assumed, that the group is abelian
      op_array[j, i] = k
    end
  end

  local op
  let op_array = op_array
    function op(iiii::Int, jjjj::Int)
      return op_array[iiii, jjjj]
    end
  end

  auttoG, Gtoaut = find_isomorphism(Int[ i for i in 1:n ], op, G)

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

  local KtoA
  let K = K, invM = invM, A = A
    function KtoA(x::Union{ nf_elem, NfRelElem })
      t = zero_matrix(base_field(K), 1, degree(K))
      for i = 1:degree(K)
        t[1, i] = coeff(x, i - 1)
      end
      y = t*invM
      return A([ y[1, i] for i = 1:degree(K) ])
    end
  end

  local AtoK
  let K = K, M = M
    function AtoK(x::AlgGrpElem)
      t = matrix(base_field(K), 1, degree(K), coefficients(x))
      y = t*M
      return K(parent(K.pol)([ y[1, i] for i = 1:degree(K) ]))
    end
  end

  return KtoA, AtoK
end

mutable struct NfToAlgGrpMor{S, T, U} <: Map{AnticNumberField, AlgGrp{S, T, U}, HeckeMap, AbsAlgAssMor}
  K::AnticNumberField
  mG::GrpGenToNfMorSet{NfToNfMor, AnticNumberField}
  A::AlgGrp{S, T, U}
  M::fmpq_mat
  Minv::fmpq_mat

  function NfToAlgGrpMor{S, T, U}() where {S, T, U}
    return new{S, T, U}()
  end
end

function show(io::IO, f::NfToAlgGrpMor)
  print(io, "Galois module map from\n")
  print(io, f.K)
  print(io, "\nto\n")
  print(io, f.A)
end

function (f::NfToAlgGrpMor)(O::NfAbsOrd)
  A = codomain(f)
  B = basis(O)
  G = group(A)
  ZG = Order(A, collect(G))
  return ideal_from_lattice_gens(A, ZG, [f(elem_in_nf(b)) for b in B], :right)
end

automorphism_map(f::NfToAlgGrpMor) = f.mG

function galois_module(K::AnticNumberField, aut::Map = automorphism_group(K)[2]; normal_basis_generator = normal_basis(K))
  G = domain(aut)
  A = FlintQQ[G]
  return _galois_module(K, A, aut, normal_basis_generator = normal_basis_generator)
end

function _galois_module(K::AnticNumberField, A, aut::Map = automorphism_group(K)[2]; normal_basis_generator = normal_basis(K))
  G = domain(aut)
  alpha = normal_basis_generator

  basis_alpha = Vector{elem_type(K)}(undef, dim(A))
  for (i, g) in enumerate(G)
    f = aut(g)
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

  z = NfToAlgGrpMor{fmpq, GrpGen, GrpGenElem}()
  z.K = K
  z.mG = aut
  z.A = A
  z.M = M
  z.Minv = invM

  return A, z
end

function galois_module(K::AnticNumberField, A::AlgGrp; normal_basis_generator = normal_basis(K))
  G = group(A)
  Au, mAu = automorphism_group(K)
  fl, f = isisomorphic(G, Au)
  @assert fl
  aut = Vector{NfToNfMor}(undef, order(G))
  for g in G
    aut[g[]] = mAu(f(g))
  end
  h = GrpGenToNfMorSet(G, aut, K)

  return _galois_module(K, A, h, normal_basis_generator = normal_basis(K))
end

domain(f::NfToAlgGrpMor) = f.K

codomain(f::NfToAlgGrpMor) = f.A

function image(f::NfToAlgGrpMor, x::nf_elem)
  K = domain(f)
  @assert parent(x) === K
  A = codomain(f)

  t = zero_matrix(base_field(K), 1, degree(K))
  for i = 1:degree(K)
    t[1, i] = coeff(x, i - 1)
  end
  y = t*f.Minv
  return A([ y[1, i] for i = 1:degree(K) ])
end

function preimage(f::NfToAlgGrpMor, x::AlgGrpElem)
  K = domain(f)
  t = matrix(base_field(K), 1, degree(K), coefficients(x))
  y = t*f.M
  v = fmpq[ y[1, i] for i = 1:degree(K) ]
  return K(v)
end

# Returns the group algebra Q[G] where G = Gal(K/Q) and a Q-linear map from K
# to Q[G] and one from Q[G] to K
function _galois_module(K::AnticNumberField, to_automorphisms::Map = automorphism_group(K)[2]; normal_basis_generator = normal_basis(K))
  G = domain(to_automorphisms)
  A = FlintQQ[G]
  alpha = normal_basis_generator

  basis_alpha = Vector{elem_type(K)}(undef, dim(A))
  for (i, g) in enumerate(G)
    f = to_automorphisms(g)
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

  function KtoA(x::nf_elem)
    t = zero_matrix(base_field(K), 1, degree(K))
    for i = 1:degree(K)
      t[1, i] = coeff(x, i - 1)
    end
    y = t*invM
    return A([ y[1, i] for i = 1:degree(K) ])
  end

  function AtoK(x::AlgGrpElem)
    t = matrix(base_field(K), 1, degree(K), coefficients(x))
    y = t*M
    return K(parent(K.pol)([ y[1, i] for i = 1:degree(K) ]))
  end

  return A, KtoA, AtoK
end

const _reps = [(i=24,j=12,n=5,dims=(1,1,2,3,3),
                reps=Vector{Vector{Rational{BigInt}}}[[[1],[1],[1],[1]],
                  [[-1],[1],[1],[1]],
                  [[-1,0,-1,1],[0,-1,1,-1],[1,0,0,1],[1,0,0,1]],
                  [[0,1,0,1,0,0,0,0,1],[0,0,1,1,0,0,0,1,0],[-1,0,0,0,1,0,0,0,-1],[1,0,0,0,-1,0,0,0,-1]],
                  [[0,-1,0,-1,0,0,0,0,-1],[0,0,1,1,0,0,0,1,0],[-1,0,0,0,1,0,0,0,-1],[1,0,0,0,-1,0,0,0,-1]]]),
               (i=48,j=48,n=10,dims=Int[1,1,1,1,2,2,3,3,3,3],
                reps=Vector{Vector{Rational{BigInt}}}[[[1],[1],[1],[1],[1]],[[-1],[1],[1],[1],[1]],[[1],[-1],[1],[1],[1]],[[-1],[-1],[1],[1],[1]],[[-1,0,-1,1],[-1,0,0,-1],[0,-1,1,-1],[1,0,0,1],[1,0,0,1]],[[1,3//2,0,-1],[1,0,0,1],[1,3//2,-2,-2],[1,0,0,1],[1,0,0,1]],[[0,1,0,1,0,0,0,0,1],[1,0,0,0,1,0,0,0,1],[0,0,1,1,0,0,0,1,0],[-1,0,0,0,1,0,0,0,-1],[1,0,0,0,-1,0,0,0,-1]],[[0,-1,0,-1,0,0,0,0,-1],[1,0,0,0,1,0,0,0,1],[0,0,1,1,0,0,0,1,0],[-1,0,0,0,1,0,0,0,-1],[1,0,0,0,-1,0,0,0,-1]],[[0,1,0,1,0,0,0,0,1],[-1,0,0,0,-1,0,0,0,-1],[0,0,1,1,0,0,0,1,0],[-1,0,0,0,1,0,0,0,-1],[1,0,0,0,-1,0,0,0,-1]],[[0,-1,0,-1,0,0,0,0,-1],[-1,0,0,0,-1,0,0,0,-1],[0,0,1,1,0,0,0,1,0],[-1,0,0,0,1,0,0,0,-1],[1,0,0,0,-1,0,0,0,-1]]])
              ]

################################################################################
#
#  Wedderburn decomposition
#
################################################################################

mutable struct AbsAlgAssMorGen{S, T, U, V} <: Map{S, T, HeckeMap, AbsAlgAssMorGen}
  domain::S
  codomain::T
  tempdomain::U
  tempcodomain::V
  tempcodomain2::V
  tempcodomain_threaded::Vector{V}
  tempcodomain2_threaded::Vector{V}

  M::U
  Minv::V

  function AbsAlgAssMorGen{S, T, U, V}(domain::S, codomain::T, M::U, Minv::V) where {S, T, U, V}
    z = new{S, T, U, V}()
    z.domain = domain
    z.codomain = codomain
    z.M = M
    z.tempcodomain = zero_matrix(base_ring(Minv), 1, nrows(Minv))
    z.tempcodomain2 = zero_matrix(base_ring(Minv), 1, ncols(Minv))
    z.tempcodomain_threaded = [zero_matrix(base_ring(Minv), 1, nrows(Minv)) for i in 1:Threads.nthreads()]
    z.tempcodomain2_threaded = [zero_matrix(base_ring(Minv), 1, ncols(Minv)) for i in 1:Threads.nthreads()]

    z.Minv = Minv
    return z
  end
end

function AbsAlgAssMorGen(dom, codom, M, Minv)
  return AbsAlgAssMorGen{typeof(dom), typeof(codom), typeof(M), typeof(Minv)}(dom, codom, M, Minv)
end

#function AbsAlgAssMorGen(A::S, B::T, M::U, N::V) where {S, T, U, V}
#  return AbsAlgAssMorGen{S, T, U, V}(A, B, M, N)
#end

domain(f::AbsAlgAssMorGen) = f.domain

codomain(f::AbsAlgAssMorGen) = f.codomain

function Base.show(io::IO, f::AbsAlgAssMorGen)
  print(io, "Algebra morphism from \n$(domain(f))\n to\n$(codomain(f))\n")
end

function image(f::AbsAlgAssMorGen, z)
  @assert parent(z) == domain(f)
  v = base_ring(codomain(f)).(coefficients(z))
  return codomain(f)(v * f.M)
end

(f::AbsAlgAssMorGen)(z::AbsAlgAssElem) = image(f, z)

function preimage(f::AbsAlgAssMorGen, z)
  @assert parent(z) === codomain(f)
  if Threads.nthreads() > 1
    ftc = f.tempcodomain_threaded[Threads.threadid()]
    ftc2 = f.tempcodomain2_threaded[Threads.threadid()]
  else
    ftc = f.tempcodomain
    ftc2 = f.tempcodomain2
  end

  _coefficients_of_restricted_scalars!(ftc, z)
  mul!(ftc2, ftc, f.Minv)
  v = Vector{eltype(ftc)}(undef, ncols(ftc2))
  for i in 1:length(v)
    @inbounds v[i] = @inbounds ftc2[1, i]
  end
  return domain(f)(v, copy = false)
end

# Write M_n(K) as M_n(Q) if [K : Q] = 1
# We use the "restricted scalar map" to modell M_n(Q) -> M_n(K)
function _as_full_matrix_algebra_over_Q(A::AlgMat{nf_elem})
  K = base_ring(A)
  @assert isabsolute(K) && degree(K) == 1
  B = matrix_algebra(FlintQQ, degree(A))

  M = identity_matrix(K, dim(B))
  Minv = identity_matrix(FlintQQ, dim(B))

  return B, AbsAlgAssMorGen(B, A, M, Minv)
end

################################################################################
#
#  Central primitive idempotents
#
################################################################################

# This is Corollary 2.1 of
# Eric Jespers, Guilherme Leal and Antonio Paques
# Central idempotents in the rational group algebra of a finite nilpotent group
# https://www.worldscientific.com/doi/10.1142/S0219498803000398
function _central_primitive_idempotents_abelian(A::AlgGrp)
  G = group(A)
  @assert base_ring(A) isa FlintRationalField
  @assert isabelian(G)
  S = subgroups(G, fun = (x, m) -> sub(x, m, false))
  o = one(A)
  idem = elem_type(A)[]
  push!(idem, 1//order(G) * sum(basis(A)))
  for (s, ms) in S
    Q, mQ = quo(G, ms, false)
    if !iscyclic(Q)
      continue
    end
    e = 1//(order(s)) * sum([A(ms(x)) for x in s])
    M = minimal_subgroups(Q, false)
    for (H, mH) in M
      U, mU = sub(G, append!([mQ\(mH(x)) for x in gens(H)], [ms(x) for x in gens(s)]))
      uhat = 1//(order(U)) * sum([A(mU(x)) for x in U])
      e = e * (o - uhat)
    end
    push!(idem, e)
  end
  return idem
end

function __decompose_abelian_group_algebra(A::AlgGrp)
  T = elem_type(base_ring(A))
  idems = _central_primitive_idempotents_abelian(A)
  res = Vector{Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}}()
  for idem in idems
    S, StoA = subalgebra(A, idem, true)
    S.issimple = 1
    push!(res, (S, StoA))
  end
  return res
end

function decompose(A::AlgGrp)
  T = elem_type(base_ring(A))
  if isdefined(A, :decomposition)
    return A.decomposition::Vector{Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}}
  end
  if group(A) isa GrpAbFinGen && (base_ring(A) isa FlintRationalField)
    res = __decompose_abelian_group_algebra(A)
    A.decomposition = res
    return res
  end
  G = group(A)
  res = __decompose(A)

  #if !isdefined(res[1][1], :isomorphic_full_matrix_algebra)
  #  if order(G) == 24 && find_small_group(G)[1] == (24, 12) &&
  #      base_ring(A) isa FlintRationalField
  #    @assert G.isfromdb
  #    _compute_matrix_algebras_from_reps(A, res, _reps[1])
  #  end
  #
  #  if order(G) == 48 && find_small_group(G)[1] == (48, 48) &&
  #      base_ring(A) isa FlintRationalField
  #    @assert G.isfromdb
  #    _compute_matrix_algebras_from_reps(A, res, _reps[2])
  #  end
  #end

  return res
end

function _compute_matrix_algebras_from_reps2(A, res)
  G = group(A)
  smallid, H, HtoG = find_small_group(G)
  idempotents = elem_type(A)[r[2](one(r[1])) for r in res]
  data = DefaultSmallGroupDB().db[smallid[1]][smallid[2]]
  Qx = Globals.Qx
  for j in data.galrep
    #@show j, data.schur[j]
    if data.schur[j] != 1
      continue
    end
    field, _ = number_field(Qx(data.fields[j]), "a", cached = false)
    d = data.dims[j]
    mats = dense_matrix_type(nf_elem)[ matrix(field, d, d, map(field, data.mod[j][k])) for k in 1:length(data.mod[j])]
    D = Tuple{GrpGenElem, dense_matrix_type(nf_elem)}[(H[H.gens[i]], mats[i]) for i in 1:length(H.gens)]
    op = (x, y) -> (x[1] * y[1], x[2] * y[2])
    id = (Hecke.id(H), identity_matrix(field, d))
    cl = closure(D, op, id)

    k0 = 0
    for k in 1:length(idempotents)
      c = coefficients(idempotents[k])
      z = zero_matrix(field, d, d)
      for (h, M) in cl
        i = A.group_to_base[HtoG(h)]
        z += field(c[i]) * M
      end
      if isone(z)
        k0 = k
        break
      end
    end

    #@show k0

    B, mB = res[k0]
    basisB = basis(B)

    MB = matrix_algebra(field, d)

    forward_matrix = zero_matrix(field, dim(B), dim(MB))

    back_matrix = zero_matrix(FlintQQ, dim(B), dim(B))

    BinMB = elem_type(MB)[]

    for i in 1:dim(B)
      img = MB(_evaluate_rep(mB(basisB[i]), d, cl, HtoG))
      push!(BinMB, img)
      elem_to_mat_row!(forward_matrix, i, img)
      v = _coefficients_of_restricted_scalars(img)
      for j in 1:length(v)
        back_matrix[i, j] = v[j]
      end
    end

    back_matrix = inv(back_matrix)



    # now comes the horror
    #
    #
    #@show back_matrix

    #v = matrix(FlintQQ, 1, dim(B), coefficients(rand(B, -10:10)))
    #@show v
    #@show matrix(FlintQQ, 1, dim(B), _coefficients_of_restricted_scalars(MB(collect(change_base_ring(field, v) * forward_matrix)))) * back_matrix

    #BtoMB = function(z)
    #  v = matrix(base_ring(MB), 1, dim(B), coefficients(z))
    #  return MB(collect(v * forward_matrix))
    #end

    #MBtoB = function(z)
    #  v = matrix(FlintQQ, 1, dim(B), _coefficients_of_restricted_scalars(z)) * back_matrix
    #  return B(collect(v))
    #end

    #println("Adding to $k0: $MB")
    f = AbsAlgAssMorGen(B, MB, forward_matrix, back_matrix)
    B.isomorphic_full_matrix_algebra = MB, f
  end
end

function _compute_matrix_algebras_from_reps(A, res, reps)
  G = group(A)
  idempotents = elem_type(A)[r[2](one(r[1])) for r in res]
  for j in 1:reps.n
    d = reps.dims[j]
    @assert length(reps.reps[j]) == length(G.gens)
    mats = fmpq_mat[ matrix(FlintQQ, d, d, reps.reps[j][k]) for k in 1:length(reps.reps[j])]
    D = Tuple{GrpGenElem, fmpq_mat}[(G[G.gens[i]], mats[i]) for i in 1:length(G.gens)]
    op = (x, y) -> (x[1] * y[1], x[2] * y[2])
    id = (Hecke.id(G), identity_matrix(FlintQQ, d))
    cl = closure(D, op, id)
    @assert length(cl) == order(G)
    k0 = 0
    for k in 1:length(idempotents)
      e = idempotents[k]
      c = coefficients(e)
      z = _evaluate_rep(e, d, cl)
      if isone(z)
        k0 = k
        break
      end
    end

    @assert k0 != 0

    B, mB = res[k0]

    @assert dim(B) == d^2

    basisB = basis(B)

    MB = matrix_algebra(FlintQQ, d)

    h = zero_matrix(FlintQQ, d^2, d^2)

    for i in 1:dim(B)
      img = MB(_evaluate_rep(mB(basisB[i]), d, cl))
      elem_to_mat_row!(h, i, img)
    end
    B.isomorphic_full_matrix_algebra = (MB, hom(B, MB, h, inv(h)))
  end
end

function _coefficients_of_restricted_scalars!(y, x)
  A = parent(x)
  K = base_ring(A)
  m = dim(A)
  n = degree(K)
  nm = n * m
  yy = coefficients(x, copy = false)
  k = 1
  for i = 1:m
    for j = 1:n
      __set!(y, k, coeff(yy[i], j - 1))
      #y[k] = coeff(yy[i], j - 1)
      k += 1
    end
  end
  return y
end

function __set_row!(y::fmpq_mat, k, c)
  GC.@preserve y
  begin
    for i in 1:length(c)
      t = ccall((:fmpq_mat_entry, libflint), Ptr{fmpq}, (Ref{fmpq_mat}, Int, Int), y, k - 1, i - 1)
      ccall((:fmpq_set, libflint), Cvoid, (Ptr{fmpq}, Ref{fmpq}), t, c[i])
    end
  end
  nothing
end

function __set_row!(c::Vector{fmpq}, y::fmpq_mat, k)
  GC.@preserve y
  begin
    for i in 1:length(c)
      t = ccall((:fmpq_mat_entry, libflint), Ptr{fmpq}, (Ref{fmpq_mat}, Int, Int), y, k - 1, i - 1)
      ccall((:fmpq_set, libflint), Cvoid, (Ref{fmpq}, Ptr{fmpq}), c[i], t)
    end
  end
  nothing
end

function __set!(y, k, c)
  GC.@preserve y begin
    t = ccall((:fmpq_mat_entry, libflint), Ptr{fmpq}, (Ref{fmpq_mat}, Int, Int), y, 0, k - 1)
    ccall((:fmpq_set, libflint), Cvoid, (Ptr{fmpq}, Ref{fmpq}), t, c)
  end
  nothing
end

function _coefficients_of_restricted_scalars!(y::Vector, x)
  A = parent(x)
  K = base_ring(A)
  m = dim(A)
  n = degree(K)
  nm = n * m
  yy = coefficients(x, copy = false)
  k = 1
  for i = 1:m
    for j = 1:n
      y[k] = coeff(yy[i], j - 1)
      k += 1
    end
  end
  return y
end

function _coefficients_of_restricted_scalars(x)
  A = parent(x)
  K = base_ring(A)
  m = dim(A)
  n = degree(K)
  nm = n * m
  y = Vector{fmpq}(undef, nm)
  return _coefficients_of_restricted_scalars!(y, x)
end

function _absolute_basis(A)
  m = dim(A)
  K = base_ring(A)
  n = degree(K)
  B = Vector{elem_type(A)}()
  bK = basis(K)
  for i in 1:n
    for j in 1:m
      v = Vector{elem_type(K)}(undef, m)
      for k in 1:m
        v[i] = zero(K)
      end
      v[j] = bK[j]
      push!(B, A(v))
    end
  end
  return B
end

function _evaluate_rep(el, d, rep)
  c = coefficients(el)
  A = parent(el)
  z = zero_matrix(FlintQQ, d, d)
  for (g, M) in rep
    i = A.group_to_base[g]
    z += c[i] * M
  end
  return z
end

function _evaluate_rep(el, d, rep, f)
  c = coefficients(el)
  A = parent(el)
  z = zero_matrix(base_ring(rep[1][2]), d, d)
  for (g, M) in rep
    i = A.group_to_base[f(g)]
    z += base_ring(M)(c[i]) * M
  end
  return z
end

elem_type(::Type{NfMorSet{AnticNumberField}}) = NfToNfMor

################################################################################
#
#  Opposite algebra
#
################################################################################

function opposite_algebra(A::AlgGrp{S, GrpAbFinGen, GrpAbFinGenElem}) where S
  G = group(A)
  z = zero_matrix(base_ring(A), dim(A), dim(A))
  for g in G
    i = A.group_to_base[g]
    elem_to_mat_row!(z, i, A(-g))
  end
  return A, hom(A, A, z, z)
end

function opposite_algebra(A::AlgGrp{S, GrpGen, GrpGenElem}) where S
  G = group(A)
  z = zero_matrix(base_ring(A), dim(A), dim(A))
  for g in G
    i = A.group_to_base[g]
    elem_to_mat_row!(z, i, A(inv(g)))
  end
  return A, hom(A, A, z, z)
end

################################################################################
#
#  Ad hoc methods
#
################################################################################

function isfree_s4_fabi(K::AnticNumberField)
  if istamely_ramified(K, fmpz(2))
    println("fabi 1")
    return true
  end

  P = prime_decomposition(maximal_order(K), 2)[1][1]

  D = decomposition_group(P)

  if length(D) == 24 && isweakly_ramified(K, P)
    println("fabi 2")
    return true
  end

  G, _, _ = generic_group(D, *, false)
  id, _, _ = find_small_group(G)
  if id == (12, 3) # A4
    println("fabi 3")
    return true
  end

  if id == (8, 3) # D4
    if isweakly_ramified(K, P)
      A, mA = automorphism_group(K)
      I, mI = inertia_subgroup(K, P, mA)
      fl = _isnormal([mI(i) for i in I])
      if order(I) == 4 && fl
        println("fabi 4")
        return true
      end
    end
  end

  return false
end

function isfree_a4_fabi(K::AnticNumberField)
  if istamely_ramified(K, fmpz(2))
    println("fabi 1")
    return true
  end

  P = prime_decomposition(maximal_order(K), 2)[1][1]

  D = decomposition_group(P)

  if length(D) == 12
    println("fabi 2")
    return true
  end

  return false
end

function isfree_a5_fabi(K::AnticNumberField)
  if !istamely_ramified(K, fmpz(2))
    println("fabi 1")
    return false
  end

  if !(istamely_ramified(K, fmpz(3)) || !isalmost_maximally_ramified(K, fmpz(3)))
    println("fabi 2")
    return false
  end

  if !(istamely_ramified(K, fmpz(5)) || !isalmost_maximally_ramified(K, fmpz(5)))
    println("fabi 3")
    return false
  end

  return true
end

function isalmost_maximally_ramified(K::AnticNumberField, p::fmpz)
  P = prime_decomposition(maximal_order(K), p)[1][1]
  G, mG = automorphism_group(K)
  D, mD = decomposition_group(K, P, mG) # this is the local Galois group
  ram_groups = []
  t = 1
  while true
    R, mR = ramification_group(K, P, t, mG)
    push!(ram_groups, [mR(r) for r in R])
    if order(R) == 1
      break
    end
    t += 1
  end

  QG = group_algebra(FlintQQ, G)
  A, KtoA = galois_module(K)
  I = KtoA(maximal_order(K))
  assOrd = right_order(I)

  S = subgroups(D)
  for (H, mH) in S
    HinG = [ mD(mH(h)) for h in H]
    for t in 1:length(ram_groups)
      if all(h in ram_groups[t] for h in HinG) && all(h in HinG for h in ram_groups[t + 1])
        eH = sum(QG(h) for h in HinG) * QG(1//Order(H))
        if !(eH in assOrd)
          return false
        end
      end
    end
  end

  return true
end

function hom(KG::AlgGrp, KH::AlgGrp, m::GrpGenToGrpGenMor)
  @assert base_ring(KG) === base_ring(KH)
  K = base_ring(KG)
  M = zero_matrix(K, dim(KG), dim(KH))
  for i in 1:dim(KG)
    j = KH.group_to_base[m(KG.base_to_group[i])]
    M[i, j] = one(K)
  end
  return hom(KG, KH, M)
end
