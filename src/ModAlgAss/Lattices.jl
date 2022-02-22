################################################################################
#
#  Lattices
#
################################################################################

mutable struct ModAlgAssLat{S, T, U}
  base_ring::S
  V::T
  basis::U
  basis_inv::U

  function ModAlgAssLat{S, T, U}(base_ring::S, V::T, basis::U) where {S, T, U}
    z = new{S, T, U}()
    z.base_ring = base_ring
    z.V = V
    z.basis = basis
    return z
  end
end

#ModAlgAssLat(base_ring::S, V::T, basis::U) where {S, T, U} = ModAlgAssLat{S, T, U}(base_ring, V, basis)

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, L::ModAlgAssLat)
  print(io, "Lattice of rank ", rank(L), " over ", base_ring(L.base_ring))
end

function _defines_lattice(V::ModAlgAss, O, B)
  Binv = inv(B)
  for g in basis(O)
    T = action(V, elem_in_algebra(g))
    BB = B * T * Binv
    if !isone(abs(denominator(BB)))
      return false
    end
  end
  return true
end

################################################################################
#
#  Lattice arithmetic
#
################################################################################

function _hnf_nonzero(a::fmpq_mat)
  b = fmpq_mat(hnf(FakeFmpqMat(a)))
  i = 1
  while iszero_row(b, i)
    i += 1
  end
  return b[i:nrows(b), 1:ncols(b)]
end

function *(m::Int, L::ModAlgAssLat)
  return lattice(L.V, L.base_ring, _hnf_nonzero(m * basis_matrix(L)))
end

function +(L::T, M::T) where {T <: ModAlgAssLat}
  @req L.base_ring === M.base_ring "Lattices must be defined over the same order"
  @req L.V === M.V "Lattices must have same ambient module"
  return lattice(L.V, L.base_ring, _hnf_nonzero(vcat(basis_matrix(L),
                                                     basis_matrix(M))))
end

function intersect(L::T, M::T) where {T <: ModAlgAssLat}
  @req L.base_ring === M.base_ring "Lattices must be defined over the same order"
  @req L.V === M.V "Lattices must have same ambient module"
  BM = basis_matrix(M)
  BN = basis_matrix(N)
  dM = denominator(BM)
  dN = denominator(BN)
  d = lcm(dM, dN)
  BMint = change_base_ring(FlintZZ, d * BM)
  BNint = change_base_ring(FlintZZ, d * BN)
  H = vcat(BMint, BNint)
  k, K = left_kernel(H)
  BI = divexact(change_base_ring(FlintQQ, hnf(view(K, 1:k, 1:nrows(BM)) * BMint)), d)
  return lattice(L.V, L.base_ring, BI)
end

################################################################################
#
#  Z-lattices
#
################################################################################

Markdown.doc"""
    lattice(V::ModAlgAss, O::AlgAssAbsOrd, B::MatElem)

Given a module with matrix action over a $\mathbf{Q}$-algebra $A$, a
$\mathbf{Z}$-order of $A$, return the lattice with $O$-lattice basis matrix $B$.
"""
function lattice(V::ModAlgAss{FlintRationalField}, O::AlgAssAbsOrd, B::MatElem; check::Bool = true)
  if B isa fmpq_mat
    return _lattice(V, O, B, check = check)
  else
    return _lattice(V, O, change_base_ring(QQ, B)::fmpq_mat, check = check)
  end
end

# internal function to construct lattice
function _lattice(V::ModAlgAss{FlintRationalField}, O::AlgAssAbsOrd, B::fmpq_mat; check::Bool = true, ishnf::Bool = false)
  if check
    fl = _defines_lattice(V, O, B)
    @req fl "Z-lattice with this basis matrix is not invariant under order"
  end

  @hassert :ModLattice _defines_lattice(V, O, B)

  if !ishnf
    BB = fmpq_mat(hnf!(FakeFmpqMat(B), :upperright))
  else
    BB = B
  end
  return ModAlgAssLat{typeof(O), typeof(V), typeof(BB)}(O, V, BB)
end

rank(L::ModAlgAssLat) = nrows(basis_matrix(L))

################################################################################
#
#  Basis matrix
#
################################################################################

function basis_matrix(L::ModAlgAssLat)
  @req base_ring(L.base_ring) isa FlintIntegerRing "Order of lattice must be a Z-order"
  @req hasmatrix_action(L.V) "Action on module must be given by matrices"
  return L.basis
end

function basis_matrix_inverse(L::ModAlgAssLat)
  @req base_ring(L.base_ring) isa FlintIntegerRing "Order of lattice must be a Z-order"
  @req hasmatrix_action(L.V) "Action on module must be given by matrices"
  if isdefined(L, :basis_inv)
    return L.basis_inv
  else
    M = inv(basis_matrix(L))
    L.basis_inv = M
    return M
  end
end

################################################################################
#
#  Reduction
#
################################################################################

@doc Markdown.doc"""
    reduction(L::ModAlgAssLat, p::IntegerUnion) -> ModAlgAss

Given an $L$ over an $\mathbf{Z}$-order and a prime $p$, return the module $L/pL$
over the field $\mathbf{F}_p$.

Note that the module will be defined without algebra and the action will be
given by $\rank(O)$ many generators. To obtain a module for the
$\mathbf{F}_p$-algebra $O/pO$, the algebra first has to be constructed using
`reduction(O, p)`.

See also `change_coefficient_ring`.
"""
function reduction(L::ModAlgAssLat, p::IntegerUnion)
  @req base_ring((L.base_ring)) isa FlintIntegerRing "Order must be a Z-order"
  F = GF(p, cached = false)
  a = action_of_basis(L)
  amodp = map(m -> change_base_ring(F, m), a)
  return Module(amodp)
end

@doc Markdown.doc"""
    change_coefficient_ring(R::Ring, L::ModAlgAssLat{FlintIntegerRing}) -> ModAlgAss

Given a lattice $L$ over an $\mathbf{Z}$-order $L$, return the $L \otimes R$
over the ring $R$.

Note that the module will be defined without algebra and the action will be
given by $\rank(O)$ many generators.
"""
function change_coefficient_ring(R::Ring, L::ModAlgAssLat)
  @req base_ring((L.base_ring)) isa FlintIntegerRing "Order must be a Z-order"
  a = action_of_basis(L)
  aR = map(m -> change_base_ring(R, m), a)
  return Module(aR)
end

@doc Markdown.doc"""
    action(L::ModAlgAssLat, x)

Given a lattice $L$ over an order $O$ and an element $x$ of $O$, return
the matrix with which $x$ is acting on $L$.
"""
function action(L::ModAlgAssLat, x)
  T = basis_matrix(L)
  Tinv = basis_matrix_inverse(L)
  M = T * action(L.V, elem_in_algebra(x))
  mul!(M, M, Tinv)
  return M
end

function action_of_basis(L::ModAlgAssLat)
  A = action_of_order_basis(L.V, L.base_ring)
  T = basis_matrix(L)
  Tinv = basis_matrix_inverse(L)
  res = Vector{eltype(A)}(undef, length(A))
  for i in 1:length(res)
    M = T * A[i]
    res[i] = mul!(M, M, Tinv)
  end
  return res
end

#function algebra(M::Vector{T}) where {T <: MatElem}
#  @assert length(M) > 0
#  A = M[1]
#  n = nrows(A)
#  n2 = n^2
#  @assert n == ncols(A)
#  K = base_ring(A)
#  Mprod = M
#  Morig = copy(M)
#
#  current_dim = -1
#
#  B = zero_matrix(K, length(Mprod) + 1, n2)
#
#  l = 0
#  while true
#    if l != 0
#      B = zero_matrix(K, length(Mprod), n2)
#    end
#    for k in 1:length(Mprod)
#      for i in 1:n
#        for j in 1:n
#          B[k, (i - 1)* n  + j] = Mprod[k][i, j]
#        end
#      end
#    end
#    # Add the identity
#    if l == 0
#      for i in 1:n
#        B[length(M) + 1, (i - 1)*n + i] = one(K)
#      end
#    end
#    new_dim = rref!(B)
#    if new_dim == current_dim
#      break
#    end
#    current_dim = new_dim
#    M = [ matrix(K, n, n, [B[k, (i - 1)*n + j] for i in 1:n for j in 1:n]) for k in 1:new_dim]
#    Mprod = [ M[i] * M[j] for i in 1:length(M) for j in 1:length(M) ]
#    l = l + 1
#  end
#
#  dim = current_dim
#  B = sub(B, 1:dim, 1:ncols(B))
#
#  basis = [ matrix(K, n, n, [B[k, (i - 1)*n + j] for i in 1:n for j in 1:n]) for k in 1:dim]
#
#  @assert isone(basis[1])
#
#  v = zero_matrix(K, 1, n2)
#
#  structure = Array{elem_type(K), 3}(dim, dim, dim)
#
#  for k in 1:dim
#    for l in 1:dim
#      N = basis[k] * basis[l]
#      for i in 1:n
#        for j in 1:n
#          v[1, (i - 1)* n  + j] = N[i, j]
#        end
#      end
#      b, u = can_solve_with_solution(B, v, side = :left)
#      error("NOT HERE!")
#      @assert b
#      @assert N == sum(u[i]*basis[i] for i in 1:dim)
#      for m in 1:dim
#        structure[k, l, m] = u[m, 1]
#      end
#    end
#  end
#
#  A = AlgAss(K, structure)
#
#  gens = Vector{AlgAssElem{elem_type(K)}}(length(Morig))
#
#  for l in 1:length(Morig)
#    N = Morig[l]
#    for i in 1:n
#      for j in 1:n
#        v[1, (i - 1)* n  + j] = N[i, j]
#      end
#    end
#    b, u = can_solve_with_solution(B, v, side = :left)
#    gens[l] =  A([u[1, m] for m in 1:dim])
#  end
#
#  A.gens = gens
#
#  return A
#end

#function gens(A::AlgAss{T}) where {T}
#  #return A.gens::Vector{AlgAssElem{T}}
#end

##

function natural_lattice(O::AlgAssAbsOrd{<:AlgMat{fmpq, fmpq_mat}})
  A = algebra(O)
  if all(x -> isone(denominator(matrix(elem_in_algebra(x)))), basis(O, copy = false))
    return lattice(Module(A, matrix.(basis(A))), O, identity_matrix(QQ, degree(algebra(O))))
  else
    error("Order is not contained in M_n(Z)")
  end
end

################################################################################
#
#  Local isomorphism
#
################################################################################

function islocally_isomorphic_with_isomophism(L::ModAlgAssLat, M::ModAlgAssLat, p::fmpz)
  @req L.base_ring === M.base_ring "Orders of lattices must agree"
  @req base_ring(L.base_ring) isa FlintIntegerRing "Order must be a Z-order"
  return _islocally_isomorphic_with_isomophism(L, M, p, Val{true})
end

function islocally_isomorphic(L::ModAlgAssLat, M::ModAlgAssLat, p::fmpz)
  @req L.base_ring === M.base_ring "Orders of lattices must agree"
  @req base_ring(L.base_ring) isa FlintIntegerRing "Order must be a Z-order"
  return _islocally_isomorphic_with_isomophism(L, M, p, Val{false})
end

function _islocally_isomorphic_with_isomophism(L::ModAlgAssLat, M::ModAlgAssLat, p::fmpz, with_isomorphism::Type{Val{S}} = Val{true}) where {S}
  @req L.base_ring === M.base_ring "Orders of lattices must agree"
  @req base_ring(L.base_ring) isa FlintIntegerRing "Order must be a Z-order"
  # We are assuming that L.V === M.V is absolutely irreducible
  # I will not even check this.
  # TODO: Relax this, Tommy knows how to do this 
  @assert L.V === M.V
  T = basis_matrix(L) * basis_matrix_inverse(M)
  d = denominator(T)
  T = d * T
  if with_isomorphism === Val{true}
    fl = iszero(valuation(det(T), p))
    if fl
      error("Tell the developers to finally do it!")
    else
      return false, T
    end
  else
    return iszero(valuation(det(T), p))
  end
end

function _lift_to_Q(K::gfp_mat)
  z = zero_matrix(QQ, nrows(K), ncols(K))
  for i in 1:nrows(K)
    for j in 1:ncols(K)
      u = K[i, j].data
      if iszero(u)
        continue
      else
        z[i, j] = u
      end
    end
  end
  return z
end

function _lift_to_Q!(z, K::gfp_mat)
  for i in 1:nrows(K)
    for j in 1:ncols(K)
      u = K[i, j].data
      if iszero(u)
        continue
      else
        z[i, j] = u
      end
    end
  end
  return z
end

function addmul!(A::gfp_mat, B::gfp_mat, C::gfp_elem, D::gfp_mat)
  ccall((:nmod_mat_scalar_addmul_ui, libflint), Cvoid, (Ref{gfp_mat}, Ref{gfp_mat}, Ref{gfp_mat}, UInt), A, B, D, C.data)
  return A
end

function mul!(A::gfp_mat, B::gfp_elem, D::gfp_mat)
  ccall((:nmod_mat_scalar_mul_ui, libflint), Cvoid, (Ref{gfp_mat}, Ref{gfp_mat}, UInt), A, C, B.data)
end

function pmaximal_sublattices(L::ModAlgAssLat, p::Int; filter = nothing, composition_factors = nothing)
  res = typeof(L)[]
  if composition_factors === nothing
    V = reduction(L, p)
    F = V.base_ring
    comp_fac = Hecke.composition_factors(V)
  else
    comp_fac = composition_factors
    F = coefficient_ring(comp_fac[1])
    V = change_coefficient_ring(F, L)
  end
  for C in comp_fac
    H = basis_of_hom(V, C)
    if length(H) == 0
      continue
    end
    # We have to loop over all morphisms, but we can discard multiples
    # So we do a projective space thingy
    pivs = Int[]
    Kl = zero_matrix(QQ, rank(L), rank(L))
    for v in enumerate_lines(F, length(H))
      zero!(Kl)
      empty!(pivs)
      #k = sum(H[i] * v[i] for i in 1:length(H))
      if length(H) == 1
        k = H[1]
      else
        k = v[1] * H[1]
        for i in 2:length(H)
          if iszero(v[i])
            continue
          end
          addmul!(k, k, v[i], H[i])
          #k = add!(k ,k, v[i] * H[i])
        end
      end
      r, K = left_kernel(k)
      _, K = rref(K)
      # The lattice we are looking is generated by lift(K) + pZ^n
      # The HNF of this lattice is/would be the lift(rref(K) and p's added in
      # the zero-rows such that the rank is full.
      # We scale the rows and check the pivots
      l = 1
      m = r + 1
      for i in 1:r
        while iszero(K[i, l])
          l += 1
        end
        # The rows are not normalized
        push!(pivs, l)
      end
      # We lift directly to Q
      Kl = _lift_to_Q!(Kl, K)
      # Set the zero rows correctly
      for i in 1:nrows(K)
        if !(i in pivs)
          Kl[m, i] = p
          m += 1
        end
      end
      # Kl has the same Z-span as fmpq_mat(hnf_modular_eldiv(lift(K), fmpz(p)))
      # We need the basis matrix with respect to 
      _bmat = mul!(Kl, Kl, L.basis)
      LL = lattice(L.V, L.base_ring, _bmat, check = false)
      if any(LLL -> LLL.basis == LL.basis, res)
        continue
      end
      if filter === nothing ||
         (filter == :local_isomorphism && all(LLL -> !islocally_isomorphic(LLL, LL, fmpz(p)), res))
        push!(res, LL)
      end
    end
  end
  return res
end

################################################################################
#
#  Centering algorithm
#
################################################################################

function sublattice_classes(L::ModAlgAssLat, p::Int)
  res = typeof(L)[L]
  to_check = typeof(L)[L]
  while !isempty(to_check)
    M = pop!(to_check)
    X = pmaximal_sublattices(M, p, filter = :local_isomorphism)
    for N in X
      if any(LLL -> islocally_isomorphic(LLL, N, fmpz(p))[1], res)
        continue
      else
        push!(res, N)
        push!(to_check, N)
      end
    end
    #@show length(res)
  end
  return res
end

function issublattice(L::ModAlgAssLat, M::ModAlgAssLat)
  return isone(denominator(basis_matrix(L) * basis_matrix_inverse(M)))
end

function _issublattice(L::ModAlgAssLat, M::ModAlgAssLat, tmp)
  tmp = mul!(tmp, basis_matrix(L), basis_matrix_inverse(M))
  return isone(denominator(tmp))
end

function sublattices(L::ModAlgAssLat, p::Int, level = inf)
  res = typeof(L)[L]
  to_check = typeof(L)[L]
  pL = p*L
  temp = typeof(L)[]
  i = 0
  F = GF(p)
  comp_fac = composition_factors(change_coefficient_ring(F, L))
  tmp_ = zero_matrix(QQ, rank(L), rank(L))
  while !isempty(to_check)
    if i >= level
      break
    end
    i += 1
    empty!(temp)

    for M in to_check
      pmax = pmaximal_sublattices(M, p, composition_factors = comp_fac)
      for N in pmax
        if _issublattice(N, pL, tmp_)
          continue
        end
        if any(LLL -> LLL.basis == N.basis, temp) || any(LLL -> LLL.basis == N.basis, res)
          continue
        else
          push!(temp, N)
        end
      end
    end
    empty!(to_check)
    append!(to_check, temp)
    append!(res, temp)
  end
  return res
end
