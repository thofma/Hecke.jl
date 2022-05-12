mutable struct NfLattice{T}
  basis::Vector{T}
  discriminant::fmpz
  is_minkowski_exact::Bool
  minkowski_gram_exact::fmpz_mat
  minkowski_gram_scaled::Tuple{Int, fmpz_mat}
  function NfLattice{T}(v::Vector{T}, discriminant::fmpz) where {T <: NumFieldElem}
    n = new{T}()
    n.basis = v
    n.discriminant = discriminant
    is_minkowski_exact = false
    return n
  end
end


function lattice(v::Vector{T}, disc::fmpz; is_exact::Bool = false) where T <: NumFieldElem
  @assert !isempty(v)
  L = NfLattice{T}(v, abs(disc))
  L.is_minkowski_exact = is_exact
  return L
end

function dim(L::NfLattice)
  return length(L.basis)
end

function basis(L::NfLattice)
  return L.basis
end

function discriminant(L::NfLattice)
  return L.discriminant
end

function nf(L::NfLattice{T}) where T <: NumFieldElem
  return parent(basis(L)[1])
end

function minkowski_matrix(L::NfLattice, p::Int)
  return minkowski_matrix(basis(L), p)
end

#apply the change of basis given by M, creating a new lattice.
function apply(L::NfLattice{T}, t::fmpz_mat) where T <: NumFieldElem
  K = nf(L)
  B = basis(L)
  new_basis = Vector{T}(undef, dim(L))
  tmp = K()
  for i = 1:length(new_basis)
    a = K()
    for j = 1:ncols(t)
      tmp = B[j]*t[i, j]
      a = add!(a, a, tmp)
    end
    new_basis[i] = a
  end
  return lattice(new_basis, discriminant(L), is_exact = L.is_minkowski_exact)
end

function minkowski_gram_mat_scaled(L::NfLattice, p::Int)
  if L.is_minkowski_exact
    L.minkowski_gram_exact = _exact_minkowski_matrix(basis(L))
    return L.minkowski_gram_exact
  end
  K = nf(L)
  if isdefined(L, :minkowski_gram_scaled) && L.minkowski_gram_scaled[1] >= p
    A = deepcopy(L.minkowski_gram_mat_scaled[2])
    shift!(A, p - L.minkowski_gram_mat_scaled[1])
  else
    c = minkowski_matrix(L, p)
    B = basis(L)
    d = zero_matrix(FlintZZ, length(B), absolute_degree(K))
    A = zero_matrix(FlintZZ, length(B), length(B))
    round_scale!(d, c, p)
    ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), A, d)
    shift!(A, -p)
    L.minkowski_gram_scaled = (p, deepcopy(A))
  end
  for i=1:absolute_degree(K)
    fmpz_mat_entry_add_ui!(A, i, i, UInt(nrows(A)))
  end
  return A
end

function weighted_minkowski_gram_scaled(L::NfLattice, v::fmpz_mat, prec::Int)
  c = deepcopy(minkowski_matrix(L, prec))
  mult_by_2pow_diag!(c, v)
  d = zero_matrix(FlintZZ, nrows(c), ncols(c))
  round_scale!(d, c, prec)
  g = zero_matrix(FlintZZ, nrows(c), nrows(c))
  ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), g, d)
  shift!(g, -prec)
  for i=1:n
    fmpz_mat_entry_add_ui!(g, i, i, UInt(nrows(d)))
  end
  return g
end

function lll(L::NfLattice, weights::fmpz_mat = zero_matrix(FlintZZ, 1, 1); starting_prec::Int = 100 + 25*div(dim(L), 3) + Int(round(log(abs(discriminant(L))))))
  if L.is_minkowski_exact
    M = _exact_minkowski_matrix(basis(L))
    l, v = lll_gram_with_transform(M)
    return FakeFmpqMat(l), v
  end
  prec = starting_prec
  local l1::FakeFmpqMat
  local v::fmpz_mat
  n = dim(L)
  starting_profile = sum(nbits(Hecke.upper_bound(fmpz, t2(x))) for x in basis(L))
  @vprint :LLL 1 "Starting profile: $(starting_profile) \n"
  @vprint :LLL 1 "Target profile: $(nbits(discriminant(L)^2)+divexact(n*(n-1), 2)) \n"
  @vprint :LLL 1 "Starting precision: $(prec) \n"
  while true
    if prec > 2^30
      error("Precision too large!")
    end
    fl, l1, v = _lll(L, weights, prec)
    if fl
      break
    end
    Lnew = apply(L, v)
    new_profile = sum(nbits(Hecke.upper_bound(fmpz, t2(x))) for x in basis(Lnew))
    @vprint :LLL 1 "New profile: $(new_profile) \n"
    if new_profile < starting_profile
      @vprint :LLL 1 "Using transformation!\n"
      l2, v2 = lll(Lnew, weights, starting_prec = ceil(Int, prec*1.5))
      return l2, v2*v
    end
    prec *= 2
    @vprint :LLL 1 "Increasing precision to $(prec) \n"
  end
  return l1, v
end

function _lll(L::NfLattice, weights::fmpz_mat, prec::Int)
  @vprint :LLL 1 "Computing Minkowski Gram matrix with precision $(prec) \n"
  local d::fmpz_mat
  local sv::fmpz
  while true
    try
      if iszero(weights)
        @vtime :LLL 1 d = minkowski_gram_mat_scaled(L, prec)
        sv = fmpz(0)
      else
        @vtime :LLL 1 d = weighted_minkowski_gram_scaled(L, weights, prec)
        sv = max(fmpz(0), sum(weights[1, i] for i=1:ncols(weights)))
      end
      break
    catch e
      prec += 100
    end
  end
  n = dim(L)
  g = identity_matrix(FlintZZ, n)
  g1 = identity_matrix(FlintZZ, n)
  ctx1 = Nemo.lll_ctx(0.4, 0.51, :gram)
  ctx2 = Nemo.lll_ctx(0.99, 0.51, :gram)
  @vtime :LLL 1 ccall((:fmpz_lll, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d, g, ctx1)
  @vtime :LLL 1 ccall((:fmpz_lll, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d, g1, ctx2)
  mul!(g, g1, g)
  fl = true
  if nbits(maximum(abs, g)) >  div(prec, 2)
    fl = false
  end
  if fl
    n = nrows(d)
    disc = discriminant(L) * fmpz(2)^(2*sv)
    di = root(disc, n) + 1
    di *= fmpz(2)^(div(n+1,2)) * fmpz(2)^prec
    if compare_index(d, 1, 1, di) > 0
      fl = false
    end
    pr = prod_diagonal(d)
    if pr > fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec)
      fl = false
    end
  end
  return fl, FakeFmpqMat(d, fmpz(2)^prec), g
end

function lll_basis(L::NfLattice{T}) where T
  K = nf(L)
  l, t = lll(L)
  L1 = apply(L, t)
  return basis(L)
end

_abs_disc(O::NfRelOrd) = absolute_discriminant(O)
_abs_disc(I::NfRelOrdIdl) = absolute_discriminant(order(I))*absolute_norm(I)

function _get_nice_basis(OL::T) where T <: Union{NfRelOrdIdl, NfRelOrd}
  L = nf(OL)
  B = pseudo_basis(OL, copy = false)
  ideals = Dict{typeof(B[1][2]), Vector{elem_type(base_field(L))}}()
  for i = 1:length(B)
    if haskey(ideals, B[i][2])
      continue
    end
    ideals[B[i][2]] = lll_basis(B[i][2])
  end
  abs_bas = Vector{elem_type(L)}(undef, absolute_degree(L))
  ind = 1
  for i = 1:length(B)
    J = ideals[B[i][2]]
    for j = 1:length(J)
      abs_bas[ind] = J[j]*B[i][1]
      ind += 1
    end
  end
  return abs_bas
end

function lll_basis(OL::T) where T <: Union{NfRelOrdIdl, NfRelOrd}
  L = nf(OL)
  B = _get_nice_basis(OL)
  is_exact = false
  if is_totally_real(L)
    is_exact = true
  end
  V = lattice(B, _abs_disc(OL), is_exact = is_exact)
  return lll_basis(V)
end
