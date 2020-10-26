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


function lattice(v::Vector{T}, disc::fmpz; isexact::Bool = false) where T <: NumFieldElem
  @assert !isempty(v)
  L = NfLattice{T}(v, disc)
  L.is_minkowski_exact = isexact
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

function minkowski_gram_mat_scaled(L::NfLattice, p::Int)
  if L.is_minkowski_exact
    L.minkowski_gram_exact = _exact_minkowski_matrix(basis(L))
    return L.minkowski_gram_exact
  end
  K = nf(L)
  if isdefined(L, :minkowski_gram_scaled) && L.minkowski_gram_scaled[1] >= p
    A = deepcopy(O.minkowski_gram_mat_scaled[1])
    shift!(A, p - O.minkowski_gram_mat_scaled[2])
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

function lll(L::NfLattice, weights::fmpz_mat = zero_matrix(FlintZZ, 1, 1); starting_prec::Int = 100)
  if L.is_minkowski_exact
    M = _exact_minkowski_matrix(basis(L))
    l, v = lll_gram_with_transform(M)
    return FakeFmpqMat(l), v
  end
  prec = starting_prec
  local l1::FakeFmpqMat
  local v::fmpz_mat
  while true
    if prec > 2^18
      error("Something wrong in short_elem")
    end
    try
      l1, v = _lll(L, weights, prec)
      break
    catch e
      if !(e isa LowPrecisionLLL || e isa InexactError)
        rethrow(e)
      end
      prec *= 2
    end
  end
  return l1, v
end

function _lll(L::NfLattice, weights::fmpz_mat, prec::Int)
  if iszero(weights)
    d = minkowski_gram_mat_scaled(L, prec)
    sv = fmpz(0)
  else
    d = weighted_minkowski_gram_scaled(L, weights, prec)
    sv = max(fmpz(0), sum(weights[1, i] for i=1:ncols(weights)))
  end
  n = dim(L)
  g = identity_matrix(FlintZZ, n)
  ctx = Nemo.lll_ctx(0.99, 0.51, :gram)
  ccall((:fmpz_lll, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d, g, ctx)
  l, t = d, g
  if nbits(maximum(abs, t)) >  div(prec, 2)
    throw(LowPrecisionLLL())
  end
  n = nrows(l)
  disc = discriminant(L) * fmpz(2)^(2*sv)
  di = root(disc, n)+1
  di *= fmpz(2)^(div(n+1,2)) * fmpz(2)^prec
  if compare_index(l, 1, 1, di) > 0 
    throw(LowPrecisionLLL())
  end
  pr = prod_diagonal(l)
  if pr > fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec)
    throw(LowPrecisionLLL())
  end
  return FakeFmpqMat(l, fmpz(2)^prec), t
end


function lll_basis(L::NfLattice{T}) where T
  K = nf(L)
  l, t = lll(L)
  B = basis(L)
  new_basis = Vector{T}(undef, dim(L))
  tmp = K()
  for i = 1:length(new_basis)
    a = K()
    for j = 1:ncols(l)
      tmp = B[j]*t[i, j]
      a = add!(a, a, tmp)
    end
    new_basis[i] = a
  end
  return new_basis
end

_abs_disc(O::NfRelOrd) = absolute_discriminant(O)
_abs_disc(I::NfRelOrdIdl) = absolute_discriminant(order(I))*absolute_norm(I)

function lll_basis(OL::T) where T <: Union{NfRelOrdIdl, NfRelOrd}
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
  isexact = false
  if istotally_real(L)
    isexact = true
  end
  V = lattice(abs_bas, _abs_disc(OL), isexact = isexact)
  return lll_basis(V)
end
