module NfMatModule

using Hecke
import Nemo
"""
In Antic, `nf_elem` is a union of
-  Degree 1 Field:
   - fmpz  numerator
   - fmpz  denominator
-  Degree 2 Field:
   - fmpz [3] coeffs 0, 1, and 2 to have a buffer for products
   - fmpz  denominator
-  Degree > 2 Field:
   - fmpq_poly which is
     - fmpz * numerator coeffs
     - fmpz   denominator
     - slong  alloc
     - slong  length
All in all, at most 4 Ptr/long/Int. This is "modelled" here as
4 Ints.

Important: the denominator has to be initioalised in all cases, a 
binary zero is fine for the other fields.
Due to the different position of the denominator in deg 2, we have
2 constructors below.
Further `zero` is constructing a valid 0 in degree 1 and > 2
while `one` is used to build a zero in degree 2.

Given and `nf_elem_raw` are immutable (otherwise the memory layout does not
work, ie. a flat array) and thus cannot have a finalizer, this type can only 
be used inside a larger sturcture via `Vector{nf_elem_raw}` as in
the matrices. This would also allow polynomials...
"""
struct nf_elem_raw
  a::Int
  b::Int
  c::Int
  d::Int
  function nf_elem_raw()
    new(0,1,0,0)  #the den is in pos 2 for deg == 1 or > 2
                  #and in pos 4 for deg == 2
  end
  function nf_elem_raw(::Int)
    new(0,0,0,1)  #the den is in pos 2 for deg == 1 or > 2
                  #and in pos 4 for deg == 2
  end
end

function Base.zero(::Type{nf_elem_raw})
  return nf_elem_raw()
end

function Base.one(::Type{nf_elem_raw})
  return nf_elem_raw(1)
end

mutable struct NfMatElem <: MatElem{nf_elem}
  entries:: Vector{nf_elem_raw}
  rows:: Vector{Int}
  nrows::Int
  ncols::Int
  base_ring::AnticNumberField

  function NfMatElem(K::AnticNumberField, r::Int, c::Int)
    if degree(K) == 2
      entries = ones(nf_elem_raw, r*c)
    else
      entries = zeros(nf_elem_raw, r*c)
    end
    rows = zeros(Int, r)
    for i=1:r
      rows[i] = (i-1)*c
    end
    M = new(entries, rows, r, c, K)
    #= to support `view`s, the finalizer is associated
       to the `entries` *not* the matrix.
       Since the finalizer get only array and not the field,
       different finalizer have to be used depending on the degree
    =#
    if degree(K) == 1
      finalizer(NfMatElem_clear1, entries)
    elseif degree(K) == 2
      finalizer(NfMatElem_clear2, entries)
    else
      finalizer(NfMatElem_clear3, entries)
    end
    return M
  end
  #creates a view M[r1:r2, c1:c2]
  function NfMatElem(M::NfMatElem, r1::Int, r2::Int, c1::Int, c2::Int)
    rows = M.rows[r1:r2]
    for i=1:length(rows)
      rows[i] += c1-1
    end
    return new(M.entries, rows, r2-r1+1, c2-c1+1, base_ring(M))
  end
  function NfMatElem(M::NfMatElem)
    K = base_ring(M)
    if degree(K) == 2
      entries = ones(nf_elem_raw, length(M.entries))
    else
      entries = zeros(nf_elem_raw, length(M.entries))
    end
    for i=1:length(entries)
      if M.entries[i].a != 0
        ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), pointer(entries, i), pointer(M.entries, i), K)
      end
    end
    if degree(K) == 1
      finalizer(NfMatElem_clear1, entries)
    elseif degree(K) == 2
      finalizer(NfMatElem_clear2, entries)
    else
      finalizer(NfMatElem_clear3, entries)
    end
    return new(entries, copy(M.rows), nrows(M), ncols(M), K)
  end
end

function NfMatElem_clear1(en::Vector{nf_elem_raw})
  #degree 1 case...
  for i=1:length(en)
    p = pointer(en, i)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
    p += sizeof(Int)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
  end
end

function NfMatElem_clear2(en::Vector{nf_elem_raw})
  for i=1:length(en)
    p = pointer(en, i)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
    p += sizeof(Int)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
    p += sizeof(Int)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
    p += sizeof(Int)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
  end
end

function NfMatElem_clear3(en::Vector{nf_elem_raw})
  for i=1:length(en)
    ccall((:fmpq_poly_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw},), pointer(en, i))
  end
end


function Base.deepcopy_internal(M::NfMatElem, d::IdDict)
  return NfMatElem(M::NfMatElem)
end

function Base.checkbounds(::Type{Bool}, M::NfMatElem, i::Int, j::Int)
  return 1 <= i <= M.nrows && 1 <= j <= M.ncols
end

function Base.checkbounds(M::NfMatElem, i::Int, j::Int)
  Base.checkbounds(Bool, M, i, j) || throw(BoundsError(M, (i,j)))
end

Hecke.nrows(M::NfMatElem) = M.nrows
Hecke.ncols(M::NfMatElem) = M.ncols
Hecke.base_ring(M::NfMatElem) = M.base_ring

@inline rows(M::NfMatElem) = M.rows
@inline ent(M::NfMatElem) = M.entries

####
#
# view
#
####
function Base.view(M::NfMatElem, r1::Int , r2::Int, c1::Int, c2::Int)
  @assert 0 < r1 <= r2 <= nrows(M)
  @assert 0 < c1 <= c2 <= ncols(M)
  return NfMatElem(M, r1, r2, c1, c2)
end

function Base.view(M::NfMatElem, r::UnitRange{Int}, c::UnitRange{Int})
  return Base.view(M, r.start, r.stop, c.start, c.stop)
end

function Base.view(M::NfMatElem, r::Colon, c::UnitRange{Int})
  return Base.view(M, 1:nrows(M), c)
end

function Base.view(M::NfMatElem, r::UnitRange{Int}, c::Colon)
  return Base.view(M, r, 1:ncols(M))
end

####
#
# Creation/ conversion
#
####
function Hecke.matrix(K::AnticNumberField, r::Int, c::Int, a::Vector{nf_elem})
  M = NfMatElem(K, r, c)
  for i=1:r
    for j=1:c
      M[i,j] = a[(i-1)*c+j]
    end
  end
  return M
end

#convert from "classical" implementation of MatElem{nf_elem}
function Hecke.matrix(M::Generic.MatSpaceElem{nf_elem})
  K = base_ring(M)
  N = NfMatElem(K, nrows(M), ncols(M))
  for i=1:nrows(M)
    for j=1:ncols(M)
      N[i,j] = M[i,j]
    end
  end
  return N
end

function Hecke.zero_matrix(K::AnticNumberField, r::Int, c::Int)
  return NfMatElem(K, r, c)
end

function Hecke.identity_matrix(K::AnticNumberField, n::Int)
  M = NfMatElem(K, n, n)
  for i=1:n
    M[i,i] = one(K)
  end
  return M
end

function Hecke.identity_matrix(M::NfMatElem)
  return identity_matrix(base_ring(M), nrows(M))
end

function Array(M::NfMatElem)
  return collect(M)
end

function Generic.Mat{nf_elem}(M::NfMatElem)
  N =  Generic.MatSpaceElem{nf_elem}(Array(M))
  N.base_ring = M.base_ring
  return N
end

Hecke.dense_matrix_type(::Type{nf_elem}) = NfMatElem

####
#
# some concatenation
#
####
function Base.vcat(M::NfMatElem, N::NfMatElem)
  K = base_ring(M)
  @assert K == base_ring(N)
  @assert ncols(M) == ncols(N)
  MN = NfMatElem(base_ring(M), nrows(M)+nrows(N), ncols(M))
  for i=1:nrows(M)
    for j=1:ncols(M)
      MN[i,j] = getindex_raw(M, i, j)
    end
  end
  for i=1:nrows(N)
    for j=1:ncols(N)
      MN[i+nrows(M), j] = getindex_raw(N, i, j)
    end
  end
  return MN
end

function Hecke.vcat!(M::NfMatElem, N::NfMatElem)
  @assert ncols(M) == ncols(N)
  n = nrows(M)
  M.nrows += nrows(N)
  resize!(M.entries, nrows(M) * ncols(N))
  for i=1:nrows(N)
    push!(M.rows, (i+n-1)*ncols(M))
    for j=1:ncols(M)
      M[i+n, j] = getindex_raw(N, i, j)
    end
  end
end

function Base.hcat(M::NfMatElem, N::NfMatElem)
  K = base_ring(M)
  @assert K == base_ring(N)
  @assert nrows(M) == nrows(N)
  MN = NfMatElem(base_ring(M), nrows(M), ncols(M)+ncols(N))
  for i=1:nrows(M)
    for j=1:ncols(M)
      MN[i,j] = getindex_raw(M, i, j)
    end
    for j=1:ncols(N)
      MN[i, j+ncols(M)] = getindex_raw(N, i, j)
    end
  end
  return MN
end

####
#
# Access - the checkbounds can be switched of for the raw versino
# the generic versino does alloc and copy, thus is slow anyway
#
####
function Base.getindex(M::NfMatElem, r::Int, c::Int)
  checkbounds(M, r, c)
  a = base_ring(M)()
  ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ref{nf_elem}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, pointer(M.entries, M.rows[r]+c), base_ring(M))
  return a
end

function Base.getindex(M::NfMatElem, r::AbstractVector{Int}, c::AbstractVector{Int})
  N = NfMatElem(base_ring(M), length(r), length(c))
  ii = 1
  for i = r
    jj = 1
    for j = c
      N[ii, jj] = M[i,j]
      jj += 1
    end
    ii += 1
  end
  return N
end

_rrange(::NfMatElem, r::Int) = r:r
_crange(::NfMatElem, c::Int) = c:c
_rrange(M::NfMatElem, r::Colon) = 1:nrows(M)
_crange(M::NfMatElem, c::Colon) = 1:ncols(M)
_rrange(::NfMatElem, r::UnitRange{Int}) = r
_crange(::NfMatElem, c::UnitRange{Int}) = c
_rrange(::NfMatElem, r::Vector{Int}) = r
_crange(::NfMatElem, c::Vector{Int}) = c

function Base.getindex(M::NfMatElem, r::Union{Colon, Int64, AbstractVector{Int64}}, c::Union{Colon, Int64, AbstractVector{Int64}})
  return Base.getindex(M, _rrange(M, r), _crange(M, c))
end

@inline function getindex_raw(M::NfMatElem, r::Int, c::Int)
  @boundscheck checkbounds(M, r, c)
  en = ent(M)
  ro = rows(M)
  return @inbounds pointer(en, ro[r]+c)
end

function Base.setindex!(M::NfMatElem, a::nf_elem, r::Int, c::Int)
  checkbounds(M, r, c)
  ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{nf_elem}, Ref{AnticNumberField}), pointer(M.entries, M.rows[r]+c), a, base_ring(M))
end

function Base.setindex!(M::NfMatElem, a::Int, r::Int, c::Int)
  checkbounds(M, r, c)
  ccall((:nf_elem_set_si, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Int, Ref{AnticNumberField}), pointer(M.entries, M.rows[r]+c), a, base_ring(M))
end

function Base.setindex!(M::NfMatElem, a::fmpz, r::Int, c::Int)
  checkbounds(M, r, c)
  ccall((:nf_elem_set_fmpz, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{fmpz}, Ref{AnticNumberField}), pointer(M.entries, M.rows[r]+c), a, base_ring(M))
end

#hopefully not used?
function Base.setindex!(M::NfMatElem, a::nf_elem_raw, r::Int, c::Int)
  @boundscheck checkbounds(M, r, c)
  ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{nf_elem_raw}, Ref{AnticNumberField}), pointer(M.entries, M.rows[r]+c), a, base_ring(M))
end

@inline function Base.setindex!(M::NfMatElem, a::Ptr{nf_elem_raw}, r::Int, c::Int)
  @boundscheck checkbounds(M, r, c)
  ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{nf_elem_raw}, Ref{AnticNumberField}), pointer(M.entries, M.rows[r]+c), a, base_ring(M))
end

function Base.setindex!(M::NfMatElem, N::NfMatElem, r::UnitRange{Int}, c::UnitRange{Int})
  for i = r
    for j = c
      M[i,j] = getindex_raw(N, i, j)
    end
  end
end

#= yields ambiguities
function Base.setindex!(M::NfMatElem, N::NfMatElem, r::Union{Colon, Int64, AbstractVector{Int64}}, c::Union{Colon, Int64, AbstractVector{Int64}})
  Base.setindex!(M, N, _rrange(M, r), _crange(M, c))
end
=#

function Hecke.swap_rows!(M::NfMatElem, i::Int, j::Int)
  M.rows[i], M.rows[j] = M.rows[j], M.rows[i]
end

function Hecke.swap_rows(M::NfMatElem, i::Int, j::Int)
  N = deepcopy(M)
  swap_rows!(N, i, j)
  return N
end

@inline function swap_entry!(M::NfMatElem, r1::Int, c1::Int, r2::Int, c2::Int)
  @boundscheck checkbounds(M, r1, c1)
  @boundscheck checkbounds(M, r2, c2)
  M.entries[M.rows[r1]+c1], M.entries[M.rows[r2]+c2] = 
     M.entries[M.rows[r2]+c2], M.entries[M.rows[r1]+c1]
end

function Hecke.swap_cols!(M::NfMatElem, i::Int, j::Int)
  for r=1:nrows(M)
    swap_entry!(M, r, i, r, j)
  end
end

function Hecke.swap_cols(M::NfMatElem, i::Int, j::Int)
  N = deepcopy(M)
  swap_cols!(N, i, j)
  return N
end
#=
function Base.show(io::IO, M::NfMatElem)
  print(io, "$(M.nrows) x $(M.ncols) matrix over $(M.base_ring)")
end
=#

@inline function Hecke.iszero_entry(M::NfMatElem, i::Int, j::Int)
  p = getindex_raw(M, i, j)
  reduce!(p, base_ring(M))
  return ccall((:nf_elem_is_zero, Nemo.libantic), Cint, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), p, base_ring(M)) == 1
end

function Hecke.iszero_row(M::NfMatElem, i::Int)
  return all(x->iszero_entry(M, i, x), 1:ncols(M))
end

function Hecke.iszero_column(M::NfMatElem, i::Int)
  return all(x->iszero_entry(M, x, i), 1:nrows(M))
end

@inline function isone_entry(M::NfMatElem, i::Int, j::Int)
  p = getindex_raw(M, i, j)
  reduce!(p, base_ring(M))
  return ccall((:nf_elem_is_one, Nemo.libantic), Cint, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), p, base_ring(M)) == 1
end

@inline function mul!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::Ptr{nf_elem_raw}, K::AnticNumberField, red::Bool = true)
  ccall((:nf_elem_mul_red, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}, Cint), a, b, c, K, red)
end

@inline function mul!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::nf_elem, K::AnticNumberField, red::Bool = true)
  ccall((:nf_elem_mul_red, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{nf_elem}, Ref{AnticNumberField}, Cint), a, b, c, K, red)
end

@inline function mul!(a::nf_elem, b::Ptr{nf_elem_raw}, c::Ptr{nf_elem_raw}, K::AnticNumberField, red::Bool = true)
  ccall((:nf_elem_mul_red, Nemo.libantic), Cvoid, (Ref{nf_elem}, Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}, Cint), a, b, c, K, red)
end

@inline function reduce!(a::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_elem_reduce, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, K)
end

@inline function add!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_elem_add, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, b, c, K)
end

@inline function add!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::nf_elem, K::AnticNumberField)
  ccall((:nf_elem_add, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{nf_elem}, Ref{AnticNumberField}), a, b, c, K)
end

@inline function sub!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_elem_sub, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, b, c, K)
end

@inline function sub!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::nf_elem, K::AnticNumberField)
  ccall((:nf_elem_sub, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{nf_elem}, Ref{AnticNumberField}), a, b, c, K)
end

function Hecke.divide_row!(M::NfMatElem, i::Int, a::nf_elem)
  ai = inv(a)
  K = parent(a)
  @assert base_ring(M) === K
  for j=1:ncols(M)
    mul!(getindex_raw(M, i, j), getindex_raw(M, i, j), a, K)
  end
end

function Hecke.transpose(M::NfMatElem)
  N = zero_matrix(base_ring(M), ncols(M), nrows(M))
  for i=1:nrows(M)
    for j=1:ncols(M)
      N[j,i] = getindex_raw(M, i, j)
    end
  end
  return N
end

#standart Gauss, no brain.
# assumes 1:start is already in ref with pivot array in piv
# operates in start:stop
#  start:stop is reduced modulo 1:start-1
#  then Gauss continues 
#
# if det == true then the scaling of multiplied together to find the
# determinant.
function _ref!(M::NfMatElem; piv::Vector{Int} = zeros(Int, ncols(M)), start::Int = 1, stop::Int = nrows(M), det::Bool = false) #TODO: mul_non_reduce?
  K = base_ring(M)
  t = K()
  de = K(1)
  for i=1:stop
    if i < start
      j = findfirst(isequal(i), piv)
    else
      j = 1
      while j <= ncols(M) && Hecke.iszero_entry(M, i, j)
        j += 1
      end
      if j>ncols(M)
        continue
      end
      @inbounds piv[j] = i
      @assert !Hecke.iszero_entry(M, i, j)
      if det
        Nemo.mul!(de, de, M[i,j])
      end
      if !isone_entry(M, i, j)
        ccall((:nf_elem_inv, Nemo.libantic), Cvoid, (Ref{nf_elem}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), t, getindex_raw(M, i, j), K)
        k = j
        while k<= ncols(M)
          reduce!(getindex_raw(M, i, k), K)
          mul!(getindex_raw(M, i, k), getindex_raw(M, i, k), t, K)
          k += 1
        end
      end
    end
    @assert isone_entry(M, i, j)
    for r = max(start, i+1):nrows(M)
      if Hecke.iszero_entry(M, r, j) 
        continue
      end
      s = getindex_raw(M, r, j)
      reduce!(s, K)
      for k=ncols(M):-1:j
        if Hecke.iszero_entry(M, i, k)
          continue
        end
        Mrk = getindex_raw(M, r, k)
        mul!(t, s, getindex_raw(M, i, k), K, false)
        sub!(Mrk, Mrk, t, K)
      end
    end
  end
  return piv, de
end

function ref!(M::NfMatElem)
  piv, _ = _ref!(M)
  permute_rows!(M, piv)
  return length(piv) - length(findall(iszero, piv))
end

function ref(M::NfMatElem)
  N = deepcopy(M)
  return ref!(N), N
end

function Hecke.rref!(M::NfMatElem)
  piv = _ref!(M)[1]
  K = base_ring(M)
  t = K()
  for j = 1:ncols(M)
    @inbounds p = piv[j]
    iszero(p) && continue
    for k=1:p-1
      s = getindex_raw(M, k, j)
      for h=ncols(M):-1:j
        mul!(t, getindex_raw(M, p, h), s, K)
        sub!(getindex_raw(M, k, h), getindex_raw(M, k, h), t, K)
      end
    end
  end
  permute_rows!(M, piv)
  return length(piv) - length(findall(iszero, piv))
end

function rref(M::NfMatElem)
  N = deepcopy(M)
  return rref!(N), N
end

function permute_rows!(M::NfMatElem, pi::Vector{Int})
  j = 1
  for i=pi
    if i==0
      continue
    end
    if j != i
      swap_rows!(M, j, i)
    end
    j += 1
  end
  return nothing
end

function inv_new(M::NfMatElem)
  @assert nrows(M) == ncols(M)
  T = hcat(M, identity_matrix(M))
  rref!(T)
  return T[:, ncols(M)+1:end]
end

Base.similar(M::NfMatElem, r::Int, c::Int) = zero_matrix(base_ring(M), r, c)
Base.similar(M::NfMatElem) = zero_matrix(base_ring(M), nrows(M), ncols(M))

#not used.
function init!(A::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_init, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), A, K)
end

function Base.:*(x::NfMatElem, y::NfMatElem)
  ncols(x) != nrows(y) && error("Incompatible matrix dimensions")
  K = base_ring(x)
  @assert K == base_ring(y)

  A = similar(x, nrows(x), ncols(y))

  C = K()
  for i = 1:nrows(x)
    for j = 1:ncols(y)
      for k = 1:ncols(x)
        mul!(C, getindex_raw(x, i, k), getindex_raw(y, k, j), K, false)
        add!(getindex_raw(A, i, j), getindex_raw(A, i, j), C, K)
      end
      reduce!(getindex_raw(A, i, j), K)
    end
  end
  return A
end

function Hecke.zero!(a::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_elem_zero, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, K)
end

#add version is used in strassen
#otherwise, classical matrix multiplication
function Nemo.mul!(C::NfMatElem, A::NfMatElem, B::NfMatElem, add::Bool = false)
  K = base_ring(A)
  @assert base_ring(B) == base_ring(C) == K
  T = K()
  S = K()
  for i=1:nrows(A)
    for j=1:ncols(B)
      Hecke.zero!(S)
      for k=1:ncols(A)
        mul!(T, getindex_raw(A, i, k), getindex_raw(B, k, j), K, false)
        Hecke.add!(S, S, T)
      end
      Hecke.reduce!(S)
      if add
        add!(getindex_raw(C, i, j), getindex_raw(C, i, j), S, K)
      else
        C[i,j] = S
      end
    end
  end
end

function Base.:-(A::NfMatElem, B::NfMatElem)
  C = zero_matrix(base_ring(A), nrows(A), ncols(A))
  return Nemo.sub!(C, A, B)
end

function Nemo.sub!(C::NfMatElem, A::NfMatElem, B::NfMatElem)
  K = base_ring(A)
  for i=1:nrows(A)
    for j=1:ncols(A)
      sub!(getindex_raw(C, i, j), getindex_raw(A, i, j), getindex_raw(B, i, j), K)
    end
  end
  return C
end

function Base.:+(A::NfMatElem, B::NfMatElem)
  C = zero_matrix(base_ring(A), nrows(A), ncols(A))
  return Nemo.add!(C, A, B)
end

function Nemo.add!(C::NfMatElem, A::NfMatElem, B::NfMatElem)
  K = base_ring(A)
  for i=1:nrows(A)
    for j=1:ncols(A)
      add!(getindex_raw(C, i, j), getindex_raw(A, i, j), getindex_raw(B, i, j), K)
    end
  end
  return C
end

#############################################################################
#
# matrix multiplication via fmpq_mat:
# write A as sum A_i t^t for A_i fmpq_mat's
# same for B and form the product, using A_i*B_j thus using fast(?)
# fmpq_mat_mul
#
# (ONLY available for degree(K) > 2, defaults to normal otherwise)
#
#############################################################################
function Hecke.coeff(M::NfMatElem, i::Int)
  return map(x->coeff(x, i), M)
end

function getindex_raw(M::fmpq_mat, i::Int, j::Int)
  return ccall((:fmpq_mat_entry, Nemo.libflint), Ptr{fmpq}, (Ref{fmpq_mat}, Int, Int), M, i-1, j-1)
end

function coeff!(m::fmpq_mat, M::NfMatElem, n::Int)
  K = base_ring(M)
  for i=1:nrows(M)
    for j=1:ncols(M)
      ccall((:nf_elem_get_coeff_fmpq, Nemo.libantic), Cvoid, (Ptr{fmpq}, Ptr{nf_elem_raw}, Int, Ref{AnticNumberField}), getindex_raw(m, i, j), getindex_raw(M, i, j), n, K)
    end
  end
end

function Hecke.denominator(a::Ptr{nf_elem_raw}, K::AnticNumberField)
  d = fmpz()
  denominator!(d, a, K)
  return d
end

function denominator!(d::fmpz, a::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_elem_get_den, Nemo.libantic), Nothing, (Ref{fmpz}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), d, a, K)
end

function setcoeff!(M::NfMatElem, n::Int, m::fmpq_mat)
  K = base_ring(M)
  @assert degree(K) > 2 #for now
  for i=1:nrows(M)
    for j=1:ncols(M)
      ccall((:fmpq_poly_set_coeff_fmpq, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, Int, Ptr{fmpq}), getindex_raw(M, i, j), n, getindex_raw(m, i, j))
    end
  end
end

function reduce!(M::NfMatElem)
  K = base_ring(M)
  for i=1:nrows(M)
    for j=1:ncols(M)
      reduce!(getindex_raw(M, i, j), K)
    end
  end
end

function mul_new(A::NfMatElem, B::NfMatElem)
  K = base_ring(A)
  degree(K) > 2 || return A*B
  @assert degree(K) > 2
  C = similar(A, nrows(A), ncols(B))
  a = [coeff(A, i) for i=0:degree(K)-1]
  b = [coeff(B, i) for i=0:degree(K)-1]
  d = zero_matrix(QQ, nrows(C), ncols(C))
  for l=0:2*degree(K)-1
    c = zero_matrix(QQ, nrows(C), ncols(C))
    for i=max(0, l-degree(K)+1):min(degree(K)-1, l)
      #i+j = l, j = l-j
      Nemo.mul!(d, a[i+1], b[l-i+1])
      Nemo.add!(c, c, d)
    end
    setcoeff!(C, l, c)
  end
  reduce!(C)
  return C
end

#############################################################################
#
# multiplication via Kronnecker segmentation via fmpz_poly_mat
#
# seems to be fastest. 
#
# Think of a NfMatElem A as a matrix of fmpq_poly
# Goal:
# C = A*B
# write A as dA * X for dA diagonal in Z and X integral (fmpz_poly)
# write B as Y * dB for bD diagonal in Z and Y integral
# C = dA * X * Y * dB
# and the middle product is fast via flint.
#
# (only for degree(K) > 2, defaults to normal otherwise)
#############################################################################
struct fmpz_poly_raw
  coeffs::Int #Ptr{fmpz}
  a::Int
  l::Int
  function fmpz_poly_raw()
    return new(0,0,0)
  end
  function fmpz_poly_raw(c::Int, a::Int, l::Int)
    return new(c, a, l)
  end
end

Base.zero(::Type{fmpz_poly_raw}) = fmpz_poly_raw()

struct fmpq_poly_raw
  coeffs::Int #Ptr{fmpz}
  den::Int #fmpz
  a::Int
  l::Int
  function fmpq_poly_raw()
    return new(0,1,0,0)
  end
  function fmpq_poly_raw(c::Int, d::Int, a::Int, l::Int)
    return new(c, d, a, l)
  end
end

Base.zero(::Type{fmpq_poly_raw}) = fmpq_poly_raw()

#minimal support to have printing (for debugging)
mutable struct fmpz_poly_mat <: MatElem{fmpz_poly}
   entries::Int #Ptr{fmpz_poly_raw}
   r::Int
   c::Int
   d::Int #Ptr{Ptr{fmpz_poly_raw}}
   function fmpz_poly_mat(r::Int, c::Int)
     mat = new()
     ccall((:fmpz_poly_mat_init, Nemo.libflint), Cvoid, (Ref{fmpz_poly_mat}, Int, Int), mat, r, c)
     finalizer(fmpz_poly_mat_clear, mat)
     return mat
   end
end

function fmpz_poly_mat_clear(M::fmpz_poly_mat)
  ccall((:fmpz_poly_mat_clear, Nemo.libflint), Cvoid, (Ref{fmpz_poly_mat}, ), M)
end

Hecke.base_ring(::fmpz_poly_mat) = Hecke.Globals.Zx
Hecke.nrows(M::fmpz_poly_mat) = M.r
Hecke.ncols(M::fmpz_poly_mat) = M.c

function Base.getindex(M::fmpz_poly_mat, i::Int, j::Int)
  f = Hecke.Globals.Zx()
  ccall((:fmpz_poly_set, Nemo.libflint), Cvoid, (Ref{fmpz_poly}, Ptr{fmpz_poly_raw}), f, getindex_raw(M, i, j))
  return f
end

function Base.checkbounds(M::fmpz_poly_mat, i::Int, j::Int)
  (1 <= i <= M.r && 1 <= j <= M.c) || throw(BoundsError(M, (i,j)))
end

@inline function getindex_raw(M::fmpz_poly_mat, i::Int, j::Int)
  @boundscheck checkbounds(M, i, j)
  return ccall((:fmpz_poly_mat_entry, Nemo.libflint), Ptr{fmpz_poly_raw}, (Ref{fmpz_poly_mat}, Int, Int), M, i-1, j-1)
end

@inline function Base.setindex!(M::fmpz_poly_mat, f::Ptr{nf_elem_raw}, i::Int, j::Int)
  @boundscheck checkbounds(M, i, j)
  ff = reinterpret(Ptr{Int}, f)
  B = [fmpz_poly_raw(unsafe_load(ff, 1), unsafe_load(ff, 3), unsafe_load(ff, 4))]
  Base.GC.@preserve B begin
    b = pointer(B, 1)
    ccall((:fmpz_poly_set, Nemo.libflint), Cvoid, (Ptr{fmpz_poly_raw}, Ptr{fmpz_poly_raw}), getindex_raw(M, i, j), b)
  end
end

@inline function Base.setindex!(M::NfMatElem, f::Ptr{fmpz_poly_raw}, i::Int, j::Int)
  @boundscheck checkbounds(M, i, j)
  ff = reinterpret(Ptr{Int}, f)
  B = [fmpq_poly_raw(unsafe_load(ff, 1), 1, unsafe_load(ff, 2), unsafe_load(ff, 3))]
  Base.GC.@preserve B begin
    b = pointer(B, 1)
    ccall((:fmpq_poly_set, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, Ptr{fmpq_poly_raw}), getindex_raw(M, i, j), b)
  end
end


function mul_KS(A::NfMatElem, B::NfMatElem)
  K = base_ring(A)
  degree(K) > 2 || return A*B

  dA = [reduce(lcm, map(denominator, A[i, :]), init = fmpz(1)) for i=1:nrows(A)]
  tA = fmpz_poly_mat(nrows(A), ncols(A))
  tB = fmpz_poly_mat(nrows(B), ncols(B))
  tC = fmpz_poly_mat(nrows(A), ncols(B))
  Base.GC.@preserve tA tB tC begin
    for i=1:nrows(A)
      for j=1:ncols(A)
        tA[i,j] = getindex_raw(A, i, j)
        s = Nemo.divexact(dA[i], denominator(getindex_raw(A, i, j), K))
        if !isone(s)
          ccall((:fmpz_poly_scalar_mul_fmpz, Nemo.libflint), Cvoid, (Ptr{fmpz_poly_raw}, Ptr{fmpz_poly_raw}, Ref{fmpz}), getindex_raw(tA, i, j), getindex_raw(tA, i, j), s)
        end
      end
    end

    dB = [reduce(lcm, map(denominator, B[:, i]), init = fmpz(1)) for i=1:ncols(B)]
    for i=1:nrows(B)
      for j=1:ncols(B)
        tB[i,j] = getindex_raw(B, i, j)
        s = Nemo.divexact(dB[j], denominator(getindex_raw(B, i, j), K))
        if !isone(s)
          ccall((:fmpz_poly_scalar_mul_fmpz, Nemo.libflint), Cvoid, (Ptr{fmpz_poly_raw}, Ptr{fmpz_poly_raw}, Ref{fmpz}), getindex_raw(tB, i, j), getindex_raw(tB, i, j), s)
        end
      end
    end

    ccall((:fmpz_poly_mat_mul, Nemo.libflint), Cvoid, (Ref{fmpz_poly_mat}, Ref{fmpz_poly_mat}, Ref{fmpz_poly_mat}), tC, tA, tB)

    C = zero_matrix(K, nrows(A), ncols(B))
    for i=1:nrows(C)
      for j=1:ncols(C)
        C[i,j] = getindex_raw(tC, i, j)
        ccall((:nf_elem_set_den, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{fmpz}, Ref{AnticNumberField}), getindex_raw(C, i, j), dA[i]*dB[j], K)
        reduce!(getindex_raw(C, i, j), K)
      end
    end
  end
  return C
end

export NfMatElem

end # NfMatModule

module TestNfMatMul
using Hecke
using Main.NfMatModule

function test_mul(k::AnticNumberField, a::Int, r::AbstractVector{fmpz})
  return test_mul(k, a, a, a, r)
end

function test_mul(k::AnticNumberField, a::Int, b::Int, c::Int, r::AbstractVector{fmpz})
  M = matrix(k, a, b, [rand(k, r) for i=1:a*b])
  N = matrix(k, b, c, [rand(k, r) for i=1:b*c])
  C = zero_matrix(k, a, c)
  m = Generic.Mat{nf_elem}(M)
  n = Generic.Mat{nf_elem}(N)
  Base.GC.gc()
  @time m*n
  Base.GC.gc()
  @time M*N
  if isdefined(Main, :Strassen)
    Base.GC.gc()
    @time Strassen.mul_strassen!(C, M, N)
  end
  Base.GC.gc()
  @time NfMatModule.mul_new(M, N)
  Base.GC.gc()
  @time NfMatModule.mul_KS(M, N)
end

end
