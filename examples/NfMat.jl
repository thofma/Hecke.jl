module NfMatModule

using Hecke
import Nemo

struct nf_elem_raw
  a::Clong
  b::Clong
  c::Clong
  d::Clong
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
    #= Not neccessary - as all entries are 0
      for deg 1: 0 is a valid fmpz in num and den
              2  0 is valid (4 fmpz)
              ?  all coeff. ptr are 0 as alloc is also 0
      for i=1:c*r
        ccall((:nf_elem_init, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), pointer(entries, i), K)
      end
      slight correction: all dens need to be 1. For 
        deg == 2 via one()
        otherwise zero()
     =#
      
    rows = zeros(Int, r)
    for i=1:r
      rows[i] = (i-1)*c
    end
    M = new(entries, rows, r, c, K)
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
end

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

function Hecke.matrix(K::AnticNumberField, r::Int, c::Int, a::Vector{nf_elem})
  M = NfMatElem(K, r, c)
  for i=1:r
    for j=1:c
      M[i,j] = a[(i-1)*c+j]
    end
  end
  return M
end

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

function Array(M::NfMatElem)
  return collect(M)
end

function Generic.Mat{nf_elem}(M::NfMatElem)
  N =  Generic.MatSpaceElem{nf_elem}(Array(M))
  N.base_ring = M.base_ring
  return N
end

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

function NfMatElem_clear1(en::Vector{nf_elem_raw})
  #degree 1 case...
  for i=1:length(en)
    p = pointer(en, i)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
    p += sizeof(Clong)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
  end
end

function NfMatElem_clear2(en::Vector{nf_elem_raw})
  for i=1:length(en)
    p = pointer(en, i)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
    p += sizeof(Clong)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
    p += sizeof(Clong)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
    p += sizeof(Clong)
    ccall((:fmpz_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw}, ), p)
  end
end

function NfMatElem_clear3(en::Vector{nf_elem_raw})
  for i=1:length(en)
    ccall((:fmpq_poly_clear, Nemo.libflint), Cvoid, (Ptr{nf_elem_raw},), pointer(en, i))
  end
end

function Base.getindex(M::NfMatElem, r::Int, c::Int)
  a = base_ring(M)()
  ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ref{nf_elem}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, pointer(M.entries, M.rows[r]+c), base_ring(M))
  return a
end

function Base.getindex(M::NfMatElem, r::UnitRange{Int}, c::UnitRange{Int})
  N = NfMatElem(base_ring(M), length(r), length(c))
  for i = r
    for j = c
      N[i-r.start+1, j-c.start+1] = M[i,j]
    end
  end
  return N
end

@inline function getindex_raw(M::NfMatElem, r::Int, c::Int)
  en = ent(M)
  ro = rows(M)
  return @inbounds pointer(en, ro[r]+c)
end

function Base.setindex!(M::NfMatElem, a::nf_elem, r::Int, c::Int)
  ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{nf_elem}, Ref{AnticNumberField}), pointer(M.entries, M.rows[r]+c), a, base_ring(M))
end

function Base.setindex!(M::NfMatElem, a::nf_elem_raw, r::Int, c::Int)
  ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{nf_elem_raw}, Ref{AnticNumberField}), pointer(M.entries, M.rows[r]+c), a, base_ring(M))
end

function Base.setindex!(M::NfMatElem, a::Ptr{nf_elem_raw}, r::Int, c::Int)
  ccall((:nf_elem_set, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{nf_elem_raw}, Ref{AnticNumberField}), pointer(M.entries, M.rows[r]+c), a, base_ring(M))
end

Hecke.nrows(M::NfMatElem) = M.nrows
Hecke.ncols(M::NfMatElem) = M.ncols
Hecke.base_ring(M::NfMatElem) = M.base_ring

@inline rows(M::NfMatElem) = M.rows
@inline ent(M::NfMatElem) = M.entries

function Base.show(io::IO, M::NfMatElem)
  print(io, "$(M.nrows) x $(M.ncols) matrix over $(M.base_ring)")
end

function Hecke.iszero_entry(M::NfMatElem, i::Int, j::Int)
  p = getindex_raw(M, i, j)
  return ccall((:nf_elem_is_zero, Nemo.libantic), Cint, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), p, base_ring(M)) == 1
end

function isone_entry(M::NfMatElem, i::Int, j::Int)
  p = getindex_raw(M, i, j)
  return ccall((:nf_elem_is_one, Nemo.libantic), Cint, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), p, base_ring(M)) == 1
end

function mul!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::Ptr{nf_elem_raw}, K::AnticNumberField, red::Bool = true)
  ccall((:nf_elem_mul_red, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}, Cint), a, b, c, K, red)
end

function mul!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::nf_elem, K::AnticNumberField, red::Bool = true)
  ccall((:nf_elem_mul_red, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{nf_elem}, Ref{AnticNumberField}, Cint), a, b, c, K, red)
end

function mul!(a::nf_elem, b::Ptr{nf_elem_raw}, c::Ptr{nf_elem_raw}, K::AnticNumberField, red::Bool = true)
  ccall((:nf_elem_mul_red, Nemo.libantic), Cvoid, (Ref{nf_elem}, Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}, Cint), a, b, c, K, red)
end

function reduce!(a::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_elem_reduce, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, K)
end

function add!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_elem_add, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, b, c, K)
end

function sub!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::Ptr{nf_elem_raw}, K::AnticNumberField)
  ccall((:nf_elem_sub, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), a, b, c, K)
end

function sub!(a::Ptr{nf_elem_raw}, b::Ptr{nf_elem_raw}, c::nf_elem, K::AnticNumberField)
  ccall((:nf_elem_sub, Nemo.libantic), Cvoid, (Ptr{nf_elem_raw}, Ptr{nf_elem_raw}, Ref{nf_elem}, Ref{AnticNumberField}), a, b, c, K)
end

function ref!(M::NfMatElem) #TODO: mul_non_reduce?
  piv = zeros(Int, ncols(M))
  K = base_ring(M)
  t = K()
  for i=1:nrows(M)
    j = 1
    while j <= ncols(M) && Hecke.iszero_entry(M, i, j)
      j += 1
    end
    if j>ncols(M)
      continue
    end
    @inbounds piv[j] = i
    @assert !Hecke.iszero_entry(M, i, j)
    if !isone_entry(M, i, j)
      ccall((:nf_elem_inv, Nemo.libantic), Cvoid, (Ref{nf_elem}, Ptr{nf_elem_raw}, Ref{AnticNumberField}), t, getindex_raw(M, i, j), K)
      k = j
      while k<= ncols(M)
        mul!(getindex_raw(M, i, k), getindex_raw(M, i, k), t, K)
        k += 1
      end
    end
    for r = i+1:nrows(M)
      s = getindex_raw(M, r, j)
      for k=ncols(M):-1:j
        Mrk = getindex_raw(M, r, k)
        mul!(t, s, getindex_raw(M, i, k), K)
        sub!(Mrk, Mrk, t, K)
      end
    end
  end
  return piv
end

function Hecke.rref!(M::NfMatElem)
  pi = ref!(M)
  K = base_ring(M)
  t = K()
  for j = 1:ncols(M)
    @inbounds p = pi[j]
    iszero(p) && continue
    for k=1:p-1
      s = getindex_raw(M, k, j)
      for h=ncols(M):-1:j
        mul!(t, getindex_raw(M, p, h), s, K)
        sub!(getindex_raw(M, k, h), getindex_raw(M, k, h), t, K)
      end
    end
  end
end

end # NfMatModule
