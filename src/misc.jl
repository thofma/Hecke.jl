import Base: isprime, dot, convert, isless, log
export basis, basis_mat, simplify_content, element_reduce_mod, inv_basis_mat,
       pseudo_inverse, denominator, submat, index, degree, sub,
       next_prime, element_is_in_order, valuation, is_smooth, is_smooth_init,
       discriminant, dot, hnf, _hnf, modular_hnf, representation_mat,
       signature, howell_form!, howell_form, _hnf_modular, isless

################################################################################
# given a basis (an array of elements), get a linear combination with
# random integral coefficients
################################################################################

function rand(b::Array{nf_elem,1}, r::UnitRange)
  s = zero(b[1].parent)
  t = zero(b[1].parent)
  for i = 1:length(b)
    Nemo.mul!(t, b[i], Base.rand(r))
    Nemo.add!(s, t, s)
  end
  return s
end

# rand

function rand_into!(b::Array{nf_elem,1}, r::UnitRange, c::nf_elem)
  Nemo.mul!(c, b[1], rand(r))
  t = zero(b[1].parent)  # this still needs to go ...
  for i = 1:length(b)
    Nemo.mul!(t, b[i], rand(r))
    Nemo.add!(c, t, c)
  end
  return c
end

# rand!


################################################################################
#
# A bunch of fmpz_mat functions, prossible should be in C or the other file
#
################################################################################

################################################################################
# computes tuple (mat, den) over Z sth. a*mat = den*Id
################################################################################

function pseudo_inverse(a::fmpz_mat)
  I = parent(a)(1) # the identity matrix
  I, d = solve(a, I)
  return I, d
end 

function pseudo_inverse(X::Tuple{fmpz_mat, fmpz})
  i, d_i = pseudo_inverse(X[1])
  i *= X[2]
  i, d_i = simplify_content(i, d_i)
  return (i,d_i)
end

################################################################################
# gcd of the entries of a
################################################################################

function simplify_content(a::fmpz_mat, d::fmpz)
  c = content(a)
  d = gcd(c, d)
  if c != 1 
    a = divexact(a, c)
    d = div(d, c)
  end
  return a, d
end


################################################################################
# same as reduce_mod - but with the symmetrix residue system
################################################################################

function reduce_mod_sym(M::fmpz_mat, m::fmpz)
  m = ZZ(m)
  M = parent(M)(M)
  m2 = div(m+1, 2)
  for i = 1:rows(M)
    for j = 1:cols(M)
      a = mod(M[i,j], m)
      if a > m2 
        M[i,j] = a-m
      else
        M[i,j] = a
      end
    end
  end
  return M
end


function reduce_mod_sym(M::fmpz_mat, m::Integer)
  m = ZZ(m)
  M = parent(M)(M)
  m2 = div(m+1, 2)
  for i = 1:rows(M)
    for j = 1:cols(M)
      a = mod(M[i,j], m)
      if a > m2 
        M[i,j] = a-m
      else
        M[i,j] = a
      end
    end
  end
  return M
end

function reduce_mod_sym(M::fmpz_mat, m::fmpz)
  M = parent(M)(M)
  m2 = div(m+1, 2)
  for i = 1:rows(M)
    for j = 1:cols(M)
      a = mod(M[i,j], m)
      if a > m2 
        M[i,j] = a-m
      else
        M[i,j] = a
      end
    end
  end
  return M
end

#
################################################################################
# possibly a slice or window in fmpz_mat?
# the nr x nc matrix starting in (a,b)
################################################################################

function submat(A::fmpz_mat, a::Int, b::Int, nr::Int, nc::Int)
  @assert nr >= 0 && nc >= 0
  M = MatrixSpace(FlintZZ, nr, nc)()::fmpz_mat
  t = ZZ()
  for i = 1:nr
    for j = 1:nc
      getindex!(t, A, a+i-1, b+j-1)
      M[i,j] = t
    end
  end
  return M
end

function submat{T <: Integer}(A::fmpz_mat, r::UnitRange{T}, c::UnitRange)
  @assert !isdefined(r, :step) || r.step==1
  @assert !isdefined(c, :step) || c.step==1
  return submat(A, r.start, c.start, r.stop-r.start+1, c.stop-c.start+1)::fmpz_mat
end


function sub(A::fmpz_mat, r::UnitRange, c::UnitRange)
  @assert !isdefined(r, :step) || r.step==1
  @assert !isdefined(c, :step) || c.step==1
  return submat(A, r.start, c.start, r.stop-r.start+1, c.stop-c.start+1)::fmpz_mat
end

################################################################################
#
# same as reduce_mod - but with the symmetric residue system
#
# needs an inplace variant
################################################################################

function element_reduce_mod(a::nf_elem, bas::Tuple{fmpz_mat, Integer}, inv_bas::Tuple{fmpz_mat, Integer}, m::Integer)
  #
  #assumes that the element is integral wrt to the basis.
  #
  n = degree(parent(a))
  M = MatrixSpace(ZZ, 1, n)();
  d_a = denominator(a)
  element_to_mat_row!(M, 1, a*d_a);
  b, d = inv_bas
  M = divexact(M*b, d*d_a)
  M = reduce_mod_sym(M, m)
  d, b = bas
  M = M*d
  s = element_from_mat_row(parent(a), M, 1)
  return divexact(s,b)
end 

function element_reduce_mod(a::nf_elem, bas::Tuple{fmpz_mat, fmpz}, inv_bas::Tuple{fmpz_mat, fmpz}, m::fmpz)
  #
  #assumes that the element is integral wrt to the basis.
  #
  n = degree(parent(a))
  M = MatrixSpace(ZZ, 1, n)();
  d_a = denominator(a)
  element_to_mat_row!(M, 1, a*d_a);
  b, d = inv_bas
  M = divexact(M*b, d*d_a)
  M = reduce_mod_sym(M, m)
  d, b = bas
  M = M*d
  s = element_from_mat_row(parent(a), M, 1)
  return divexact(s,b)
end 


################################################################################
#
#
# integer stuff - probably already in c somewhere
#
#
# Note: isprime currently is not a proof in julia
################################################################################

function next_prime(z::Integer)
  if z == Integer(1) || z == Integer(0)
    return Integer(2)
  end
  if iseven(z)
    z += 1
  else z += 2
  end
  while !isprime(z)
    z += 2
  end
  return z
end

# should be Bernstein'ed: this is slow for large valuations
# returns the maximal v s.th. z mod p^v == 0 and z div p^v
#   also useful if p is not prime....
function valuation{T <: Integer, S <: Integer}(z::T, p::S)
  assert(z!=0) # can't handle infinity yet
  v = 0
  while mod(z, p)==0
    z = div(z, p)
    v += 1
  end
  return v, z
end 
function valuation{T <: Integer, S <: Integer}(z::Rational{T}, p::S)
  assert(z!=0) # can't handle infinity yet
  v, d = valuation(den(z), p)
  w, n = valuation(num(z), p)
  return w-v, n//d
end 

function valuation(z::fmpz, p::fmpz)
  assert(z!=0) # can't handle infinity yet
  v = 0
  while mod(z, p)==0
    z = div(z, p)
    v += 1
  end
  return v, z
end 
function valuation(z::fmpq, p::fmpz)
  assert(z!=0) # can't handle infinity yet
  v, d = valuation(den(z), p)
  w, n = valuation(num(z), p)
  return w-v, n//d
end 



################################################################################
#
#  fmpq_poly with denominator 1 to fmpz_poly
#
################################################################################

function Base.call(a::FmpzPolyRing, b::fmpq_poly)
  (den(b) != 1) && error("denominator has to be 1")
  temp = fmpz[]
  for i in 0:degree(b)
    push!(temp, num(coeff(b,i)))
  end
  z = fmpz_poly(temp)
  z.parent = a
  return z
end


################################################################################
#
#  positive remainder
#
################################################################################

function prem{T<:Integer}(a::Integer, m::T)
  b = a % m
  if b < 0
    return m+b
  else
    return b
  end
end

function prem{T}(a::fmpz, m::T)
  return prem(BigInt(a), m)
end
     
function *(a::fmpz, b::BigFloat)
  return BigInt(a)*b
end

function Float64(a::fmpz)
  return ccall((:fmpz_get_d, :libflint), Float64, (Ptr{fmpz},), &a)
end

function BigFloat(a::fmpq)
  r = BigFloat(0)
  ccall((:fmpq_get_mpfr, :libflint), Void, (Ptr{BigFloat}, Ptr{fmpq}, Int32), &r, &a, Base.MPFR.ROUNDING_MODE[end])
  return r
end

function isless(a::Float64, b::fmpq) return a<b*1.0; end
function isless(a::fmpq, b::Float64) return a*1.0<b; end

function isless(a::Float64, b::fmpz) return a<b*1.0; end
function isless(a::fmpz, b::Float64) return a*1.0<b; end

function Base.call(a::FlintIntegerRing, b::fmpq)
  den(b) != 1 && error("denominator not 1")
  return a(num(b))
end

# Bernstein: coprime bases
# ppio(a,b) = (c,n) where v_p(c) = v_p(a) if v_p(b) !=0, 0 otherwise
#                         c*n = a
# or c = gcd(a, b^infty)

function ppio(a::fmpz, b::fmpz) 
  c = gcd(a, b)
  n = div(a, c)
  m = c
  g = gcd(c, n)
  while g != 1
    c = c*g
    n = div(n, g)
    g = gcd(c, n)
  end
  return (c, n)
end

function ppio(a::Integer, b::Integer) 
  c = gcd(a, b)
  n = div(a, c)
  m = c
  g = gcd(c, n)
  while g != 1
    c = c*g
    n = div(n, g)
    g = gcd(c, n)
  end
  return (c, n)
end


function denominator(a::nf_elem)                                           
  d_den = fmpz()::fmpz
  ccall((:nf_elem_get_den, :libflint), Void,                                                              
    (Ptr{fmpz}, Ptr{nf_elem}, Ptr{AnticNumberField}),
    &d_den, &a, &parent(a))                                             
  return d_den                                                             
end

function basis(K::AnticNumberField)
  n = degree(K)
  g = gen(K);
  d = Array(typeof(g), n)
  b = K(1)
  for i = 1:n-1
    d[i] = b
    b *= g
  end
  d[n] = b
  return d
end

function element_to_mat_row!(a::fmpz_mat, i::Int, b::nf_elem)
  ccall((:nf_elem_to_mat_row, :libflint), 
        Void, 
       (Ptr{Nemo.fmpz_mat}, Int32, Ptr{nf_elem}, Ptr{AnticNumberField}), 
       &a, Int32(i-1), &b, &parent(b))
end

const d_from = fmpz(1)
function element_from_mat_row(K::AnticNumberField, a::fmpz_mat, i::Int)
  global d_from::fmpz
  b = K();
  ccall((:nf_elem_from_mat_row, :libflint), 
        Void, 
       (Ptr{nf_elem}, Ptr{fmpz_mat}, Int, Ptr{AnticNumberField}),
       &b, &a, i-1, &parent(b))
  set_denominator!(b, d_from)     
  return b
end

dot(x::nf_elem, y::Int64) = x*y

dot(x::nf_elem, y::fmpz) = x*y

function representation_mat(a::nf_elem)
  @assert denominator(a) == 1
  n = degree(a.parent)
  M = MatrixSpace(FlintZZ, n,n)()::fmpz_mat
  t = gen(a.parent)
  b = a
  for i = 1:n-1
    element_to_mat_row!(M, i, b)
    b *= t
  end
  element_to_mat_row!(M, n, b)
  return M
end 

function set_denominator!(a::nf_elem, d::fmpz)
  ccall((:nf_elem_set_den, :libflint), 
        Void, 
       (Ptr{Nemo.nf_elem}, Ptr{Nemo.fmpz}, Ptr{Nemo.AnticNumberField}), 
       &a, &d, &parent(a))
end

function factor_dict(A::BigInt)
  D = Dict{BigInt, Int}()
  a = factor(A)
  for i = 1:a.len 
    D[a.d[i][1]] = a.d[i][2]
  end
  return D
end

function factor_dict(A::fmpz)
  D = Dict{fmpz, Int}()
  a = factor(A)
  for i = 1:a.len 
    D[a.d[i][1]] = a.d[i][2]
  end
  return D
end

################################################################################
################################################################################
#
# other stuff:
#  fmpz_mat -> Array(BigInt, 2)
#
################################################################################
################################################################################
function Array(a::fmpz_mat)
  A = Array(BigInt, rows(a), cols(a))
  for i = 1:rows(a)
    for j = 1:cols(a)
      A[i,j] = a[i,j]
    end 
  end
  return A
end


################################################################################
#
# other stuff:
#  export various types to a Magma or Nemo readable file
#
################################################################################
# fmpz_mat -> nemo file
# use as include(...)
################################################################################
function toNemo(io::IOStream, A::fmpz_mat; name = "A")
  println(io, name, " = MatrixSpace(ZZ, ", rows(A), ", ", cols(A), ")([")
  for i = 1:rows(A)
    for j = 1:cols(A)
      print(io, A[i,j])
      if j < cols(A)
        print(io, " ")
      end
    end
    if i<rows(A)
      println(io, ";")
    end
  end
  println(io, "]);")
  println(io, "println(\"Loaded ", name, "\")")
end

function toNemo(s::ASCIIString, A::fmpz_mat)
  f = open(s, "w")
  toNemo(f, A)
  close(f)
end

################################################################################
# fmpz_mat -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, A::fmpz_mat; name = "A")
  println(io, name, " := Matrix(Integers(), ", rows(A), ", ", cols(A), ", [")
  for i = 1:rows(A)
    for j = 1:cols(A)
      print(io, A[i,j])
      if j < cols(A)
        print(io, ", ")
      end
    end
    if i<rows(A)
      println(io, ",")
    end
  end
  println(io, "]);")
  println(io, "\"Loaded ", name, "\";")
end

function toMagma(s::ASCIIString, A::fmpz_mat)
  f = open(s, "w")
  toMagma(f, A)
  close(f)
end

################################################################################
# Smat -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, A::Smat; name = "A")
  println(io, name, " := SparseMatrix(Integers(), ", rows(A), ", ", cols(A), ", [")
  for i = 1:rows(A)
    for xx = 1:length(A.rows[i].entry) 
      x = A.rows[i].entry[xx]
      print(io, "<", i, ", ", x.col, ", ", x.val, ">")
      if xx < length(A.rows[i].entry) || i<rows(A)
        print(io, ", ")
      end
    end
    println(io, "")
  end
  println(io, "]);")
  println(io, "\"Loaded ", name, "\";")
end

function toMagma(s::ASCIIString, A::Smat)
  f = open(s, "w")
  toMagma(f, A)
  close(f)
end

*(a::fmpz, b::nf_elem) = b * a

function is_zero_row(M::fmpz_mat, i::Int)
  for j = 1:cols(M)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row{T}(M::MatElem{T}, i::Int)
  for j in 1:cols(M)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

function is_zero_row{T <: Integer}(M::Array{T, 2}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row(M::Array{fmpz, 2}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row(M::Array{fmpz, 2}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row{T <: RingElem}(M::Array{T, 2}, i::Int)
  for j in 1:Base.size(M, 2)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

#computes (hopefully) the hnf for vcat(a*I, m) and returns ONLY the
#non-singular part. By definition, the result wil have full rank
#
#Should be rewritten to use Howell and lifting rather the big HNF
#
function modular_hnf(m::fmpz, a::fmpz_mat, shape::Symbol = :upperright)
  c = vcat(parent(a)(m), a)
  n = cols(a)
  w = window(c, n+1, 1, 2*n, n)
  ccall((:fmpz_mat_scalar_mod_fmpz, :libflint), Void, (Ptr{fmpz_mat}, Ptr{fmpz_mat}, Ptr{fmpz}), &w, &w, &m)
  if shape == :lowerleft
    c = _hnf(c, shape)
    return sub(c, n+1:2*n, 1:n)
  else
    c = hnf(c)
    c = sub(c, 1:n, 1:n)
  end
end

function _lift_howell_to_hnf(x::nmod_mat)
# Assume that x is square, in howell normal form and all non-zero rows are at the bottom
# NOTE: _OUR_ Howell normal form algorithm always puts the rows at the right position
# If row i is non-zero then i is the rightmost non-zero entry
# Thus lifting is just replacing zero diagonal entries
  !issquare(x) && error("Matrix has to be square")
  y = lift_unsigned(x)
  for i in cols(y):-1:1
    z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &y, i - 1, i - 1)
    if Bool(ccall((:fmpz_is_zero, :libflint), Int, (Ptr{fmpz}, ), z))
#      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &y, 0, i - 1)
      ccall((:fmpz_set_ui, :libflint), Void, (Ptr{fmpz}, UInt), z, x._n)
#      for k in 1:i-1
#        _swaprows!(y, k, k+1)
#      end
    end
  end
  return y
end

function submat{T <: Integer}(x::nmod_mat, r::UnitRange{T}, c::UnitRange{T})
  z = deepcopy(window(x, r, c))
  return z
end

function submat{T <: Integer}(x::fmpz_mat, r::UnitRange{T}, c::UnitRange{T})
  z = deepcopy(window(x, r, c))
  return z
end

function _hnf_modular(x::fmpz_mat, m::fmpz, shape::Symbol = :lowerleft)
  if abs(m) < fmpz(typemax(UInt))
    y = MatrixSpace(ResidueRing(FlintZZ, m), rows(x), cols(x))(x)
    howell_form!(y, shape)
    y = submat(y, rows(y) - cols(y) + 1:rows(y), 1:cols(y))
    return _lift_howell_to_hnf(y)
  end
  return __hnf_modular(x, m, shape)
end

function __hnf_modular(x::fmpz_mat, m::fmpz, shape::Symbol = :lowerleft)
# See remarks above
  y = deepcopy(x)
  howell_form!(y, m, shape)
  y = submat(y, rows(y) - cols(y) + 1:rows(y), 1:cols(y))
  for i in cols(y):-1:1
    z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &y, i - 1, i - 1)
    if Bool(ccall((:fmpz_is_zero, :libflint), Int, (Ptr{fmpz}, ), z))
    #if ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, i - 1, i - 1) == 0
#      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &y, 0, i - 1)
      ccall((:fmpz_set, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), z, &m)
#      for k in 1:i-1
#        _swaprows!(y, k, k+1)
#      end
    end
  end
  return y
end

function _hnf(x::fmpz_mat, shape::Symbol = :upperright)
  if shape == :lowerleft
    h = hnf(_swapcols(x))
    _swapcols!(h)
    _swaprows!(h)
    return h::fmpz_mat
  end
  return hnf(x)::fmpz_mat
end


function howell_form!(x::fmpz_mat, m::fmpz, shape::Symbol = :upperright)
  if shape == :lowerleft
    _swapcols!(x)
    ccall((:_fmpz_mat_howell, :libflint), Int, (Ptr{fmpz_mat}, Ptr{fmpz}), &x, &m)
    _swapcols!(x)
    _swaprows!(x)
  else
    ccall((:_fmpz_mat_howell, :libflint), Int, (Ptr{fmpz_mat}, Ptr{fmpz}), &x, &m)
  end
end

function howell_form(x::fmpz_mat, m::fmpz, shape::Symbol = :upperright)
  y = deepcopy(x)
  howell_form!(y, m, shape)
  return y
end

function howell_form!(x::nmod_mat, shape::Symbol = :upperright)
  if shape == :lowerleft
    _swapcols!(x)
    ccall((:_nmod_mat_howell, :libflint), Int, (Ptr{nmod_mat}, ), &x)
    _swapcols!(x)
    _swaprows!(x)
  else
    ccall((:_nmod_mat_howell, :libflint), Int, (Ptr{nmod_mat}, ), &x)
  end
end

function howell_form(x::nmod_mat, shape::Symbol = :upperright)
  y = deepcopy(x)
  howell_form!(y, shape)
  return y
end

function _swaprows(x::fmpz_mat)
  y = deepcopy(x)
  _swaprows!(y)
  return y
end

function _swapcols(x::fmpz_mat)
  y = deepcopy(x)
  _swapcols!(y)
  return y
end

function _swaprows!(x::fmpz_mat)
  r = rows(x)
  c = cols(x)

  if r == 1
    return x
  end

  if r % 2 == 0
    for i in 1:div(r,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, i - 1, j - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, (r - i + 1) - 1, j - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  else
    for i in 1:div(r-1,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, i - 1, j - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, (r - i + 1) - 1, j - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  end
  nothing
end

function _swaprows!(x::fmpz_mat, i::Int, j::Int)
  ccall((:_fmpz_mat_swap_rows, :libflint), Void, (Ptr{fmpz_mat}, Int, Int), &x, i-1, j-1)
  nothing
end

function _swaprows!(x::nmod_mat, i::Int, j::Int)
  ccall((:_nmod_mat_swap_rows, :libflint), Void, (Ptr{nmod_mat}, Int, Int), &x, i-1, j-1)
#  for k in 1:rows(x)
#    s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Lim, (Ptr{nmod_mat}, Int, Int), &x, i, k)
#    t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Lim, (Ptr{nmod_mat}, Int, Int), &x, j, k)
#    set_entry!(x, i, k, t)
#    set_entry!(y, j, k, s)
#  end
  nothing
end
  

function _swaprows!(x::nmod_mat)
  r = rows(x)
  c = cols(x)

  if r == 1
    return nothing
  end

  if r % 2 == 0
    for i in 1:div(r,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, i - 1, j - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, (r - i + 1) - 1, j - 1)
        set_entry!(x, r - i + 1, j, s)
        set_entry!(x, i, j, t)
      end
    end
  else
    for i in 1:div(r-1,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, i - 1, j - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, (r - i + 1) - 1, j - 1)
        set_entry!(x, i, j, t)
        set_entry!(x, r - i + 1, j, s)
      end
    end
  end
  nothing
end

function _swapcols!(x::nmod_mat)
  r = rows(x)
  c = cols(x)

  if c == 1
    return nothing
  end

  if c % 2 == 0
    for i in 1:div(c,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, j - 1, i - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, j - 1, (c - i + 1 ) - 1)
        set_entry!(x, j, i, t)
        set_entry!(x, j, c - i + 1, s)
      end
    end
  else
    for i in 1:div(c-1,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, j - 1, i - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, j - 1, (c - i + 1 ) - 1)
        set_entry!(x, j, i, t)
        set_entry!(x, j, c - i + 1, s)
      end
    end
  end
  nothing
end


function _swapcols!(x::fmpz_mat)
  r = rows(x)
  c = cols(x)

  if c == 1
    return x
  end

  if c % 2 == 0
    for i in 1:div(c,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, j - 1, i - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, j - 1, (c - i + 1 ) - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  else
    for i in 1:div(c-1,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, j - 1, i - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, j - 1, (c - i + 1 ) - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  end
  nothing
end

################################################################################
#
#  Signature 
#
################################################################################

function signature(x::fmpz_poly)
  r = Array(Int, 1)
  s = Array(Int, 1)
  ccall((:fmpz_poly_signature, :libflint), Void, (Ptr{Int}, Ptr{Int}, Ptr{fmpz_poly}), r, s, &x)
  return (r[1],s[1])
end

function signature(x::fmpq_poly)
  R = PolynomialRing(FlintZZ, "x")[1]
  return signature(R(x))
end

function signature(K::AnticNumberField)
  return signature(K.pol)
end

################################################################################
##
################################################################################

function basis_mat(K::AnticNumberField, b::Array{nf_elem, 1})
  d = denominator(b[1])
  n = degree(K)
  for i = 2:n
    d = Base.lcm(d, denominator(b[i]))
  end
  M = MatrixSpace(ZZ, n,n)()
  for i = 1:n
    element_to_mat_row!(M, i, b[i]*d)
  end
  return M, d
end 


################################################################################
##
################################################################################

function //(a::fmpq, b::fmpz)
  return a//fmpq(b)
end

function //(a::fmpz, b::fmpq)
  return fmpq(a)//b
end

function *(a::fmpz, b::Float64)
  return BigInt(a)*b
end

function *(b::Float64, a::fmpz)
  return BigInt(a)*b
end

function *(a::fmpq, b::Float64)
  return Rational(a)*b
end

function *(b::Float64, a::fmpq)
  return Rational(a)*b
end

function Float64(a::fmpq)
  b = a*fmpz(2)^53
  Float64(div(num(b), den(b)))/Float64(2^53)
end

function convert(R::Type{Rational{Base.GMP.BigInt}}, a::Nemo.fmpz)
  return R(BigInt(a))
end

log(a::fmpz) = log(BigInt(a))
log(a::fmpq) = log(num(a)) - log(den(a))
################################################################################
# 
################################################################################

function max(a::fmpz_mat)
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &a, 0,0)
  for i=1:rows(a)
    for j=1:cols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &a, i-1, j-1)
      if ccall((:fmpz_cmpabs, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_abs, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), &r, m)
  return r
end

function lift_unsigned(a::nmod_mat)
  z = MatrixSpace(FlintZZ, rows(a), cols(a))()
  ccall((:fmpz_mat_set_nmod_mat_unsigned, :libflint), Void,
          (Ptr{fmpz_mat}, Ptr{nmod_mat}), &z, &a)
  return z
end

dot(x::BigInt, y::NfOrderElem) = x * y

colon(start::fmpz, stop::fmpz) = StepRange(start, fmpz(1), stop)

function round(a::fmpq)
  n = num(a)
  d = den(a)
  q = div(n, d)
  r = mod(n, d)
  if r >= d//2
    return q+1
  else
    return q
  end
end

function basis_rels(b::Array{nf_elem, 1}, c; bd::fmpz = fmpz(10^35), no_p::Int = 4, no_rel::Int = 10000, no_coeff::Int = 4 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = fmpz(1)
  for i=1:no_rel
    zero!(a)
    for j=1:no_coeff
      cf = rand([-1, 1])
      p  = rand(1:nb)
      if cf==1
        Nemo.add!(a, a, b[p])
      else
        Nemo.sub!(a, a, b[p])
      end
    end
    n = norm_div(a, one, no_p)
    if cmpabs(num(n), bd) <= 0 
      if class_group_add_relation(c, a, n, one)
        a = b[1].parent()
      end
    end
  end
end


function rels_stat(b::Array{hecke.nf_elem, 1}; no_p = 4, no_rel::Int = 10000, no_coeff::Int = 4 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = fmpz(1)

  stat = Dict{Int, Int}()
  for i=1:no_rel
    zero!(a)
    for j=1:no_coeff
      p  = rand(1:nb)
      Nemo.add!(a, a, b[p])
    end
    n = norm_div(a, one, no_p)
    k - Int(round(log(abs(n))))
    if isdefined(stat, k)
      stat[k] += 1
    else
      stat[k] = 1
    end
  end
  return stat
end

