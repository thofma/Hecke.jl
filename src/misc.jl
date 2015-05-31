import Base: isprime
export basis, basis_mat, simplify_content, element_reduce_mod, inv_basis_mat,
       pseudo_inverse, denominator, submat, index, degree,
       next_prime, element_is_in_order, valuation, is_smooth, is_smooth_init,
       discriminant

################################################################################
#
# Support stuff for number fields, stuff that need orders and fields
# and thus is in a different file.
#
################################################################################

################################################################################
# basis of an (Pari)Order as array of elements in the field
################################################################################

function basis(K::NfNumberField, O::PariMaximalOrder)
  if isdefined(O, :basis)
    return O.basis
  end
  n = degree(K)
  d = Array(typeof(K(0)), n)
  b = Nemo.basis(O)
  Qx = K.pol.parent
  for i = 1:n 
    d[i] = K(Qx(b[i]))
  end
  O.basis = d
  return d
end

################################################################################
# the same basis, but the elements (the coefficients) are put into a marix
# The matrix is put on a common denominator.
# returns a tuple (mat, den)
# the result is cached in the order
################################################################################

function basis_mat(K::NfNumberField, O::PariMaximalOrder)
  if isdefined(O, :basis_mat) 
    return O.basis_mat
  end
  b = basis(K, O)
  d = denominator(b[1])
  n = degree(K)
  for i = 2:n
    d = lcm(d, denominator(b[i]))
  end
  M = MatrixSpace(ZZ, n,n)()
  for i = 1:n
    element_to_mat_row!(M, i, b[i]*d)
  end
  O.basis_mat = M, d
  return M, d
end 

################################################################################
# The pseudo inverse of the above matrix
# the result is cached in the order
################################################################################

function inv_basis_mat(K::NfNumberField, O::PariMaximalOrder)
  if isdefined(O, :inv_basis_mat) 
    return O.inv_basis_mat
  end
  b, d_b = basis_mat(K, O)
  i, d_i = pseudo_inverse(b)
  i *= d_b
  i, d_i = simplify_content(i, d_i)
  O.inv_basis_mat = i, d_i
  return i, d_i
end 


################################################################################
# given a basis (an array of elements), get a linear combination with
# random integral coefficients
################################################################################

function rand(b::Array{nf_elem,1}, r::UnitRange)
  s = zero(b[1].parent)
  t = zero(b[1].parent)
  for i = 1:length(b)
    Nemo.mult_into!(b[i], Base.rand(r), t)
    Nemo.add_into!(s, t, s)
  end
  return s
end

# rand

function rand_into!(b::Array{nf_elem,1}, r::UnitRange, c::nf_elem)
  Nemo.mult_into!(b[1], rand(r), c)
  t = zero(b[1].parent)  # this still needs to go ...
  for i = 1:length(b)
    Nemo.mult_into!(b[i], rand(r), t)
    Nemo.add_into!(c, t, c)
  end
  return c
end

# rand!



################################################################################
# The index of the equation order (Z[x]/pol) in the maximal order
################################################################################

function index(O::PariMaximalOrder)
  if isdefined(O, :index)
    return O.index
  end
  K = O.pari_nf.nf
  b = basis_mat(K, O)
  O.index = b[2]^degree(K)//determinant(b[1])
  return O.index
end

function degree(O::PariMaximalOrder)
  return degree(O.pari_nf.nf)
end

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
# possibly a slice or winwod in fmpz_mat?
# the nr x nc matrix starting in (a,b)
################################################################################

function submat(A::fmpz_mat, a::Int, b::Int, nr::Int, nc::Int)
  @assert nr >= 0 && nc >= 0
  M = MatrixSpace(ZZ, nr, nc)()
  t = ZZ()
  for i = 1:nr
    for j = 1:nc
      M[i,j] = getindex!(t, A, a+i-1, b+j-1)
    end
  end
  return M
end

function sub(A::fmpz_mat, r::UnitRange, c::UnitRange)
  @assert !isdefined(r, :step) || r.step==1
  @assert !isdefined(c, :step) || c.step==1
  return submat(A, r.start, c.start, r.stop-r.start+1, c.stop-c.start+1)
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


function element_reduce_mod(a::nf_elem, O::PariMaximalOrder, m::Integer)
  K = parent(a)
  return element_reduce_mod(a, basis_mat(K, O), inv_basis_mat(K, O), m)
end 

function element_reduce_mod(a::nf_elem, O::PariMaximalOrder, m::fmpz)
  K = parent(a)
  return element_reduce_mod(a, basis_mat(K, O), inv_basis_mat(K, O), m)
end 



################################################################################
#
# boolean function: test membership
#
################################################################################

function element_is_in_order(a::nf_elem, O::PariMaximalOrder)
  K = parent(a)
  n = degree(K)
  M = MatrixSpace(ZZ, 1, n)();
  d_a = denominator(a)
  element_to_mat_row!(M, 1, a*d_a);
  b, d = inv_basis_mat(K, O)
  M = M*b
  for i = 1:n
    if mod(M[1,i], d*d_a) != 0
#      println("M is", M, " dens are ", d, " and ", d_a, " index i=", i)
      return false
    end
  end
#  println ("basis rep is ", divexact(M, d*d_a))
  return true
end

################################################################################
# the denominator of a in the field wrt to the order O
################################################################################

function denominator(a::nf_elem, O::PariMaximalOrder)
  n = degree(parent(a))
  M = MatrixSpace(ZZ, 1, n)();
  d_a = denominator(a)
  element_to_mat_row!(M, 1, a*d_a);
  b, d = inv_basis_mat(parent(a), O)
  M = divexact(M*b, d)
  c = content(M)
  return div(d_a, gcd(d_a, c))
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
# smoothness test and factorisation over a factor base
# not optimal or even good....
# hopefully a stable API
#
################################################################################

type smooth_ctx{T}
  prod::T
  base::Set{T}
end

function is_smooth_init{T}(r::Set{T})
  c = smooth_ctx(prod(r), r)
  return c
end

function is_smooth{T}(c::smooth_ctx{T}, a::T)
  g = gcd(c.prod, a)
  while g != 1 
    a = div(a, g)
    g = gcd(g, a)
  end
  return a == 1
end

function factor{T}(c::smooth_ctx{T}, a::T)
  f = Dict{T, Int}()
  for i in c.base
    if mod(a, i)==0
      v = valuation(a, i)
      f[i] = v[1]
      a = v[2]
      if a == 1 
        break
      end
    end
  end
  assert(a==1)
  return f
end

function factor{T}(c::smooth_ctx{T}, a::fmpq)
  f = Dict{T, Int}()
  n = num(a)
  d = den(a)
  for i in c.base
    if mod(d, i)==0
      v = valuation(d, i)
      if isdefined(f, :i)
        f[i] -= v[1]
      else
        f[i] = -v[1]
      end
      d = v[2]
      if d == 1 && n == 1
        break
      end
    end
    if mod(n, i)==0
      v = valuation(n, i)
      if isdefined(f, :i)
        f[i] += v[1]
      else
        f[i] = v[1]
      end
      n = v[2]
      if d == 1 && n==1
        break
      end
    end
  end
  @assert d==1 && n==1 
  return f
end

###############################################################################
#
#   discriminant of maximal order ...
#
###############################################################################

function discriminant(O::PariMaximalOrder)
  K = O.pari_nf.nf  
  f = K.pol
  R = parent(f)
  Sy,y = PolynomialRing(ZZ,"y")
  coef = typeof(ZZ(0))[]
  for i in 0:degree(f)
    push!(coef,ZZ(coeff(f,i)))
  end
  g = Sy(coef)
  disc = div(discriminant(g),ZZ(index(O))^2)
  return disc
end

################################################################################
#
#  fmpq_poly with denominator 1 to fmpz_poly
#
################################################################################

function Base.call(a::FmpzPolyRing, b::fmpq_poly)
  (denominator(b) != 1) && error("denominator has to be 1")
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
  return Float64(BigInt(a))
end

function Float64(a::fmpq)
  return Float64(BigInt(num(a))//BigInt(den(a)))
end

function BigFloat(a::fmpq)
  return BigFloat(BigInt(num(a))//BigInt(den(a)))
end


function Base.call(a::IntegerRing, b::fmpq)
  den(b) != 1 && error("denominator not 1")
  return ZZ(num(b))
end

# Berstein: coprime bases
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

