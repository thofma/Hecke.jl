#=
    Copyright (C) 2023-24, Claus Fieker, John Abbott
=#

module Det
using Hecke
import AbstractAlgebra, Nemo
using LinearAlgebra, Profile, Base.Intrinsics
import Nemo: add!, mul!, zero!, sub!
import Hecke: mod_sym!

#creates an unimodular n x n matrix where the inverse is much larger
#than the original matrix. Entries are chosen in U
function rand_mat(n::Int, U::AbstractArray=1:10)
  C = zero_matrix(ZZ, n, n)
  for i=1:n-1
    C[i, i+1] = 1
  end
  for i=2:n
    C[n, i] = rand(U)
  end
  C[n,1] = 1
  for i=2:n-1
    C[i,i] = rand(U)
  end
  return C
end

function rand_hnf(n::Int, U::AbstractArray=1:10)
  C = zero_matrix(ZZ, n, n)
  for i=1:n
    d = rand(U)
    C[i,i] = d
    for j=1:i-1
      if iszero(d)
        C[j,i] = rand(U)
      else
        C[j,i] = rand(0:d-1)
      end
    end
  end
  return C
end

function graeffe(f::PolyRingElem)
#  f = f*f(-gen(parent(f)))
#  return parent(f)([coeff(f, 2*i) for i=0:div(degree(f), 2)])
   f_e = parent(f)([coeff(f, 2*i) for i=0:div(degree(f), 2)])
   f_o = parent(f)([coeff(f, 2*i+1) for i=0:div(degree(f), 2)])
   return (-1)^degree(f)*(f_e^2-shift_left(f_o^2, 1))
end


#applies n unimodular transformations (add scaled row/col)
function perturb!(A, n::Int = 100, c::AbstractRange = -10:10; side::Symbol = :both)
  local rnd::Function
  if side == :left
    rnd = function()
      true
    end
  elseif side == :right
    rnd = function()
      false
    end
  elseif side == :both
    rnd = function()
      rand(0:1) == 1
    end
  else
    error("side has to be :right, :left or :both")
  end
  for i=1:n
    x = rand(c)
    while iszero(x)
      x = rand(c)
    end
    if rnd()
      k = rand(1:nrows(A))
      l = rand(1:nrows(A))
      while l == k
        l = rand(1:nrows(A))
      end
      AbstractAlgebra.add_row!(A, x, k, l)
    else
      k = rand(1:ncols(A))
      l = rand(1:ncols(A))
      while l == k
        l = rand(1:ncols(A))
      end
      AbstractAlgebra.add_column!(A, x, k, l)
    end
  end
end

#takes the result of lu! and turns it into a proper lu
function Nemo.lu(P::Perm, U, r::Int)
  m = nrows(U)
  n = ncols(U)
  R = base_ring(U)
  L = similar(U, m, m)

  for i = 1:m
    for j = 1:n
      if i > j
        L[i, j] = U[i, j]
        U[i, j] = R(0)
      elseif i == j
        L[i, j] = R(1)
      elseif j <= m
        L[i, j] = R(0)
      end
    end
  end
  return r, P, L, U
end

#
# see https://arxiv.org/pdf/1901.00904.pdf
# p2
#
#  A B  = I       0  * A 0 * I A^-1 B
#  C D   C A^-1   I    0 X   0  I
#
# for X = D - C A^-1 B
#
# inv( I A; 0 I) = I -A; 0 I
#
# TODO:
#    inplace
#    pre-alloced tmp for the recursion
#
# only worksing iff A is invertble. In this case magically X is also invertable
# in general need to use lu (lu!_strassen)
# FAST when applicable
function inv_strassen(A::fpMatrix)
#  @show size(A)
  if isodd(ncols(A)) || ncols(A) < 400
    return inv(A)
  end
#  @show :strassen, ncols(A)
  @assert nrows(A) == ncols(A)
  @assert iseven(ncols(A))
  n = div(ncols(A), 2)
  A11 = view(A, 1:n, 1:n)
  A12 = view(A, 1:n, n+1:2*n)
  A21 = view(A, n+1:2*n, 1:n)
  A22 = view(A, n+1:2*n, n+1:2*n)

  A11_i = inv_strassen(A11)
  A11_i_A12 = A11_i*A12
  delta = A22-A21*A11_i_A12
  X22 = delta_i = inv_strassen(delta)
  A21_A11_i = A21*A11_i
  X21 = -delta_i*A21_A11_i
  X12 = -A11_i_A12*delta_i
  X11 = A11_i-A11_i_A12*X21

  X = similar(A)
  ccall((:nmod_mat_set, Hecke.libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), view(X, 1:n, 1:n), X11)
  ccall((:nmod_mat_set, Hecke.libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), view(X, 1:n, n+1:n+n), X12)
  ccall((:nmod_mat_set, Hecke.libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), view(X, n+1:n+n, 1:n), X21)
  ccall((:nmod_mat_set, Hecke.libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), view(X, n+1:n+n, n+1:n+n), X22)

  return X

  return [X11 X12; X21 X22]
end

# Triangular denominator: for a solution matrix "s", given denominator d and A= d*s.
#  Uses presumably the following function
## [17] gcdx(a::ZZRingElem, b::ZZRingElem)
##     @ Nemo ~/OSCAR/GIT/Nemo.jl/src/flint/ZZRingElem.jl:1293
# NOTE: mod(,) seems to return least-non-negative remainder
# Storjohann
function hcol(A::ZZMatrix, d::ZZRingElem)  # why not Vector{ZZRingElem}???
  n = nrows(A)
  w = deepcopy(A)
  g = d
  t = Array(ZZ,n)
  h = zero_matrix(ZZ,n,n)
  s = 1
  v = 1
  for i = 1:n
    k = n-(i-1)
    gg,e,f = gcdx(g,A[k,1])
    t[k] = f
    h[k,k] = g/gg
    g = gg
  end
  for i = 1:n
    if h[i,i] == 1
      continue
    end
    for k = 1:i-1
      h[k,i] = mod(-t[i]*w[k,1], h[i,i])
      w[k,1] = mod(w[k,1]+h[k,i]*w[i,1], d)
    end
    w[i,1] = h[i,i]*w[i,1]
    d = d/h[i,i]
    divexact!(w, w, h[i,i])
  end
  return h
end

@inline function Nemo.mat_entry_ptr(b::fpMatrix, i::Int, j::Int)
  unsafe_load(reinterpret(Ptr{Ptr{Culong}}, b.rows), i) + (j-1)*sizeof(Culong)
end

function induce_crt!(A::ZZMatrix, p::ZZRingElem, B::fpMatrix, ::Integer; signed::Bool = false)
  #the second modulus is implicit in B: B.n

  ccall((:fmpz_mat_CRT_ui, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZRingElem}, Ref{fpMatrix}, Int), A, A, p, B, signed)
  Nemo.mul!(p, p, B.n)
  return
end

function vector_int(a::fpMatrix)
  b = zeros(Int, nrows(a) * ncols(a))
  vector_int!(b, a)
  return b
end

function vector_int!(a::Vector{Int}, b::fpMatrix)
  ccall(:memcpy, Cvoid, (Ref{Int}, Ptr{Clong}, Int), a, b.entries, nrows(b)*ncols(b) * 8)
end

function _map_entries(k::Nemo.fpField, n::Int, m::Int)
  #create a fpMatrix with julias memory manager,
  #create a "view" where the view_parent is a julia-Uint array with the
  #entries
  # => no finaliser
  # => matrix(entries) can be used as a 1-dim julia array
  #    (for broadcast)
  u = zeros(Int, n*m)
  a = Nemo.fpMatrix()
  a.base_ring = k
  a.entries = reinterpret(Ptr{Cvoid}, pointer(u))
  v = zeros(UInt, n)
  for i=1:n
    v[i] = a.entries + (i-1)*m*8
  end
  a.view_parent = (u, v)
  a.rows = reinterpret(Ptr{Cvoid}, pointer(v))
  a.r = n
  a.c = m
  change_prime(a, UInt(characteristic(k)))
  return a
end


function _map_entries(k::Nemo.fpField, A::ZZMatrix)
  #turns A into a fpMatrix with julias memory manager,
  #create a "view" where the view_parent is a julia-Uint array with the
  #entries
  # => no finaliser
  # => matrix(entries) can be used as a 1-dim julia array
  #    (for broadcast)
  a = _map_entries(k, nrows(A), ncols(A))
  map_entries!(a, k, A)
  return a
end

@inline myround(a, p, pi) = @fastmath a-p*Base.rint_llvm(a*pi)

function mod!(A::AbstractArray{Float64}, p::Int)
  return mod!(A, Float64(p), 1.0/Float64(p))
end

function mod!(A::AbstractArray{Float64}, pf::Float64, pfi::Float64)
#  pf = Float64(p)
#  pfi = 1/pf
#  A = reshape(A, nrows(A)*ncols(A))
#  A .= (x->myround(x, pf, pfi)).(A)
#  return
  Ap = pointer(A)
  @fastmath for i= 1:length(A)
    a = Base.Intrinsics.pointerref(Ap, 1, 1)
#    a = unsafe_load(Ap)
    a -= pf*Base.rint_llvm(a*pfi)
#    a -= pf*Base.trunc(a*pfi)
#    if a < 0
#      a += pf
#    end

#     a = Base.modf(a, pf)
    Base.Intrinsics.pointerset(Ap, a, 1, 1)
#    unsafe_store!(Ap, a)
    Ap += sizeof(Float64)
  end
end

mutable struct CrtCtx_Mat
  c::Int #how many primes before tree

  d::Vector{ZZRingElem} #the product tree so far
  M::Vector{ZZMatrix}

  pos::Int
  cc::Int

  function CrtCtx_Mat(c::Int = 1)
    return new(c, ZZRingElem[], ZZMatrix[], 0, 0)
  end
end

function Base.push!(C::CrtCtx_Mat, a::fpMatrix)
  if C.pos == 0
    push!(C.M, lift(a))
    push!(C.d, ZZ(a.n))
    C.cc = 1
    C.pos += 1
    return
  end
  pos = C.pos
  if C.cc == 0
    if pos > length(C.M)
      push!(C.M, lift(a))
      push!(C.d, ZZ(a.n))
    else
      C.M[pos] = lift(a)
      C.d[pos] = ZZ(a.n)
    end
    C.cc = 1
  else
    induce_crt!(C.M[C.pos], C.d[C.pos], a, 1; signed = true)
    C.cc += 1
  end
  if C.cc >= C.c #full...
    while pos > 1 && C.d[pos-1] < C.d[pos] #assuming primes are in order
      g, e, f = gcdx(C.d[pos-1], C.d[pos])
      @assert isone(g)
      mul!(C.M[pos-1], f*C.d[pos])
      mul!(C.M[pos], e*C.d[pos-1])
      add!(C.M[pos-1], C.M[pos-1], C.M[pos])
      C.d[pos-1] *= C.d[pos]
      #@show maximum(nbits, C.M[pos-1])
      mod_sym!(C.M[pos-1], C.d[pos-1])
      pos -= 1
    end
    C.pos = pos + 1
    C.cc = 0
  end
end

function finish(C::CrtCtx_Mat)
  pos = C.pos
  if C.cc == 0
    pos -= 1
  end
  while pos > 1
    g, e, f = gcdx(C.d[pos-1], C.d[pos])
    @assert isone(g)
    mul!(C.M[pos-1], f*C.d[pos])
    mul!(C.M[pos], e*C.d[pos-1])
    add!(C.M[pos-1], C.M[pos-1], C.M[pos])
    C.d[pos-1] *= C.d[pos]
#    @show maximum(nbits, C.M[pos-1]), nbits(C.d[pos-1])
    mod_sym!(C.M[pos-1], C.d[pos-1])
    pos -= 1
  end
  return C.M[1]
end


# Input: B vector of matrices as Double64 meant to be mod q[i]
# Output: RE vector of matrices ...                       p[i]
# fast and useful if number of primes is small
# otherwise: not so much...
# from hnfproj of Storjohann
#
# CRT mod pq: x = a mod p, x = b mod q, 1 = ep+fq
#  x = fqa + epb
#
function change_rns!(RE::Vector{Matrix{Float64}}, p::Vector{Int}, q::Vector{Int}, B::Vector{<:AbstractArray{Float64}}, U::Vector{Matrix{Float64}} = [])
  @show length(q), length(p)
  if length(p) > 40 # also slow, induce_crt! is killing it
          # to try, for 20 bit primes, to do pairwise CRT using BLAS
          # or just not use the UniCert_rns ...
          # actually: if entries are large enough this is winning!q
          # possibly: do an induce_crt_env where one can push data in
#    x = matrix(ZZ, map(x->ZZ(Int(x)), B[1]))
#    P = ZZ(q[1])
    C = CrtCtx_Mat(2)

    y = _map_entries(Native.GF(3, cached = false), size(B[1], 1), size(B[1], 2))
    for i=1:length(B)
      y.view_parent[1] .= map(Base.rint_llvm, reshape(B[i], :))
      change_prime(y, UInt(q[i]))
      push!(C, y)
#      induce_crt!(x::ZZMatrix, P::ZZRingElem, y::fpMatrix, 1; signed = true)
    end
    x = finish(C)
    for i=1:length(p)
      map_entries!(y, Native.GF(p[i], cached = false), x)
      if length(RE) < i
        push!(RE, reshape(map(Float64, y.view_parent[1]), size(B[1])))
      else
        RE[i] .= reshape(map(Float64, y.view_parent[1]), size(B[1]))
      end
    end
    return
  end
  T = Float64
  bd = Int[]  # mixed radix rep (wrt to q) of (prod(q)-1)/2
  pr = mapreduce(ZZ, *, q)
  pr = div(pr, 2)
  for i = q
    push!(bd, pr % i)
    pr = divexact(pr - bd[end], i)
  end

  qinv = Int[0]
  for i=2:length(B)
    push!(qinv, invmod(Int(mapreduce(ZZ, *, q[1:i-1]) % q[i]), q[i]))
  end
  cp = [x-Int(mapreduce(ZZ, *, q) % x) for x = p]

  if length(U) < 1
    push!(U, copy(B[1]))
  else
    U[1] .= B[1]
  end
  @fastmath for i=2:length(B)
    if length(U) < i
      push!(U, copy(U[i-1]))
    else
      U[i] .= U[i-1]
    end
    for j=i-2:-1:1
      BLAS.scal!((q[j] % T(q[i])), U[i])
      BLAS.axpy!(1.0, U[j], U[i])
      mod!(U[i], q[i])
    end
    BLAS.scal!(T((qinv[i]*(q[i]-1)) % q[i]), U[i])
    BLAS.axpy!(T(qinv[i]), B[i], U[i])
    mod!(U[i], q[i])
  end

  for j = 1:length(p)
    if length(RE) < j
      push!(RE, copy(U[length(B)]))
    else
      RE[j] .= U[length(B)]
    end
    mod!(RE[j], p[j])
    @fastmath for i=length(B)-1:-1:1
      BLAS.scal!(T(q[i] % p[j]), RE[j])
      BLAS.axpy!(1.0, U[i], RE[j])
      mod!(RE[j], p[j])
    end
  end

  for i=1:length(RE[1])
    for j=1:length(B)
      if U[j][i] > bd[j]
        for k=1:length(p)
          RE[k][i] = (RE[k][i] + cp[k]) % p[k]
        end
        break
      elseif U[j][i] < bd[j]
        break
      end
    end
  end
  return RE
end

# Storjohann's unimodular certification
# We use CRT to obtain the modular inverse B0
# The p-adic Hensel-lifting version (below) seems to be faster
function UniCertZ_CRT_rns(A::ZZMatrix)
  n = nrows(A);
  #assume ncols == n
  H = hadamard_bound2(A)
  EntrySize = maximum(nbits, A)
  e = max(16, 2+ceil(Int, 2*log2(n)+EntrySize))
  println("Modulus X has  $e bits");

  B0 = Matrix{Float64}[]
  m = ZZ(1); p = 2^21;  # MAGIC NUMBER (initial prime needs to be such that
                        #a full scalar product does not overflow:
                        #n*(p-1)^2 < 2^53 is my guess
  Xp = Int[]
  @time while nbits(m) < e
    p = next_prime(p);
    ZZmodP = Native.GF(p, cached = false);
    MatModP = map_entries(ZZmodP, A)
    B00 = inv_strassen(MatModP)
    push!(Xp, p)
    push!(B0, map(Float64, lift(B00)).entries)
    Nemo.mul!(m, m, p)
  end
  println("Got modular inverses");
  #m is the X

  Ap = Matrix{Float64}[]
  m_inv = fpFieldElem[]
  Y = ZZ(1)
  Yp = Int[]
  while nbits(Y) < Int(1+ceil(log2(n)+EntrySize))
    p = next_prime(p)
    push!(Yp, p)
    k = Native.GF(p, cached = false)
    push!(Ap, map(Float64, lift(map_entries(k, A))).entries)
    push!(m_inv, inv(k(m)))
    Nemo.mul!(Y, Y, p)
  end

  # Compute max num iters in k
  k = (n-1)*(EntrySize+log2(n)/2) - (2*log2(n) + EntrySize);
  k = k/log2(m);
  k = 2+ceil(Int, log2(k));
  println("Max num iters is k=$(k)");

  t = similar(B0[1])
  RY = Matrix{Float64}[]
  U = Matrix{Float64}[]
  change_rns!(RY, Yp, Xp, B0, U)
  for i = 1:length(Ap)
    x = Ap[i]
    t = RY[i]
    t .= -x*t
    mod!(t, Yp[i])
    for j=1:n
      t[j,j] += 1.0
    end
    BLAS.scal!(Float64(lift(m_inv[i])), t)
    mod!(t, Yp[i])
  end

  if all(iszero, RY)
    return true
  end

  RX = map(similar, B0)
  MY = map(similar, Ap)
  R = similar(B0[1])
  M = similar(B0[1])
  T = similar(M)

  MX = Matrix{Float64}[]

  for i in 0:k-1
    println("UniCertZ: loop: i=$(i)");
    @time change_rns!(RX, Xp, Yp, RY, U)
    @time for t = 1:length(RX)
      BLAS.gemm!('n', 'n', 1.0, RX[t], RX[t], 0.0, M)
      mod!(M, Xp[t])
      if length(MX) < t
        push!(MX, B0[t] * M)
      else
        BLAS.gemm!('n', 'n', 1.0, B0[t], M, 0.0, MX[t])
      end
      mod!(MX[t], Xp[t])
    end
    @time change_rns!(MY, Yp, Xp, MX, U)
    @time for k=1:length(Ap)
      S = RY[k]
      M = similar(S)
      BLAS.gemm!('n', 'n', 1.0, S, S, 0.0, M)
#      change_rns2!(M, Yp[k], Xp, MX, U)
#      S .= S*S
      BLAS.gemm!('n', 'n', -1.0, Ap[k], MY[k], 1.0, M)
#      S .-= Ap[k] * M
      mod!(M, Yp[k])
      BLAS.scal!(Float64(lift(m_inv[k])), M)
      mod!(M, Yp[k])
      RY[k], M = M, RY[k]
    end

    if all(iszero, RY)
      return true
    end
  end #for
  return false
end

#naive, vanilla UniSolve, terrible...
function UniSolve(A::ZZMatrix, bb::ZZMatrix)
  n = nrows(A);
  #assume ncols == n
  H = hadamard_bound2(A)
  EntrySize = maximum(abs, A)
  e = max(16, Int(2+ceil(2*log2(n)+log2(EntrySize))));
  println("Modulus has  $e bits");

  B0 = zero_matrix(ZZ,n,n) ## will be computed by crt in loop below
  m = ZZ(1); p = 2^29;  # MAGIC NUMBER (initial prime, probably should be about 2^29?)
  @time while (nbits(m) < e)
    p = next_prime(p);
    ZZmodP = Native.GF(p, cached = false);
    MatModP = map_entries(ZZmodP, A)
    B00 = inv_strassen(MatModP)
    induce_crt!(B0,m, B00,p, signed = true);  #  also updates:  m = m*p;
  end
  println("Got modular inverse");

  # Compute max num iters in k
  k = (n-1)*(log2(EntrySize)+log2(n)/2) - (2*log2(n) + log2(EntrySize));
  k = max(k, 1)
  k = k/log2(m);

  k = max(k, 1)
  k = 2+Int(ceil(log2(k)));
  println("Max num iters is k=$(k)");

  ZZmodM = residue_ring(ZZ,m);
  B0_modm = map_entries(ZZmodM, B0);
  I = identity_matrix(ZZ,n)
  S0 = bb*B0  #sol mod X
  R = (I-A*B0)/m
  X = ZZ(p)
  XX = X
  for i in 0:k+1
    println("UniCertZ: loop: i=$(i)");
    @time R_bar = R^2;
    @time M = lift(B0_modm*map_entries(ZZmodM, R_bar));
    Hecke.mod_sym!(M, m)
    S0 = S0 + S0*R*XX + bb*M*XX^2
    XX = XX^2*X
    fl, r, d = induce_rational_reconstruction(S0, XX)
    if fl && r*A == d*bb
      return r, d
    end
    Hecke.mod_sym!(S0, XX)
    @time R = (R_bar - A*M)/m;
  end #for
  return S0, XX
end

# Storjohann's unimodular certification
# We use CRT to obtain the modular inverse B0
# The p-adic Hensel-lifting version (below) seems to be faster
function UniCertZ_CRT(A::ZZMatrix)
  n = nrows(A);
  #assume ncols == n
  H = hadamard_bound2(A)
  EntrySize = maximum(abs, A)
  e = max(16, Int(2+ceil(2*log2(n)+log2(EntrySize))));
  println("Modulus has  $e bits");

  B0 = zero_matrix(ZZ,n,n) ## will be computed by crt in loop below
  m = ZZ(1); p = 2^29;  # MAGIC NUMBER (initial prime, probably should be about 2^29?)
  @time while (nbits(m) < e)
    p = next_prime(p);
    ZZmodP = Native.GF(p, cached = false);
    MatModP = map_entries(ZZmodP, A)
    B00 = inv(MatModP)
    induce_crt!(B0,m, B00,p, signed = true);  #  also updates:  m = m*p;
  end
  println("Got modular inverse");

  # Compute max num iters in k
  k = (n-1)*(log2(EntrySize)+log2(n)/2) - (2*log2(n) + log2(EntrySize));
  k = k/log2(m);
  k = 2+Int(ceil(log2(k)));
  println("Max num iters is k=$(k)");

  ZZmodM, = residue_ring(ZZ,m);
  B0_modm = map_entries(ZZmodM, B0);
  I = identity_matrix(ZZ,n)
  R = (I-A*B0)/m
  if is_zero(R)
    return true;
  end
  for i in 0:k-1
    println("UniCertZ: loop: i=$(i)");
    @time R_bar = R^2;
    @time M = lift(B0_modm*map_entries(ZZmodM, R_bar));
    Hecke.mod_sym!(M, m)
    @time R = (R_bar - A*M)/m;
    if is_zero(R)
      return true
    end
  end #for
  return false
end

function mod_sym!(a::Ptr{ZZRingElem}, b::Ptr{ZZRingElem}, c::ZZRingElem, t::ZZRingElem = ZZ(0))
  ccall((:fmpz_ndiv_qr, Nemo.libflint), Cvoid, (Ref{ZZRingElem}, Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), t, a, b, c)
end

function renorm(U::ZZMatrix, m::ZZRingElem; start::Int = 1, last::Int = nrows(U))
  i = start
  R = zero_matrix(ZZ, 1, ncols(U))
  t = ZZ(0)
  while true
    R_ptr = Nemo.mat_entry_ptr(R, 1, 1)
    U_ptr = Nemo.mat_entry_ptr(U, i, 1)
    for j=1:ncols(U)
      add!(R_ptr, R_ptr, U_ptr)
      mod_sym!(U_ptr, R_ptr, m, t)
      sub!(R_ptr, R_ptr, U_ptr)
      divexact!(R_ptr, R_ptr, m)
      R_ptr += sizeof(Clong)
      U_ptr += sizeof(Clong)
    end
    i += 1
    if i > nrows(U)
      if i > last || is_zero(R)
        return U
      end
      while !is_zero(R)
        U.r += 1
        if i > last
          return U
        end
        @assert U.r <= last
        U_ptr = Nemo.mat_entry_ptr(U, i, 1)
        R_ptr = Nemo.mat_entry_ptr(R, 1, 1)
        for j=1:ncols(U)
          Hecke.set!(U_ptr, R_ptr)
          mod_sym!(U_ptr, R_ptr, m, t)
          sub!(R_ptr, R_ptr, U_ptr)
          divexact!(R_ptr, R_ptr, m)
          R_ptr += sizeof(Clong)
          U_ptr += sizeof(Clong)
          i += 1
        end
      end
      return U
    end
  end
end

function add_into!(A::ZZMatrix, C::ZZMatrix, c::Int)
  @show A.r = max(A.r, C.r+c)
  for i=1:nrows(C)
    A_ptr = Nemo.mat_entry_ptr(A, i+c, 1)
    C_ptr = Nemo.mat_entry_ptr(C, i, 1)
    for j=1:ncols(A)
      add!(A_ptr, C_ptr)
      A_ptr += sizeof(Clong)
      C_ptr += sizeof(Clong)
    end
  end
end

# "solves" xA = U using the double + 1 method
# pr_max is the bit size (num + den) of the solution
# the functions returns
# - a matrix X
# - an integer m
# the rows of X are the base-m expansion of the solution
# use e.g. to_base(X, m) to destructively get the solution
# followed by induce_rational_reconstruction(xx, m^(nrows(X)-1))
#
function UniCertZ_CRT(A::ZZMatrix, U::ZZMatrix; pr_max::Int = 10^8)
  n = nrows(A);
  #assume ncols == n
  H = hadamard_bound2(A)
  EntrySize = maximum(abs, A)
  e = max(16, Int(2+ceil(2*log2(n)+log2(EntrySize))));
  println("Modulus has  $e bits");

  B0 = zero_matrix(ZZ,n,n) ## will be computed by crt in loop below
  m = ZZ(1); p = 2^29;  # MAGIC NUMBER (initial prime, probably should be about 2^29?)
  @time while (nbits(m) < e)
    p = next_prime(p);
    ZZmodP = Native.GF(p, cached = false);
    MatModP = map_entries(ZZmodP, A)
    B00 = inv(MatModP)
    induce_crt!(B0,m, B00,p, signed = true);  #  also updates:  m = m*p;
  end
  println("Got modular inverse");

  # Compute max num iters in k
  k = (n-1)*(log2(EntrySize)+log2(n)/2) - (2*log2(n) + log2(EntrySize));
  k = max(1, k/log2(m));
  k = 2+Int(ceil(log2(k)));
  println("Max num iters is k=$(k)");

  ZZmodM, = residue_ring(ZZ,m);
  B0_modm = map_entries(ZZmodM, B0);

  @show size(U)
  @assert nrows(U) == 1
  @show pr = 2^(k+2)-1  
  V = zero_matrix(ZZ, pr+100, ncols(U))
  V[1, :] = U
  U = V
  U.r = 1
#  @assert maximum(abs, U) <= m

  I = identity_matrix(ZZ,n)
  R = (I-A*B0)/m
  V = zero_matrix(ZZ, pr + 100, ncols(U))
  V[1, :] = U*B0 #sol mod m
  @show V.r = 1
  renorm(V, m; last = 10)
  l = nrows(V)
  add_into!(V, V*R, 1) #sol mod m^2
  renorm(V, m; last = 10)
  @show V

  if is_zero(R)
    return true;
  end
  ex = 1
  for i in 0:k-1
    println("UniCertZ: loop: i=$(i)");
    @time R_bar = R^2;
    @time M = lift(B0_modm*map_entries(ZZmodM, R_bar));
    Hecke.mod_sym!(M, m)
    @time R = (R_bar - A*M)/m;

    @assert nrows(U) == 1

    add_into!(V, U*M, 2*ex)  #sol mod 2ex+1
    renorm(V, m, start = 2*ex, last = pr)
    @show 2*ex+1


    ex = 2*ex + 1

    if nrows(V) > nrows(R)
      n = nrows(R)
      l = nrows(V)
      e = div(l, n)
      add_into!(V, V[e*n+1:end, :]*R, ex+e*n)
      for j=e:-1:1
        @assert j*n <= pr
        add_into!(V, V[(j-1)*n+1:j*n, :]*R, ex+(j-1)*n)
#        renorm(V, m, start = ex+(j-1)*n-1, last = pr)
        if nrows(V)*nbits(m) >= pr_max
          @show "abort at j", j, e, nrows(V), nrows(V)*nbits(m), pr_max
          return V, m
        end
      end
#      renorm(V, m, start = ex+e*n-1, last = pr)
    else
      add_into!(V, V*R, ex) #sol mod 2(2ex+1)
    end
    renorm(V, m, start = ex-1, last = pr)


    @show 2*ex
    if 2*ex*nbits(m) >= pr_max
      @show "done"
      return V, m
    end

    if is_zero(R)
      return V, m
    end
  end #for
  return V, m
end

#inplace conversion
#the rows of a are encoding a base-b row vector
#this computes asymptotically fast(?) the ZZ-version
function to_base(a::ZZMatrix, b::ZZRingElem, nr::Int = nrows(a))
  while nr > 1
    for i=1:div(nr, 2)
      add_row!(a, b, 2*i-1, 2*i)
      swap_rows!(a, i, 2*i-1)
    end
    if is_odd(nr)
      add_row!(a, b^2, div(nr, 2), nr)
    end
    nr = div(nr, 2)
    b *= b
  end
  return a[1:1, :]
end

function in_base(a::ZZRingElem, b::ZZRingElem)
  di = ZZRingElem[]
  while !iszero(a)
    push!(di, mod_sym(a, b))
    a = divexact(a-di[end], b)
  end
  return di
end

function _det(a::fpMatrix)
  a.r < 10 && return ZZ(lift(det(a)))
  #_det avoids a copy: det is computed destructively
  r = ccall((:_nmod_mat_det, Nemo.libflint), UInt, (Ref{fpMatrix}, ), a)
  return ZZ(r)
end

function t_det(h::ZZMatrix)
  return Hecke.prod_diagonal(h)
end

# Determinant algorithm: U is the range for random RHS matrix (default -100:100)
# Answer is !!! CORRECT UP TO SIGN !!!
# should be trivial to fix as we compute some det mod odd p already
function DetS(A::ZZMatrix, U::AbstractArray= -100:100; use_rns::Bool = false, do_hnf::Bool = false)
  n = ncols(A)
  T = ZZMatrix[]
  AT = A
  d1 = ZZ(1) # will be the det

  p = UInt(next_prime(2^60))
  det_p = ZZ(0)
  prod_p = ZZ(1)
  Ainf = maximum(nbits, A)
  Had = div(nbits(hadamard_bound2(A)), 2)+1

  #Dixon cost
  # lifting has (at least) Had/60 many steps (as the numerator will be
  # of maximal size)
  # Each step uses (Ainf+60+n)/60 many modular products
  #                +1 for lifting
  #so that should be the number of quadratic steps
  #
  function dixon_cost(::ZZRingElem)
    ceil(Int, (((Ainf+60+n)/60 + 1) * Had/60)/n)
  end
  #this should estimate the number of modular dets that will cost
  #as much as the next dixon step.
  #if we are close enough to Had, we move to crt.
  function crt_cost(d::ZZRingElem)
    return ceil(Int, (Had-nbits(d))/60)
  end
  function hnf_cost(d::ZZRingElem)
    ceil(Int, nbits(d)/60)
  end
  function uni_cost(d::ZZRingElem)
    ceil(Int, log(n)*(2*n+Ainf)/60)
  end

  f = true
  local Ap::fpMatrix
  small = Ainf+n
  @time while nbits(prod_p) < small + 20
    if f
      f = false
      Ap = map_entries(Nemo.fpField(p, false), A)
    else
      change_prime(Ap, p)
      map_entries!(Ap, Nemo.fpField(p, false), A)
    end
    d = _det(Ap)
    if det_p == 0
      det_p = d
    else
      det_p = crt(det_p, prod_p, d, ZZ(p))
    end
    Nemo.mul!(prod_p, prod_p, p)
    p = next_prime(p)
  end
  det_p = mod_sym(det_p, prod_p)
  det_small = false
  if nbits(prod_p) - nbits(det_p) > 30
    @show "det small", det_p
    det_small = true
  end

  if do_hnf
    _hnf = identity_matrix(ZZ, n)
  end
  local D::DixonCtx
  f = true
  while !det_small
    b = rand(matrix_space(ZZ,n,1),U);
    if f
      @show :solve_init
      D = dixon_init(A, b)
      f = false
    end
    @show :solving
    @time TS, d = dixon_solve(D, b)
#    @assert A*TS == d*b
    for i=1:length(T)
      TS = T[i]*TS
    end
    c = content(TS)
    g = gcd(c, d)
    divexact!(TS, TS, g)
    d = divexact(d, g)
    println("DetS: loop: nbits(d)=$(nbits(d))");

    @assert !isone(d)  #should never happen, the det_p should catch that
    isone(d) && break
    d1 *= d
    @show  (Had - nbits(d1) - nbits(prod_p))/60
    @show mod_sym(d1, prod_p) , det_p
    if Had - nbits(d1) < nbits(prod_p)
      @show "at H-bound",  (Had - nbits(d1) - nbits(prod_p))/60
      if do_hnf
        @show d
        T1 = hcol(TS, d)
        return T1 * _hnf 
      end
      return d1
    end
    if (Had - nbits(d1) - nbits(prod_p))/60 < dixon_cost(d)
      @show "finishing with CRT"
      if do_hnf 
        T1 = hcol(TS, d)
        AT = AbstractAlgebra.Strassen._solve_triu(T1, AT; side = :left)
        _hnf = T1 * _hnf 
      end
      while nbits(prod_p)+nbits(d1) < Had
        change_prime(Ap, p)
        map_entries!(Ap, Nemo.fpField(p, false), A)
        d = _det(Ap)
        det_p = crt(det_p, prod_p, d, ZZ(p))
        Nemo.mul!(prod_p, prod_p, ZZ(p))
      end
      mis = mod_sym(det_p*invmod(d1, prod_p), prod_p)
      if do_hnf
        h = hnf_modular_eldiv(AT, mis)
        return h * _hnf 
      end
      return d1*mis
    end
    @time T1 = hcol(TS, d)
    push!(T, T1)
    @show :solve
    @time _AT = AbstractAlgebra.Strassen._solve_triu(T1, AT; side = :left)
#    @assert _AT*T1 == AT
    if do_hnf
      _hnf = T1 * _hnf
    end
    @show maximum(nbits, _AT), maximum(nbits, T1), maximum(nbits, AT)
    AT = _AT
#    @show nbits(prod_p), nbits(d1)
#    @show nbits(abs(mod_sym(invmod(d1, prod_p)*det_p, prod_p)))
    if nbits(abs(mod_sym(invmod(d1, prod_p)*det_p, prod_p))) < small
      break
    end
#    @show nbits(d), Ainf
    if nbits(d) < Ainf + n
      @show :doin_hnf
      h = hnf_modular_eldiv(AT, d)
      d1 *= prod([h[i,i] for i=1:n])
    @show Had / nbits(d1)
      AT = AbstractAlgebra.Strassen._solve_triu(h, AT; side = :left)
      if do_hnf
        _hnf = h * _hnf
      end
      if nbits(abs(mod_sym(invmod(d1, prod_p)*det_p, prod_p))) < small
        break
      end
    end
  end
  det_p = invmod(d1, prod_p)*det_p
  @show det_p = mod_sym(det_p, prod_p)
  @show small
  @assert !is_zero(det_p)
#  @assert nbits(abs(det_p)) < small
  @show :hnf
  @time h = hnf_modular_eldiv(AT, det_p)
  @show t_det(h) // det_p, det(h)
  d1 *= t_det(h)

  @time AT = AbstractAlgebra.Strassen._solve_triu(h, AT; side = :left)
    if do_hnf
      _hnf = h*_hnf
    end
    println("DOING UNICERTZ");
    @show uni_cost(d1)
    @show crt_cost(d1)
    #need to cost this as well

    if use_rns
      @time fl = UniCertZ_CRT_rns(AT)
    else
      @time fl = UniCertZ_CRT(AT)
    end
    #           @assert fl == is_unit(det(ZAT));
    if fl
      if do_hnf
        return _hnf
      end
      return d1
    end
    error("unimod failed")
    return d1
end

#adaptive rational_reconstruction: if solution is unbalanced with
#denominator smaller than numerator
function induce_rational_reconstruction(a::ZZMatrix, b::ZZRingElem)
  A = similar(a)
  D = ZZ(1)
  T = ZZ()
  n = ZZ()
  d = ZZ()
  for i=1:nrows(a)
    a_ptr = Nemo.mat_entry_ptr(a, i, 1)
    A_ptr = Nemo.mat_entry_ptr(A, i, 1)
    for j=1:ncols(a)
#      @show i, j
      Nemo.set!(T, a_ptr)
      Nemo.mul!(T, T, D)
      Nemo.mod!(T, T, b)
      fl = ratrec!(n, d, T, b)
      fl || return fl, A, D
      if !isone(d)
        D = D*d
        Nemo.mul!(A, A, d)
      end
      Nemo.set!(A_ptr, n)

      a_ptr += sizeof(ZZRingElem)
      A_ptr += sizeof(ZZRingElem)
    end
  end
  return true, A, D
end

function Nemo.div!(a::ZZRingElem, b::ZZRingElem, c::ZZRingElem)
  ccall((:fmpz_tdiv_q, Nemo.libflint), Cvoid, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), a, b, c)
end

function shift_right!(a::ZZRingElem, b::ZZRingElem, i::Int)
  ccall((:fmpz_fdiv_q_2exp, Nemo.libflint), Cvoid, (Ref{ZZRingElem}, Ref{ZZRingElem}, Int), a, b, i)
end

#output sensitive rational_reconstruction, in particular if
#numerator is larger than den as in the induced case above
function ratrec!(n::ZZRingElem, d::ZZRingElem, a::ZZRingElem, b::ZZRingElem)
  k = nbits(b)
  l = 1
  N = deepcopy(b)
  D = ZZ(2)

#  @assert 0<a<b
  done = false
  while !done && D <= N
    Nemo.mul!(D, D, D)
    div!(N, b, D)
    shift_right!(N, N, 1)
    if D>N
      D = N = iroot(b, 2)
      D = div(D, 2)
      done = true
    end

#    @assert 2*N*D < b

    fl = ccall((:_fmpq_reconstruct_fmpz_2, Nemo.libflint), Bool, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), n, d, a, b, N, D)

    if fl && (nbits(n)+nbits(d) < k - 30 || D>N)
      return fl
    end
    l += 1
  end
  return false
end

function Hecke.map_entries(k::Nemo.fpField, A::ZZMatrix)
  a = zero_matrix(k, nrows(A), ncols(A))
  return map_entries!(a, k, A)
end

function map_entries!(a::fpMatrix, k::Nemo.fpField, A::ZZMatrix)
  ccall((:fmpz_mat_get_nmod_mat, Nemo.libflint), Cvoid, (Ref{fpMatrix}, Ref{ZZMatrix}), a, A)
  return a
end

function change_prime(a::fpMatrix, p::UInt)
  a.n = p  #in flint 3.0 available as nmod_mat_set_mod
  a.norm = leading_zeros(p)
  a.ninv = ccall((:n_preinvert_limb_prenorm, Nemo.libflint), UInt, (UInt, ), p << a.norm)
end

function lift!(A::ZZMatrix, a::fpMatrix)
  ccall((:fmpz_mat_set_nmod_mat, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, Ref{fpMatrix}), A, a)
end

mutable struct DixonCtx{T}
  bound::ZZRingElem
  Ainv::T
  p::UInt
  crt_primes::Vector{UInt}
  A_mod::Vector{T}
  d_mod::T
  y_mod::T
  Ay_mod::T
  Ay::ZZMatrix
  x::ZZMatrix
  d::ZZMatrix
  A::ZZMatrix
  function DixonCtx(T::DataType)
    return new{T}()
  end
end
#copied from flint to allow the use of adaptive reconstruction,
#support cases with small primes and Float64
function dixon_init(A::ZZMatrix, B::ZZMatrix, T::DataType = fpMatrix)
  #solves, in the end, Ax = B
  #NOT xA = B
  @assert nrows(B) == ncols(A)
  D = DixonCtx(T)
  D.A = A

  n = nrows(A)
  cols = ncols(B)

  _N = ZZ()
  _D = ZZ()
  ccall((:fmpz_mat_solve_bound, Nemo.libflint), Cvoid, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZMatrix}, Ref{ZZMatrix}), _N, _D, A, B)
  local Ainv_t
  if T == fpMatrix
    p = next_prime(2^59)
  else
    p = next_prime(2^20)
  end
  while true
    Ainv_t = map_entries(Native.GF(p, cached = false), A)
    try
      Ainv_t = inv(Ainv_t)
      break
    catch e
      if e != ErrorException || e.msg != "Matrix not invertible"
        rethrow(e)
      end
    end
    p = next_prime(p)
  end
  if T == fpMatrix
    Ainv = Ainv_t
  else
    Ainv = map_entries(Float64, lift(Ainv_t)).entries
  end
  @assert p != 0
  D.p = p
  D.Ainv = Ainv

  D.bound = 2*maximum(abs, [_D, _N])^2 * 2^30
  D.crt_primes = UInt[]
  D.A_mod = T[]

  pr = ZZ(1)
  xp = next_prime(p)
  maxA = maximum(abs, A) *(p-1)*n*2

  while true
    push!(D.crt_primes, xp)
    if T == fpMatrix
      push!(D.A_mod, map_entries(Nemo.fpField(UInt(xp), false), A))
    else
      push!(D.A_mod, map_entries(Float64, lift(map_entries(Nemo.fpField(UInt(xp), false), A))).entries)
    end
    pr *= xp
    if pr > maxA
      break
    end
    xp = next_prime(xp)
  end

  k = Nemo.fpField(UInt(p), false)
  if T == fpMatrix
    D.d_mod = zero_matrix(k, nrows(B), ncols(B))
    D.y_mod = zero_matrix(k, nrows(B), ncols(B))
    D.Ay_mod = zero_matrix(k, nrows(B), ncols(B))
  else
    D.d_mod = zeros(Float64, nrows(B), ncols(B))
    D.y_mod = zeros(Float64, nrows(B), ncols(B))
    D.Ay_mod = zeros(Float64, nrows(B), ncols(B))
  end
  D.Ay = zero_matrix(ZZ, nrows(B), ncols(B))
  D.x = zero_matrix(ZZ, nrows(B), ncols(B))

  return D
end

function map_entries!(A::Matrix{Float64}, k::Nemo.fpField, d::ZZMatrix)
  @assert size(A) == size(d)
  p = characteristic(k)
  t = ZZ()
  for i=1:nrows(d)
    d_ptr = Nemo.mat_entry_ptr(d, i, 1)
    for j=1:ncols(d)
      A[i,j] = ccall((:fmpz_mod_ui, Nemo.libflint), UInt, (Ref{ZZRingElem}, Ptr{ZZRingElem}, Int), t, d_ptr, p)
      d_ptr += 8
    end
  end
end

function dixon_solve(D::DixonCtx{T}, B::ZZMatrix; block::Int = 10) where T
  @assert ncols(D.A) == nrows(B)
  #we're solveing Ax=B
  zero!(D.x)
  d = deepcopy(B)
  ppow = ZZ(1)
  i = 1
  nexti = 1
  while ppow <= D.bound
    map_entries!(D.d_mod, Nemo.fpField(D.p, false), d)

    if T == fpMatrix
      Nemo.mul!(D.y_mod, D.Ainv, D.d_mod)
      ccall((:fmpz_mat_scalar_addmul_nmod_mat_fmpz, Nemo.libflint), Cvoid, (Ref{ZZMatrix}, Ref{fpMatrix}, Ref{ZZRingElem}), D.x, D.y_mod, ppow)
    else
      BLAS.gemm!('N', 'N', 1.0, D.Ainv, D.d_mod, 0.0, D.y_mod)
      mod!(D.y_mod, Int(D.p))
      for i=1:nrows(D.x)
        x_ptr = Nemo.mat_entry_ptr(D.x, i, 1)
        for j=1:ncols(D.x)
          addmul!(x_ptr, ppow, Int(D.y_mod[i, j]))
          x_ptr += 8
        end
      end
    end

    Nemo.mul!(ppow, ppow, D.p)
    if ppow > D.bound
      break
    end

    stabilised = i == nexti;

    if stabilised
      nexti = ceil(Int,(i*1.4)) + 1;
      #maybe col by col? to stop doing cols that are already there?
      #main use currently is 1 col anyway
      fl, num, den = induce_rational_reconstruction(D.x, ppow)

      if fl
        # fl = (D.A*num == den*B)
        sz = max(maximum(nbits, D.A) + maximum(nbits, num)
                                     + nbits(ncols(B)) + 1,
                 maximum(nbits, B) + nbits(den))
        if sz < nbits(ppow)
#          @show "no prod neccessary"
        else
          xp = next_prime(D.p)
#          @show ceil(Int, (sz - nbits(ppow))/60)
          for i=1:ceil(Int, (sz - nbits(ppow))/60)
            k = Nemo.fpField(xp, false)
            Ap = map_entries(k, D.A)
            Bp = map_entries(k, B)
            nump = map_entries(k, num)
            fl = Ap*nump == Bp*k(den)
            fl || break
            xp = next_prime(xp)
          end
        end
#        @show fl
        fl && return num, den
      end
    end

    i += 1

    prod = ZZ(1)
    if false
       n = nrows(D.A)
       for i=1:n
         Ay_ptr = Nemo.mat_entry_ptr(D.Ay, i, 1)
         A_ptr = Nemo.mat_entry_ptr(D.A, i, 1)
         ccall((:fmpz_zero, Nemo.libflint), Cvoid, (Ptr{ZZRingElem},), Ay_ptr)
         for j=1:n
           y_ptr = Nemo.mat_entry_ptr(D.y_mod, j, 1)
           addmul!(Ay_ptr, A_ptr, unsafe_load(y_ptr))
           A_ptr += sizeof(ZZRingElem)
         end
       end
#       @assert is_zero(map_entries(base_ring(D.y_mod), D.Ay - D.A * lift(D.y_mod)))
#      Nemo.mul!(D.Ay, D.A, lift(D.y_mod))
    else
      C = CrtCtx_Mat(block)
      local mu
      if T == fpMatrix
      else
        mu = _map_entries(Native.GF(3), nrows(D.y_mod), ncols(D.y_mod))
      end
      for j=1:length(D.crt_primes)
        change_prime(D.y_mod, D.crt_primes[j])
        change_prime(D.Ay_mod, D.crt_primes[j])

        if T == fpMatrix
          Nemo.mul!(D.Ay_mod, D.A_mod[j], D.y_mod)
          push!(C, D.Ay_mod)
        else
          BLAS.gemm!('N', 'N', 1.0, D.A_mod[j], D.y_mod, 0.0, D.Ay_mod)
          mod!(D.Ay_mod, Int(D.crt_primes[j]))
          change_prime(mu, D.crt_primes[j])
          mu.view_parent[1] .=  D.Ay_mod
          push!(C, mu)
        end
#        if j == 1
#          lift!(D.Ay, D.Ay_mod)
#          prod = ZZ(D.crt_primes[j])
#        else
#          induce_crt!(D.Ay, prod, D.Ay_mod, D.crt_primes[j], signed = true)
#        end
      end
      change_prime(D.y_mod, D.p)
      finish(C)
    end
#    sub!(d, d, D.Ay)
    Nemo.sub!(d, d, C.M[1])
    divexact!(d, d, ZZ(D.p))
  end
  fl, num, den = induce_rational_reconstruction(D.x, ppow)

  @assert fl
#  @time @assert D.A*num == den*B
  return num, den
end

end # module

#= test:
for i = 1:20
   n = 100*i
   for di = 1:10:101
     N = matrix(ZZ, rand(-ZZ(10)^di:ZZ(10)^di, n, n))
     V = matrix(ZZ, rand(-ZZ(10)^di:ZZ(10)^di, n, 1))
     rt = time_ns()
     d = Det.dixon_init(N, V)
     s = Det.dixon_solve(d, V)
     st = time_ns()
     x = Det.UniCertZ_CRT(transpose(N), transpose(V), pr_max = 2*nbits(s[2]))
     f = open("/tmp/res", "a")
     println(f, "$i: n=$n : $di : $((st-rt)*1e-9) : $((time_ns() -st)*1e-9)")
     close(f)
     z = (time_ns() -st)*1e-9
     if z > 500
       break
     end
     @time Base.GC.gc()
   end
end
=#

