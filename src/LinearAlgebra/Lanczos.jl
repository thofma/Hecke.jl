function lanczos{T}(A::Smat{T}, At::Smat{T}, b::MatElem{T})
  w = [ b ]
  i = 0
  #At = transpose(A)
  function c(w, i, j)
    a = (transpose(w[j+1])*(At*(A*(At*(A*w[i - 1 + 1])))))[1,1]
    d = (transpose(w[j+1])*(At*(A*w[j+1])))[1,1]
    return divexact(a,d)
  end
  while !iszero(w[i+1])
    i = i + 1
    wi = At*(A*w[(i-1)+1]) - c(w,i,i-1)*w[i-1+1] - ( i >= 2 ? c(w, i, i-2)*w[i-2+1] : 0*w[1])
    push!(w, wi)
  end
  
  R = 0 * w[1]
  for j in 0:i-1
    R = R + divexact((transpose(w[j+1])*b)[1,1],(transpose(w[j+1])*(At*(A*w[j+1])))[1,1]) * w[j+1]
  end
  return R
end

#intrinsic ModularLancos(A, b) -> .
#  {}
#
#  p := NextPrime(2^20);
#  last_x := false;
#  prod_x := 1;
#  repeat
#    p := NextPrime(p);
#    k := GF(p);
#    xp := Lancos(Matrix(k, A), Matrix(k, b));
#    if last_x cmpne false then
#      pi := Modinv(p, prod_x);
#      pr := Modinv(prod_x, p);
#      xp := Matrix(Integers(), xp);
#      last_x := pi*p*last_x + xp*pr*prod_x;
#      prod_x *:= p;
#    else
#      prod_x := p;
#      last_x := Matrix(Integers(), xp);
#    end if;
#    p, prod_x;
#    Zm := Integers(prod_x);
#    X := Eltseq(Matrix(Zm, last_x));
#    sol := [];
#    for x in X do
#      fl, y := RationalReconstruction(x);
#      if fl then
#        Append(~sol, y);
#      else
#        break;
#      end if;
#    end for;
#    if #sol eq #X and A*Matrix(Rationals(), #sol, 1, sol) eq b then
#      return sol;
#    end if;
#  until false;
#end intrinsic;

################################################################################
#
# NmodSmat
#
################################################################################

type NmodSmat
  r::Int
  c::Int
  rows::Array{SmatRow{Int}, 1}
  nnz::Int
  modulus::Int

  function NmodSmat()
    r = new()
    r.rows = Array(SmatRow{Int}, 0)
    r.nnz = 0
    r.r = 0
    r.c = 0
    return r
  end
end

function NmodSmat(A::Smat{BigInt}, modulus::Int)
  m = NmodSmat()
  m.modulus = modulus
  m.c = cols(A)
  m.r = rows(A)
  m.nnz = 0
  r = Array(SmatRow{Int}, rows(A))
  for i in 1:length(A.rows)
    c =Entry{Int}[]
    for j in 1:length(A.rows[i].entry)
      # this can be done faster I guess
      x = Int(mod(A.rows[i].entry[j].val, modulus))
      if x < 0 
        x = x + modulus
      end
      if x == 0 
        continue
      end
      y = A.rows[i].entry[j].col
      m.nnz = m.nnz + 1
      push!(c, Entry{Int}(y,x))
    end
    r[i] = SmatRow{Int}()
    r[i].entry = c
  end
  m.rows = r
  return m
end

# FIX THIS

#function NmodSmat(A::fmpz_mat, mod::Int)
#  m = NmodSmat()
#  m.modulus = mod
#  m.c = cols(A)
#  m.r = 0
#  for i=1:rows(A)
#    if is_zero_row(A, i)
#      continue
#    end
#    r = SmatRow{BigInt}()
#    for j =1:cols(A)
#      if A[i,j] != 0
#        m.nnz += 1
#        push!(r.entry, Entry{BigInt}(j, A[i,j]))
#      end
#    end
#    push!(m.rows, r)
#    m.r += 1
#  end
#  return m
#end

#function Smat{T}(A::Array{T, 2})
#  m = Smat{T}()
#  m.c = Base.size(A, 2)
#  m.r = 0
#  for i=1:Base.size(A, 1)
#    if is_zero_row(A, i)
#      continue
#    end
#    r = SmatRow{T}()
#    for j =1:Base.size(A, 2)
#      if A[i,j] != 0
#        m.nnz += 1
#        push!(r.entry, Entry{T}(j, A[i,j]))
#      end
#    end
#    push!(m.rows, r)
#    m.r += 1
#  end
#  return m
#end

function show(io::IO, A::NmodSmat)
  println(io, "Sparse ", A.r, " x ", A.c, " matrix with ", A.nnz, " non-zero entries and modulus $(A.modulus)")
end

function getindex(A::NmodSmat, i::Int, j::Int)
  if i in 1:A.r
    for h in A.rows[i].entry
      if h.col == j
        return h.val
      end
    end
  end
  return 0
end

function transpose(A::NmodSmat)
  B = NmodSmat()
  B.modulus = A.modulus
  B.r = A.c
  B.c = A.r
  B.nnz = 0 
  t = Float64(0)
  for j in 1:cols(A)
    C = SmatRow{Int}()
    C.entry = Array(Entry{Int}, rows(A))
    const l = 0
    for i in 1:rows(A)
      g(x) = x.col == j
      t += @elapsed k = findfirst(g, A.rows[i].entry)
      #println("$j $i $k $(A.rows[i].entry[k])")
      if k != 0 
        l = l + 1
        C.entry[l] =  Entry{Int}(i, A.rows[i].entry[k].val)
        B.nnz = B.nnz + 1
      end
    end
    resize!(C.entry, l)
    push!(B.rows, C)
  end
  println("time for findfirst: $t")
  return B
end

# Sparse matrix times dense vector -> dense vector

function _raw_getindex(A::nmod_mat, i::Int, j::Int)
  return ccall((:nmod_mat_get_entry, :libflint), Int, (Ptr{nmod_mat}, Int, Int), &A, i - 1, j - 1)::Int
end

rows(A::NmodSmat) = A.r

cols(A::NmodSmat) = A.c

function _add!(C::nmod_mat, A::nmod_mat, B::nmod_mat)
  ccall((:nmod_mat_add, :libflint), Void, (Ptr{nmod_mat}, Ptr{nmod_mat}, Ptr{nmod_mat}), &C, &A, &B)
end

function _sub!(C::nmod_mat, A::nmod_mat, B::nmod_mat)
  ccall((:nmod_mat_sub, :libflint), Void, (Ptr{nmod_mat}, Ptr{nmod_mat}, Ptr{nmod_mat}), &C, &A, &B)
end


function _mul!(C::nmod_mat, A::Int, B::nmod_mat)
  ccall((:nmod_mat_scalar_mul, :libflint), Void, (Ptr{nmod_mat}, Ptr{nmod_mat}, UInt), &C, &B, UInt(A))
end
  

function *(A::NmodSmat, B::nmod_mat)
  C = MatrixSpace(ResidueRing(ZZ, A.modulus), A.r, 1)()
  mul!(C, A, B)
  return C
end
  
const numm =  [ Int(0) ] 

function mul!(C::nmod_mat, A::NmodSmat, B::nmod_mat)
  global numm
  numm[1] = numm[1] + 1
  for i in 1:rows(A)
    c = 0
    for k in 1:length(A.rows[i].entry)
      c = c +A.rows[i].entry[k].val * _raw_getindex(B, A.rows[i].entry[k].col, 1)
    end
    d = ccall((:n_mod2_preinv, :libflint), UInt, (Int, Int, UInt), c, A.modulus, B._ninv) # c = mod(c, A.modulus)
    ccall((:nmod_mat_set_entry, :libflint), Void, (Ptr{nmod_mat}, Int, Int, UInt), &C, i - 1, 0, d)
    #Nemo.set_entry!(C, i, 1, reinterpret(c))
  end
end

  function _s(w::nmod_mat, v::nmod_mat)
    ##println("calling s with w v")
    Cc = 0
    for l in 1:rows(w)
      Cc = Cc + _raw_getindex(w, l, 1) * _raw_getindex(v, l, 1)
    end
    return ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc, w._n, w._ninv)::Int
  end


function lanczos(A::NmodSmat, At::NmodSmat, b::nmod_mat)
  global numm
  m = A.modulus::Int
  
  w = [ b ]::Array{nmod_mat, 1}
  i = 0
  #At = transpose(A)
  # This is dangerous! Overflow could occur depending on the modulus
  precomp = Dict{Int, nmod_mat}() # cache At*A*At*A*w[i]
  precomp2 = Dict{Int, nmod_mat}() # cache At*A*w[i]

  scalar = Dict{Tuple{Int, Int}, Int}() # cache w[i]*At*A*w[j]
  scalar2 = Dict{Tuple{Int, Int}, Int}() # cache w[i]*At*A*At*A*w[j]


  const vc = NmodMatSpace(ResidueRing(FlintZZ, m), A.c, 1)()::nmod_mat
  const vr = MatrixSpace(ResidueRing(FlintZZ, m), A.r, 1)()::nmod_mat

  const vc2 = MatrixSpace(ResidueRing(FlintZZ, m), A.c, 1)()::nmod_mat
  const vc3 = MatrixSpace(ResidueRing(FlintZZ, m), A.c, 1)()::nmod_mat
  const vc4 = MatrixSpace(ResidueRing(FlintZZ, m), A.c, 1)()::nmod_mat
  const vr2 = MatrixSpace(ResidueRing(FlintZZ, m), A.r, 1)()::nmod_mat


  function c(w::Array{nmod_mat, 1}, i::Int, j::Int)
    if haskey(scalar2, (j+1,i))
      a = scalar2[(j+1,i)]
    else
      #println("calling c with w and $i $j")
      if haskey(precomp, i)
        vc = precomp[i]::nmod_mat
      else
        if haskey(precomp2, i)
          mul!(vr, A, precomp2[i])
          mul!(vc, At, vr)
          precomp[i] = deepcopy(vc)
        else
          mul!(vr, A, w[i - 1 + 1])
          mul!(vc, At, vr)
          precomp2[i] = deepcopy(vc)
          mul!(vr, A, vc)
          mul!(vc, At, vr)
          precomp[i] = deepcopy(vc)
        end
      end
      a = _s(w[j+1], vc)
      scalar2[(j+1,i)] = a
    end
    #mul!(vc, At, vr)

    #a = (transpose(w[j+1])*(At*(A*(At*(A*w[i - 1 + 1])))))[1,1]
    if haskey(scalar, (j+1, j+1))
      d = scalar[(j+1, j+1)]
    else
      if haskey(precomp2, j+1)
        d = _s(w[j+1], precomp2[ j+1])
      else
        mul!(vr, A, w[j+1])
        mul!(vc, At, vr)
        precomp2[ j+1] = deepcopy(vc)
        d = _s(w[j+1], vc)
      end
        scalar[(j+1, j+1)] = d
    end


    #d = (transpose(w[j+1])*(At*(A*w[j+1])))[1,1]
    tee = [ Int(0) ]
    g = ccall((:n_gcdinv, :libflint), Int, (Ptr{Int}, Int, Int), tee, d, m)
    if g != 1
      error("Noninvertible denominator")
    end
    return ccall((:n_mulmod2_preinv, :libflint), Int, (Int, Int, Int, UInt), a, tee[1], m, b._ninv)

#    return mod(a*Int(ccall((:n_invmod, :libflint), UInt, (UInt, UInt), d, m)),m)
  end

  TTT = Float64(0)
  TTTT = Float64(0)


  while !iszero(w[i+1])
    i = i + 1
    TTTT = @elapsed begin
    if haskey(precomp2, i)
      vc2 = precomp2[i]::nmod_mat
    else
      mul!(vr2, A, w[i - 1 + 1])
      mul!(vc2, At, vr2)
      precomp2[i] = deepcopy(vc2)
    end

    _mul!(vc, c(w,i,i-1), w[i])
    _sub!(vc3, vc2, vc)
    
   if i == 1 
     wi = deepcopy(vc3)
    else
      _mul!(vc4, c(w,i,i-2), w[i-2+1])
      _sub!(vc2, vc3, vc4)
      wi = deepcopy(vc2)
    end
    end
    #println("Time for step $i: $TTTT")
    #println("Number of proper mults: $(numm[1])")
    TTT += TTTT

    #wi = At*(A*w[(i-1)+1]) - c(w,i,i-1)*w[i-1+1] - ( i >= 2 ? c(w, i, i-2)*w[i-2+1] : 0*w[1])
    push!(w, wi)
  end
  
  TT = Float64(0)
  R = 0 * w[1]
  for j in 0:i-1
    #R = R + divexact((transpose(w[j+1])*b)[1,1],(transpose(w[j+1])*(At*(A*w[j+1])))[1,1]) * w[j+1]
    if haskey(scalar, (j+1,j+1))
      r = scalar[(j+1,j+1)]
    else
      if haskey(precomp2, j + 1)
        vc2 = precomp2[j + 1]::nmod_mat
      else
        mul!(vr2, A, w[j + 1])
        mul!(vc2, At, vr2)
        precomp2[ j + 1] = deepcopy(vc2)
      end
      r = _s(w[j+1],vc2)
    end
    tee = [ Int(0) ]
    g = ccall((:n_gcdinv, :libflint), UInt, (Ptr{Int}, UInt, UInt), tee, r, m)
    if g != 1
      error("Noninvertible denominator")
    end

    TT += @elapsed R = R + _s(w[j + 1],w[1])*tee[1]*w[j+1]
  end
  #println("Time to sum up $TT")
  #println("Time to compute c $TTT")
  return R
end

function lanczos2(A::NmodSmat, At::NmodSmat, b::nmod_mat)
  m = A.modulus
  
  i = 0
  #At = transpose(A)

  const vc = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const vc2 = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const vc3 = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const vr = MatrixSpace(ResidueRing(ZZ, A.modulus), A.r, 1)() # for vr = A*something

  const v2 = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const v3 = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const w3 = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const w1 = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const w0 = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const w2 = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something
  const x = MatrixSpace(ResidueRing(ZZ, A.modulus), A.c, 1)() # for vc = At*something

  w0 = b
  w1 = deepcopy(w0)
  mul!(vr, A, w1)
  mul!(v2, At, vr)
  # compute all scalar products in one loop
  Cc1 = 0
  Cc2 = 0
  Cc3 = 0
  for l in 1:v2.r
    u1 = _raw_getindex(v2, l, 1)
    u2 = _raw_getindex(w1, l, 1)
    u3 = _raw_getindex(w0, l, 1)
    Cc1 = Cc1 + u1 * u1
    Cc2 = Cc2 + u1 * u2
    Cc3 = Cc3 + u2 * u3
  end

  t0 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc1, m, b._ninv) 
  t1 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc2, m, b._ninv) 
  t4 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc3, m, b._ninv)
  
  inv = [ Int(0) ]
  g = ccall((:n_gcdinv, :libflint), Int, (Ptr{Int}, Int, Int), inv, t1, m)
  if g != 1
    error("Noninvertible denominator")
  end
  t0overt1 = ccall((:n_mulmod2_preinv, :libflint), Int, (Int, Int, Int, UInt), t0, inv[1], m, b._ninv)
  t4overt1 = ccall((:n_mulmod2_preinv, :libflint), Int, (Int, Int, Int, UInt), t4, inv[1], m, b._ninv)

  _mul!(vc, t0overt1, w1)
  _sub!(w2, v2, vc)

  _mul!(x, t4overt1, w1)

  while !iszero(w2)
    i = i + 1
    mul!(vr, A, w2)
    mul!(v3, At, vr)
    Cc1 = 0
    Cc2 = 0
    Cc3 = 0
    Cc4 = 0
    Cc5 = 0

    for l in 1:v2.r
      u1 = _raw_getindex(v3, l, 1)
      u2 = _raw_getindex(w2, l, 1)
      u3 = _raw_getindex(v2, l, 1)
      u4 = _raw_getindex(w1, l, 1)
      u5 = _raw_getindex(w0, l, 1)
      Cc1 = Cc1 + u1 * u1
      Cc2 = Cc2 + u1 * u2
      Cc3 = Cc3 + u1 * u3
      Cc4 = Cc4 + u4 * u3
      Cc5 = Cc5 + u2 * u5
    end

    t0 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc1, m, b._ninv) 
    t1 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc2, m, b._ninv) 
    t2 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc3, m, b._ninv) 
    t3 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc4, m, b._ninv) 
    t4 = ccall((:n_mod2_preinv, :libflint), Int, (Int, Int, UInt), Cc5, m, b._ninv)

    inv = [ Int(0) ]
    g = ccall((:n_gcdinv, :libflint), Int, (Ptr{Int}, Int, Int), inv, t1, m)

    if g != 1
      error("Noninvertible denominator")
    end
    t0overt1 = ccall((:n_mulmod2_preinv, :libflint), Int, (Int, Int, Int, UInt), t0, inv[1], m, b._ninv)

    t4overt1 = ccall((:n_mulmod2_preinv, :libflint), Int, (Int, Int, Int, UInt), t4, inv[1], m, b._ninv)
    _mul!(vc, t0overt1, w2)
    _sub!(vc2, v3, vc)

    g = ccall((:n_gcdinv, :libflint), Int, (Ptr{Int}, Int, Int), inv, t3, m)

    if g != 1
      println(i)
      println(iszero(w1), iszero(v2))
      return w1, v2
      error("Noninvertible denominator")
    end
    t2overt3 = ccall((:n_mulmod2_preinv, :libflint), Int, (Int, Int, Int, UInt), t2, inv[1], m, b._ninv)

    _mul!(vc, t2overt3, w1)
    _sub!(w3, vc2, vc)

    _mul!(vc, t4overt1, w2)
    _add!(x, x, vc)
    ccall((:nmod_mat_set, :libflint), Void, (Ptr{nmod_mat}, Ptr{nmod_mat}), &w1, &w2)
    ccall((:nmod_mat_set, :libflint), Void, (Ptr{nmod_mat}, Ptr{nmod_mat}), &w2, &w3)
    ccall((:nmod_mat_set, :libflint), Void, (Ptr{nmod_mat}, Ptr{nmod_mat}), &v2, &v3)
  end
  
  return x
end

function transpose{T}(A::Smat{T})
  B = Smat{T}()
  B.r = A.c
  B.c = A.r
  for j in 1:cols(A)
    C = SmatRow{T}()
    for i in 1:rows(A)
      g(x) = x.col == j
      k = findfirst(g, A.rows[i].entry)
      #println("$j $i $k $(A.rows[i].entry[k])")
      if k != 0 
        push!(C.entry, Entry{T}(i, A.rows[i].entry[k].val))
        B.nnz = B.nnz + 1
      end
    end
    push!(B.rows, C)
  end
  return B
end

function *{T}(A::Smat{T}, B::MatElem{T})
  V = zero(MatrixSpace(parent(B).base_ring, A.r, 1))
  for i in 1:rows(A)
    c = B.parent.base_ring(0)
    for k in 1:length(A.rows[i].entry)
      c = c + A.rows[i].entry[k].val * B[A.rows[i].entry[k].col,1]
    end
    V[i,1] = c
  end
  return V
end


