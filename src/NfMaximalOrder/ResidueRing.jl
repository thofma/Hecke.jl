export quo

type NfMaxOrdQuoRing <: Ring
  base_ring::NfMaximalOrder
  ideal::NfMaximalOrderIdeal
  basis_mat::fmpz_mat

  function NfMaxOrdQuoRing(O::NfMaximalOrder, I::NfMaximalOrderIdeal)
    z = new()
    z.base_ring = O
    z.ideal = I
    z.basis_mat = basis_mat(I)

    return z
  end
end

base_ring(Q::NfMaxOrdQuoRing) = Q.base_ring

ideal(Q::NfMaxOrdQuoRing) = Q.ideal

basis_mat(Q::NfMaxOrdQuoRing) = Q.basis_mat

function show(io::IO, Q::NfMaxOrdQuoRing)
  print(io, "Quotient of $(Q.base_ring)")# and ideal $(Q.ideal)")
end

type NfMaxOrdQuoRingElem <: RingElem
  elem::NfOrderElem
  parent::NfMaxOrdQuoRing

  function NfMaxOrdQuoRingElem(O::NfMaxOrdQuoRing, x::NfOrderElem)
    z = new()
    z.elem = mod(x, ideal(O))
    z.parent = O
    return z
  end
end

parent(x::NfMaxOrdQuoRingElem) = x.parent

function show(io::IO, x::NfMaxOrdQuoRingElem)
  print(io, "$(x.elem)")
end

function call(O::NfMaxOrdQuoRing, x::NfOrderElem)
  parent(x) != base_ring(O) && error("Cannot coerce element into the quotient ring")
  return NfMaxOrdQuoRingElem(O, x)
end

type NfMaxOrdQuoMap <: Map{NfMaximalOrder, NfMaxOrdQuoRing}
  header::MapHeader{NfMaximalOrder, NfMaxOrdQuoRing}

  function NfMaxOrdQuoMap(O::NfMaximalOrder, Q::NfMaxOrdQuoRing)
    z = new()
    
    _image = function (x::NfOrderElem)
      return Q(x)
    end

    _preimage = function (x::NfMaxOrdQuoRing)
      return x.elem
    end

    z.header = MapHeader(O, Q, _image, _preimage)
    return z
  end
end

function quo(O::NfMaximalOrder, I::NfMaximalOrderIdeal)
  # We should check that I is not zero
  Q = NfMaxOrdQuoRing(O, I)
  f = NfMaxOrdQuoMap(O, Q)
  return Q, f
end

function +(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem + y.elem)
end

function -(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem - y.elem)
end

function -(x::NfMaxOrdQuoRingElem)
  return parent(x)(-x.elem)
end

function *(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  return parent(x)(x.elem * y.elem)
end

function *(x::Integer, y::NfMaxOrdQuoRingElem)
  return parent(x)(x * y.elem)
end

*(x::NfMaxOrdQuoRingElem, y::Integer) = y*x

function *(x::fmpz, y::NfMaxOrdQuoRingElem)
  return parent(x)(x * y.elem)
end

*(x::NfMaxOrdQuoRingElem, y::fmpz) = y*x

==(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem) = x.elem == y.elem

function divexact(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  parent(x) != parent(y) && error("Elements must have same parents")
  R = parent(x)
  d = degree(base_ring(R))
  # We cannot solve with non-square matrices.
  # Thus build the matrix
  # ( 1   x    0  )
  # ( 0  M_y   I  )
  # ( 0  M_I   0  ).
  # Compute the HNF ->
  # ( 1   0   u )
  # ( *   *   * )
  # u will be the coefficient vector of the quotient
  A = representation_mat(y.elem)
  B = basis_mat(parent(x))
  C = MatrixSpace(ZZ, 1, d)()
  a = elem_in_basis(x.elem)
  for i in 1:d
    C[1, i] = a[i]
  end
  D = MatrixSpace(ZZ, 2*d + 1, 1)()
  U = vcat(A, B)
  U = vcat(C, U)
  U = hcat(D, U)
  U = hcat(U, vcat(vcat(MatrixSpace(ZZ, 1, d)(), one(parent(A))), parent(A)()))
  U[1,1] = 1
  U = hnf(U)
  v = submat(U, 1:1, (d + 2):(2*d + 1))
  z = R(-base_ring(R)(fmpz[ v[1, i] for i in 1:d]))
  @assert z*y == x
  return z
end

euclid(x::NfMaxOrdQuoRingElem) = is_zero(x) ? fmpz(-1) : norm(ideal(base_ring(parent(x)), x.elem) + parent(x).ideal)

is_zero(x::NfMaxOrdQuoRingElem) = x.elem.elem_in_nf == 0

function divrem(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  q = rand(parent(x))
  r = x - q*y
  e = euclid(y)
  while euclid(r) < e
    q = rand(parent(x))
    r = x - q*y
  end
  return q, r
end

function rand(Q::NfMaxOrdQuoRing)
  A = basis_mat(Q)
  B = basis(base_ring(Q))
  z = rand(fmpz(1):A[1,1]) * B[1]

  for i in 2:rows(A)
    z = z + rand(fmpz(1):A[i, i]) * B[i]
  end

  return Q(z)
end

elem_type(::Type{NfMaxOrdQuoRing}) = NfMaxOrdQuoRingElem


function call(f::NfMaxOrdQuoMap, I::NfMaximalOrderIdeal)
  O = domain(f)
  Q = codomain(f)
  B = Q.ideal + I
  b = basis(B)

  z = O()

  while true
    z = rand(fmpz(1):norm(Q.ideal)^2) * b[1]

    for i in 2:degree(O)
      z = z + rand(fmpz(1):norm(Q.ideal)^2) * b[i]
    end

    if norm(ideal(O, z) + ideal(O, O(norm(Q.ideal)))) == norm(B)
      break
    end
  end

  return Q(z)
end

function annihilator(x::NfMaxOrdQuoRingElem)
  I = parent(x).ideal
  O = base_ring(parent(x))
  f = NfMaxOrdQuoMap(O, parent(x))
  M_I = basis_mat(I)
  M_x = representation_mat(x.elem)
  U = vcat(M_x, M_I)
  m = _kernel(U)
  @assert rows(m) == degree(O)
  @assert cols(m) == 2*degree(O)
  I = ideal(O, _hnf(submat(m, 1:degree(O), 1:degree(O)), :lowerleft))
  return f(I)
end

function _kernel(x::fmpz_mat)
  H, U = hnf_with_transform(x)
  i = 1
  for i in 1:rows(H)
    if is_zero_row(H, i)
      break
    end
  end
  return submat(U, i:rows(U), 1:cols(U))
end

function _divexact_strong(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  n = euclid(x)
  m = euclid(y)
  @assert mod(n, m) == 0
  target = divexact(n, m)

  q0 = divexact(x, y)

  if euclid(q0) == target
    return q0
  else
    i = annihilator(y)

    q = q0 + rand(parent(x))*i

    while euclid(q) != target 
      q = q0 + rand(parent(x))*i
    end
  end

  @assert q*y == x
  @assert euclid(q) *euclid(y) == euclid(x)

  return q
end

function gcd(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  Q = parent(x)
  O = base_ring(Q)

  I = ideal(O, x.elem) + ideal(O, y.elem)

  f = NfMaxOrdQuoMap(O, parent(x))

  return f(I)
end

function xxgcd(x::NfMaxOrdQuoRingElem, y::NfMaxOrdQuoRingElem)
  Q = parent(x)
  O = base_ring(Q)

  d = degree(O)

  if is_zero(x)
    return deepcopy(y), Q(O(0)), Q(O(1)), Q(O(-1)), Q(O(0))
  elseif is_zero(y)
    return deepcopy(x), Q(O(1)), Q(O(0)), Q(O(0)), Q(O(-1))
  end

  g = gcd(x, y)

  e = _divexact_strong(x, g)
  f = _divexact_strong(y, g)

  @assert euclid(gcd(e, f)) == 1

  M_e = representation_mat(e.elem)
  M_f = representation_mat(f.elem)

  M_I = basis_mat(Q)

  # let us build
  # ( 1  Q(1) 0  0 )
  # ( 0  M_e  I  0 )
  # ( 0  M_f  0  I )
  # ( 0  M_I  0  0 )

  C = MatrixSpace(ZZ, 1, d)()::fmpz_mat
  a = elem_in_basis(Q(O(1)).elem)
  for i in 1:d
    C[1, i] = a[i]
  end

  IdMat = one(MatrixSpace(ZZ, d, d))
  ZeMat = zero(MatrixSpace(ZZ, d, d))

  U = hcat(MatrixSpace(ZZ, 3*d + 1, 1)(), vcat(vcat(vcat(C, M_e), M_f), M_I))
  U = hcat(U, vcat(vcat(vcat(parent(C)(), IdMat), ZeMat), ZeMat))
  U = hcat(U, vcat(vcat(vcat(parent(C)(), ZeMat), IdMat), ZeMat))
  U[1, 1] = 1

  U = hnf(U)::fmpz_mat

  u = Q(-O([ U[1,i] for i in (d + 2):(2*d + 1)]))
  v = Q(-O([ U[1,i] for i in (2*d + 2):(3*d + 1)]))

  @assert g == u*x + v*y
  @assert Q(O(1)) == u*e - (v*(-f))

  return g, u, v, -f, e
end

function howell_form(A::Mat{NfMaxOrdQuoRingElem})
  #A = deepcopy(B)
  n = rows(A)
  m = cols(A)
  if n < m
    A = vcat(A, MatrixSpace(base_ring(A), m-n, m)())
  end
  for j in 1:m
    for i in j+1:n
      #print("Computing xgcd of $(_raw_getindex(A,j,j)), $(_raw_getindex(A,i,j))\n")
      g,s,t,u,v = xxgcd(A[j,j], A[i,j])
      #println("$g $s $t $u $v ")
      for k in 1:m
        t1 = s*A[j, k] + t*A[i, k]
        t2 = u*A[j, k] + v*A[i, k]
        A[j, k] = t1
        A[i, k] = t2
      end
    end
    #println(A)
  end
  #println("I have a triangular matrix:")
  #println(A)
  T = MatrixSpace(base_ring(A), 1, cols(A))()
  # We do not normalize!
  for j in 1:m
    if !is_zero(A[j,j]) != 0
#      #println("nonzero case")
#      u = _unit(_raw_getindex(A,j,j), A._n)
#      for k in 1:m
#        t1 = mod(u*_raw_getindex(A,j,k), A._n)
#        ccall((:nmod_mat_set_entry, :libflint), Void, (Ptr{nmod_mat}, Int, Int, UInt), &A, j - 1, k - 1, t1)
#      end
#      for i in 1:j-1
#        q = UInt(prem(- Int(div(_raw_getindex(A, i, j), _raw_getindex(A, j, j))), Int(A._n)))
#        for k in j:m
#          _raw_setindex(A, i, k, mod(_raw_getindex(A, i, k) + q *_raw_getindex(A, j, k), A._n))
#        end
#      end
      #print("computing the annihilator for $j ... ")
      a = annihilator(A[j, j])
      #println("annihilator is $l")
      if is_zero(a)
        continue
      end
      for k in 1:m
        T[1, k] = a*A[j, k]
      end
    else
      for k in 1:m
        T[1, k] = A[j, k]
      end
    end

    for i in j+1:m 
      g,s,t,u,v = xxgcd(A[i, i], T[1, i])
      for k in 1:m
        t1 = s*A[i, k] + t*T[1, k]
        t2 = u*A[i, k] + v*T[1, k]
        A[i, k] = t1
        T[1, k] = t2
      end
    end
  end
  return A
end

elem_type(::NfMaxOrdQuoRing) = NfMaxOrdQuoRingElem

zero(Q::NfMaxOrdQuoRing) = Q(zero(base_ring(Q)))

deepcopy(x::NfMaxOrdQuoRingElem) = NfMaxOrdQuoRingElem(parent(x), x.elem)

function call(M::MatrixSpace{NfMaxOrdQuoRingElem}, x::Mat{NfOrderElem})
  base_ring(base_ring(M)) != base_ring(parent(x)) && error("Base rings do not coincide")
  return M(map(base_ring(M), x.entries))
end

function call(M::MatrixSpace{NfOrderElem}, x::MatElem{fmpz})
  return M(NfOrderElem[ base_ring(M)(x[i, j]) for i in 1:rows(x), j in 1:cols(x)])
end

elem_type(::NfMaximalOrder) = NfOrderElem
