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

type NfMaxOrdQuoRingElem
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
  print(io, "Element $(x.elem)\n of\n$(parent(x))")
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
  # ( 0  M_y  M_y )
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
  println(U)
  U = hnf(U)
  println(U)
  println("coeff: $(fmpz[ U[1, i] for i in (d + 2):(2*d + 1)])")
  z = R(-base_ring(R)(fmpz[ U[1, i] for i in (d + 2):(2*d + 1)]))
  println(z)
  @assert z*y == x
  return z
end
