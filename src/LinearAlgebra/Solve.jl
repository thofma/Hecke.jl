@doc raw"""
    rand!(a::AbsSimpleNumFieldElem, U::AbstractArray) -> AbsSimpleNumFieldElem

Inplace, set the coefficients of $a$ to random elements in $U$.
$a$ is returned.
"""
function rand!(a::AbsSimpleNumFieldElem, U::AbstractArray)
  for i=1:degree(parent(a))
    _num_setcoeff!(a, i-1, rand(U))
  end
  return a
end

@doc raw"""
    rand(K::AbsSimpleNumField, U::AbstractArray) -> AbsSimpleNumFieldElem

Find an element in $K$ where the coefficients are selected at random in $U$.
"""
function rand(K::AbsSimpleNumField, U::AbstractArray)
  a = K()
  return rand!(a, U)
end

@doc raw"""
    rand!(A::Generic.Mat{AbsSimpleNumFieldElem}, U::AbstractArray) -> Generic.Mat{AbsSimpleNumFieldElem}

Inplace, replace each element in $A$ by an element where the coefficients are
selected at random in $U$.
Returns $A$.
"""
function rand!(A::Generic.Mat{AbsSimpleNumFieldElem}, U::AbstractArray)
  for i=1:nrows(A)
    for j=1:ncols(A)
      rand!(A[i,j], U)
    end
  end
  return A
end

@doc raw"""
    rand(A::Generic.MatSpace{AbsSimpleNumFieldElem}, U::AbstractArray) -> Generic.Mat{AbsSimpleNumFieldElem}

Create a random matrix in $A$ where the coefficients are selected from $U$.
"""
function rand(A::Generic.MatSpace{AbsSimpleNumFieldElem}, U::AbstractArray)
  return rand!(A(), U)
end

@doc raw"""
    modular_lift(ap::Vector{fqPolyRepMatrix}, me::modular_env) -> Array

Given an array of matrices as computed by \code{modular_proj},
compute a global pre-image using some efficient CRT.
"""
function modular_lift(ap::Vector{fqPolyRepMatrix}, me::modular_env)
  A = zero_matrix(me.K, nrows(ap[1]), ncols(ap[1]))
  for i=1:nrows(A)
    for j=1:ncols(A)
      A[i,j] = modular_lift([ap[k][i,j] for k=1:length(ap)], me)
    end
  end
  return A
end



function small_coeff(a::AbsSimpleNumFieldElem, B::ZZRingElem, i::Int)
  z = ZZRingElem()
  Nemo.num_coeff!(z, a, i)
  return cmpabs(z, B) <= 0
end

@doc raw"""
    rational_reconstruction(A::Generic.Mat{AbsSimpleNumFieldElem}, M::ZZRingElem) -> Bool, Generic.Mat{AbsSimpleNumFieldElem}

Apply \code{rational_reconstruction} to each entry of $M$.
"""
function rational_reconstruction2(A::Generic.Mat{AbsSimpleNumFieldElem}, M::ZZRingElem)
  B = similar(A)
  sM = root(M, 2)
  d = one(A[1,1])
  di = inv(d)
  for i=1:nrows(A)
    for j=1:ncols(A)
      a = A[i,j]*d
      if degree(parent(a)) == 1
        a_len = 1
      elseif degree(parent(a)) == 2
        a_len = 2
      else
        a_len = a.elem_length
      end
      mod_sym!(a, M)
      if all(i->small_coeff(a, sM, i), 1:a_len)
        B[i,j] = a*di
      else
        n, dn = algebraic_reconstruction(a, M)
        d*=dn
        if any(i->!small_coeff(d, sM, i), 1:a_len)
          println("early $i $j abort")
          return false, B
        end
        di*=inv(dn)
        B[i,j] = n*di
      end
    end
  end
  println("final den: $d")
  return true, B//d
end

function rational_reconstruction(A::Generic.Mat{AbsSimpleNumFieldElem}, M::ZZRingElem)
  B = similar(A)
  for i=1:nrows(A)
    for j=1:ncols(A)
      fl, B[i,j] = rational_reconstruction(A[i,j], M)
      if !fl
        return false, B
      end
    end
  end
  return true, B
end

function algebraic_reconstruction(a::AbsSimpleNumFieldElem, M::ZZRingElem)
  K = parent(a)
  n = degree(K)
  Znn = matrix_space(FlintZZ, n, n)
#  L = [ Znn(1) representation_matrix_q(a)[1] ; Znn(0) Znn(M)]
  L = vcat(hcat(Znn(1), representation_matrix_q(a)[1]), hcat(Znn(0),Znn(M)))
  lll!(L)
  d = Nemo.elem_from_mat_row(K, sub(L, 1:1, 1:n), 1, ZZRingElem(1))
  n = Nemo.elem_from_mat_row(K, sub(L, 1:1, n+1:2*n), 1, ZZRingElem(1))
  return n,d
  return true, n//d
end

function algebraic_reconstruction(a::AbsSimpleNumFieldElem, M::AbsNumFieldOrderIdeal)
  K = parent(a)
  n = degree(K)
  Znn = matrix_space(FlintZZ, n, n)
  L = [ Znn(1) representation_matrix_q(a)[1] ; Znn(0) basis_matrix(M, copy = false)]
  lll!(L)
  d = Nemo.elem_from_mat_row(K, sub(L, 1:1, 1:n), 1, ZZRingElem(1))
  n = Nemo.elem_from_mat_row(K, sub(L, 1:1, n+1:2*n), 1, ZZRingElem(1))
  return n,d
  return true, n//d
end

@doc raw"""
    algebraic_split(a::AbsSimpleNumFieldElem) -> AbsSimpleNumFieldElem, AbsSimpleNumFieldElem

Writes the input as a quotient of two "small" algebraic integers.
"""
function algebraic_split(a::AbsSimpleNumFieldElem)
  n = degree(parent(a))
  d = denominator(a)
  M, dd = representation_matrix_q(a)
  @assert d == dd
  #need to scale to make sure the kernel is found. Maybe better to
  #actually find the kernel and then look for small elements
  #a = be/ga <=> M_a * ga - I * be = 0 (this is the kernel)
  #furthermore, I want be and ga to be "small" - the LLL
  M = [M*dd identity_matrix(FlintZZ, n); -d^2*identity_matrix(FlintZZ, n) zero_matrix(FlintZZ, n, n)]
  L = lll(M)
  @assert iszero(L[1, 1:n])
  L = L[1, n+1:2*n]
  ga = parent(a)(collect(L))
  be = a*ga
  @assert denominator(be) == 1
  return be, ga
end

#function denominator_ideal(M::Generic.MatSpaceElem{AbsSimpleNumFieldElem}, den::AbsSimpleNumFieldElem)
function denominator_ideal(M::Vector{AbsSimpleNumFieldElem}, den::AbsSimpleNumFieldElem)
  k = parent(M[1,1])
  zk = maximal_order(k)
  _, d = integral_split(M[1]//den * zk)
  g = simplify(den*zk * inv(d)).num ## should be small
  if isone(g)
    return d
  end

  for m = M
    i = simplify(ideal(zk, minimum(g)^2, zk(m)))
    j = simplify(i*inv(g))
    if denominator(j) == 1
      continue
    end
    _, dd = integral_split(m//den * zk)
    d = lcm(d, dd)
    g = simplify(simplify(den*zk * inv(d)).num)
    if isone(g)
      break
    end
  end
  return d
end


#TODO/ To experiment:
# - vector reconstruction ala Storjohan
# - reconstruction with algebraic denominators
# - vector reconstruction with algebraic denominators
# - Talk to Bill: fqPolyRepMatrix is missing in Nemo, the inv is dreadfully slow
# - extend to non-unique solutions
# - make Aip*D mult faster, A*y as well?
#
function _solve_dixon(A::Generic.Mat{AbsSimpleNumFieldElem}, B::Generic.Mat{AbsSimpleNumFieldElem})
  p = next_prime(p_start)
  K = base_ring(A)

  me = modular_init(K, p)
  ap = modular_proj(A, me)
  ap = [inv(x) for x= ap]
  Aip = modular_lift(ap, me)
  sol = 0*B
  D = B
  pp = ZZRingElem(1)
  last_SOL = false
  nd = 0
  while true
    nd += 1
    y = Aip*D
    mod!(y, ZZRingElem(p))
    sol += y*pp
    pp *= p
    fl, SOL = rational_reconstruction(sol, pp)
#    t = A*sol-B
#    mod!(t, pp)
#    @assert iszero(t)
    if fl
      if last_SOL == SOL && A*SOL == B
        #println("used $nd $p-adic digits")
        return SOL
      else
        last_SOL = SOL
      end
    end
    D = D - A*y
    divexact!(D, ZZRingElem(p))
#    if nbits(pp) > 10000 # a safety device to avoid infinite loops
#      error("not work")
#    end
  end
end
