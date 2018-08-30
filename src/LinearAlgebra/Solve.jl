@doc Markdown.doc"""
    rand!(a::nf_elem, U::AbstractArray) -> nf_elem
> Inplace, set the coefficients of $a$ to random elements in $U$.
> $a$ is returned.
"""
function rand!(a::nf_elem, U::AbstractArray)
  for i=1:degree(parent(a))
    _num_setcoeff!(a, i-1, rand(U))
  end
  return a
end    

@doc Markdown.doc"""
    rand(K::AnticNumberField, U::AbstractArray) -> nf_elem
> Find an element in $K$ where the coefficients are selceted at random in $U$.
"""
function rand(K::AnticNumberField, U::AbstractArray)
  a = K()
  return rand!(a, U)
end

@doc Markdown.doc"""
    rand!(A::Generic.Mat{nf_elem}, U::AbstractArray) -> Generic.Mat{nf_elem}
> Inplace, replace each element in $A$ by an element where the coefficients are
> sected at random in $U$.
> Returns $A$.
"""
function rand!(A::Generic.Mat{nf_elem}, U::AbstractArray)
  for i=1:rows(A)
    for j=1:cols(A)
      rand!(A[i,j], U)
    end
  end
  return A
end    

@doc Markdown.doc"""
    rand(A::Generic.MatSpace{nf_elem}, U::AbstractArray) -> Generic.Mat{nf_elem}
> Create a random matrix in $A$ where the coefficients are selected from $U$.
"""
function rand(A::Generic.MatSpace{nf_elem}, U::AbstractArray)
  return rand!(A(), U)
end

@doc Markdown.doc"""
    modular_lift(ap::Array{fq_nmod_mat, 1}, me::modular_env) -> Array
> Given an array of matrices as computed by \code{modular_proj},
> compute a global pre-image using some efficient CRT.
"""
function modular_lift(ap::Array{fq_nmod_mat, 1}, me::modular_env)
  A = zero_matrix(me.K, rows(ap[1]), cols(ap[1]))
  for i=1:rows(A)
    for j=1:cols(A)
      A[i,j] = modular_lift([ap[k][i,j] for k=1:length(ap)], me)
    end
  end
  return A
end

@doc Markdown.doc"""
    mod!(A::Generic.Mat{nf_elem}, m::fmpz)
> Inplace: reduce all entries of $A$ modulo $m$, into the positive residue system.
"""
function mod!(A::Generic.Mat{nf_elem}, m::fmpz)
  for i=1:rows(A)
    for j=1:cols(A)
      mod!(A[i,j], m)
    end
  end
end

@doc Markdown.doc"""
    mod_sym!!(A::Generic.Mat{nf_elem}, m::fmpz)
> Inplace: reduce all entries of $A$ modulo $m$, into the symmetric residue system.
"""
function mod_sym!(A::Generic.Mat{nf_elem}, m::fmpz)
  for i=1:rows(A)
    for j=1:cols(A)
      mod_sym!(A[i,j], m)
    end
  end
end

function small_coeff(a::nf_elem, B::fmpz, i::Int)
  z = fmpz()
  Nemo.num_coeff!(z, a, i)
  return cmpabs(z, B) <= 0
end

@doc Markdown.doc"""
    rational_reconstruction(A::Generic.Mat{nf_elem}, M::fmpz) -> Bool, Generic.Mat{nf_elem}
> Apply \code{rational_reconstruction} to each entry of $M$.
"""
function rational_reconstruction2(A::Generic.Mat{nf_elem}, M::fmpz)
  B = similar(A)
  sM = root(M, 2)
  d = one(A[1,1])
  di = inv(d)
  for i=1:rows(A)
    for j=1:cols(A)
      a = A[i,j]*d
      mod_sym!(a, M)
      if all(i->small_coeff(a, sM, i), 1:a.elem_length)
        B[i,j] = a*di
      else
        n, dn = algebraic_reconstruction(a, M)
        d*=dn
        if any(i->!small_coeff(d, sM, i), 1:a.elem_length)
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

function rational_reconstruction(A::Generic.Mat{nf_elem}, M::fmpz)
  B = similar(A)
  for i=1:rows(A)
    for j=1:cols(A)
      fl, B[i,j] = rational_reconstruction(A[i,j], M)
      if !fl 
        return false, B
      end
    end
  end
  return true, B
end

function algebraic_reconstruction(a::nf_elem, M::fmpz)
  K = parent(a)
  n = degree(K)
  Znn = MatrixSpace(FlintZZ, n, n)
  L = [ Znn(1) representation_mat_q(a)[1] ; Znn(0) Znn(M)]
  lll!(L)
  d = Nemo.elem_from_mat_row(K, sub(L, 1:1, 1:n), 1, fmpz(1))
  n = Nemo.elem_from_mat_row(K, sub(L, 1:1, n+1:2*n), 1, fmpz(1))
  return n,d
  return true, n//d
end

function algebraic_reconstruction(a::nf_elem, M::NfAbsOrdIdl)
  K = parent(a)
  n = degree(K)
  Znn = MatrixSpace(FlintZZ, n, n)
  L = [ Znn(1) representation_mat_q(a)[1] ; Znn(0) basis_matrix(M, Val{false})]
  lll!(L)
  d = Nemo.elem_from_mat_row(K, sub(L, 1:1, 1:n), 1, fmpz(1))
  n = Nemo.elem_from_mat_row(K, sub(L, 1:1, n+1:2*n), 1, fmpz(1))
  return n,d
  return true, n//d
end


@doc Markdown.doc"""
    divexact!(A::Generic.Mat{nf_elem}, p::fmpz) 
> Inplace: divide each entry by $p$.
"""
function divexact!(A::Generic.Mat{nf_elem}, p::fmpz)
  for i=1:rows(A)
    for j=1:cols(A)
      A[i,j] = A[i,j]//p
    end
  end
end

#TODO/ To experiment:
# - vector reconstruction ala Storjohan
# - reconstruction with algebraic denominators
# - vector reconstruction with algebraic denominators
# - Talk to Bill: fq_nmod_mat is missing in Nemo, the inv is dreadfully slow
# - extend to non-unique solutions
# - make Aip*D mult faster, A*y as well?
#
function Nemo.solve_dixon(A::Generic.Mat{nf_elem}, B::Generic.Mat{nf_elem})
  p = next_prime(p_start)
  K = base_ring(A)
  
  me = modular_init(K, p)
  ap = modular_proj(A, me)
  @time ap = [inv(x) for x= ap]
  Aip = modular_lift(ap, me)
  sol = 0*B
  D = B
  pp = fmpz(1)
  last_SOL = false
  nd = 0
  while true
    nd += 1
    y = Aip*D
    mod!(y, fmpz(p))
    sol += y*pp
    pp *= p
    fl, SOL = rational_reconstruction(sol, pp)
#    t = A*sol-B
#    mod!(t, pp)
#    @assert iszero(t)
    if fl 
      if last_SOL == SOL && A*SOL == B
        println("used $nd $p-adic digits")
        return SOL
      else
        last_SOL = SOL
      end
    end
    D = D - A*y
    divexact!(D, fmpz(p))
#    if nbits(pp) > 10000 # a safety device to avoid infinite loops
#      error("not work")
#    end
  end
end


