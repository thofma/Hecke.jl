Markdown.doc"""
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

Markdown.doc"""
    rand(K::AnticNumberField, U::AbstractArray) -> nf_elem
> Find an element in $K$ where the coefficients are selceted at random in $U$.
"""
function rand(K::AnticNumberField, U::AbstractArray)
  a = K()
  return rand!(a, U)
end

Markdown.doc"""
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

Markdown.doc"""
    rand(A::Generic.MatSpace{nf_elem}, U::AbstractArray) -> Generic.Mat{nf_elem}
> Create a random matrix in $A$ where the coefficients are selected from $U$.
"""
function rand(A::Generic.MatSpace{nf_elem}, U::AbstractArray)
  return rand!(A(), U)
end

Markdown.doc"""
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

Markdown.doc"""
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

Markdown.doc"""
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

Markdown.doc"""
    rational_reconstruction(A::Generic.Mat{nf_elem}, M::fmpz) -> Bool, Generic.Mat{nf_elem}
> Apply \code{rational_reconstruction} to each entry of $M$.
"""
function rational_reconstruction(A::Generic.Mat{nf_elem}, M::fmpz)
  B = similar(A)
  for i=1:rows(A)
    for j=1:cols(A)
      fl, B[i,j] = rational_reconstruction(A[i,j], M)
      if !fl
        return fl, B
      end
    end
  end
  return true, B
end

Markdown.doc"""
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
  while true
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


