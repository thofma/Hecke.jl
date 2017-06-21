
################################################################################
#
#  Comparison
#
################################################################################


# At the moment ==(A::NfMaxOrdIdl, B::NfMaxOrdIdl)
# falls back to ==(A::NfOrdIdl, B::NfOrdIdl)

################################################################################
#
#  Prime ideals
#
################################################################################

doc"""
***
    isramified(O::NfMaxOrd, p::Int) -> Bool

> Returns whether the integer $p$ is ramified in $\mathcal O$.
> It is assumed that $p$ is prime.
"""
function isramified(O::NfMaxOrd, p::Int)
  lp = prime_decomposition(O, p)
  for P in lp
    if P[2] > 1
      return true
    end
  end
  return false
end

doc"""
***
    degree(P::NfMaxOrdIdl) -> Int
> The inertia degree of the prime-ideal $P$.
"""
function degree(A::NfMaxOrdIdl)
  @assert isprime(A)
  return A.splitting_type[2]
end

doc"""
***
    ramification_index(P::NfMaxOrdIdl) -> Int
> The ramification index of the prime-ideal $P$.
"""
function ramification_index(A::NfMaxOrdIdl)
  @assert isprime(A)
  return A.splitting_type[1]
end

doc"""
***
    splitting_type(P::NfMaxOrdIdl) -> Int, Int
> The ramification index and inertia degree of the prime ideal $P$.
> First value is the ramificatio index, the second the degree of $P$.
"""
function splitting_type(A::NfMaxOrdIdl)
  @assert isprime(A)
  return A.splitting_type
end

################################################################################
#
#  Prime decomposition
#
################################################################################

##TODO: make fmpz-safe!!!!

doc"""
***
    prime_decomposition(O::NfMaxOrd,
                        p::Integer,
                        degree_limit::Int = 0,
                        lower_limit::Int = 0) -> Array{Tuple{NfMaxOrdIdl, Int}, 1}

> Returns an array of tuples $(\mathfrak p_i,e_i)$ such that $p \mathcal O$ is the product of
> the $\mathfrak p_i^{e_i}$ and $\mathfrak p_i \neq \mathfrak p_j$ for $i \neq j$.
>
> If `degree_limit` is a nonzero integer $k > 0$, then only those prime ideals
> $\mathfrak p$ with $\deg(\mathfrak p) \leq k$ will be returned.
> Similarly if `\lower_limit` is a nonzero integer $l > 0$, then only those prime ideals
> $\mathfrak p$ with $l \leq \deg(\mathfrak p)$ will be returned.
> Note that in this case it may happen that $p\mathcal O$ is not the product of the
> $\mathfrak p_i^{e_i}$.
"""
function prime_decomposition(O::NfMaxOrd, p::Integer, degree_limit::Int = 0, lower_limit::Int = 0)
  if mod(fmpz(index(O)),p) == 0
    return prime_dec_index(O, p, degree_limit, lower_limit)
  end
  return prime_dec_nonindex(O, p, degree_limit, lower_limit)
end

function prime_dec_nonindex(O::NfMaxOrd, p::Integer, degree_limit::Int = 0, lower_limit::Int = 0)
  K = nf(O)
  f = K.pol
  I = IdealSet(O)
  R = parent(f)
  Zx, x = PolynomialRing(FlintIntegerRing(),"x")
  Zf = Zx(f)
  Zmodpx = PolynomialRing(ResidueRing(FlintIntegerRing(), p, cached=false), "y", cached=false)[1]
  fmodp = Zmodpx(Zf)
  fac = factor(fmodp)
  _fac = Dict{typeof(fmodp), Int}()
  if degree_limit == 0
    degree_limit = degree(K)
  end
  for (k,v) in fac
    if degree(k) <= degree_limit && degree(k) >= lower_limit
      _fac[k] = v
    end
  end
  fac = _fac
  result = Array{Tuple{typeof(I()),Int}}(length(fac))
  k = 1
  t = fmpq_poly()
  b = K()
  #fill!(result,(I(),0))
  for (fi, ei) in fac
    t = parent(f)(lift(Zx,fi))
    b = K(t)
    ideal = I()
    ideal.gen_one = p
    ideal.gen_two = O(b, false)
    ideal.is_prime = 1
    ideal.parent = I
    ideal.splitting_type = ei, degree(fi)
    ideal.norm = ZZ(p)^degree(fi)
    ideal.minimum = ZZ(p)

    # We have to do something to get 2-normal presentation:
    # if ramified or valuation val(b,P) == 1, (p,b)
    # is a P(p)-normal presentation
    # otherwise we need to take p+b
    # I SHOULD CHECK THAT THIS WORKS

    if !((mod(norm(b),(ideal.norm)^2) != 0) || (ei > 1))
      ideal.gen_two = ideal.gen_two + O(p)
    end

    ideal.gens_normal = p
    ideal.gens_weakly_normal = true

    # Find an "anti-uniformizer" in case P is unramified
    # We don't call it anti-unfiformizer anymore

    #if ideal.splitting_type[1] == 1
    #  t = parent(f)(lift(Zx, divexact(fmodp, fi)))
    #  ideal.anti_uniformizer = O(K(t), false)
    #end

    if length(fac) == 1 && ideal.splitting_type[2] == degree(f)
      # Prime number is inert, in particular principal
      ideal.is_principal = 1
      ideal.princ_gen = O(p)
    end
    result[k] =  (ideal, ei)
    k += 1
  end
  return result
end

function prime_dec_index(O::NfMaxOrd, p::Int, degree_limit::Int = 0, lower_limit::Int = 0)
  if degree_limit == 0
    degree_limit = degree(O)
  end

  # Firstly compute the p-radical of O
  Ip = pradical(O, p)
  R = quoringalg(O, Ip, p)
  AA = split(R)

  I = IdealSet(O)
  result = Array{Tuple{typeof(I()),Int}, 1}()
  # We now have all prime ideals, but only their basis matrices
  # We need the ramification indices and a 2-element presentation

  for j in 1:length(AA)
    P = AA[j].ideal
    f = 0

    # First compute the residue degree
    for i in 1:degree(O)
      f = f + valuation(basis_mat(P)[i,i], fmpz(p))
    end

    P.norm = fmpz(p)^f

    if f > degree_limit || f < lower_limit
      continue
    end

    # The following does not work if there is only one prime ideal
    if length(AA) > 1 && (1-1/p)^degree(O) < 0.1
      # Finding the second element might take some time
      @vprint :NfMaxOrd 1 "chances are very low: ~$((1-1/p)^degree(O))"
      # This is rougly Algorithm 6.4 of Belabas' "Topics in comptutational algebraic
      # number theory".

      # Compute Vp = P_1 * ... * P_j-1 * P_j+1 * ... P_g
      if j == 1
        Vp = AA[2].ideal
        k = 3
      else
        Vp = AA[1].ideal;
        k = 2;
      end

      for i in k:length(AA)
        if i == j
          continue
        else
          Vp = intersection(Vp, AA[i].ideal)
        end
      end

      u, v = idempotents(P, Vp)

      x = zero(parent(u))

      if !iszero(mod(norm(u), norm(P)*p))
        x = u
      elseif !iszero(mod(norm(u + p), norm(P)*p))
        x = u + p
      elseif !iszero(mod(norm(u - p), norm(P)*p))
        x = u - p
      else
        for i in 1:degree(O)
          if !iszero(mod(norm(v*basis(P)[i] + u), norm(P)*p))
            x = v*basis(P)[i] + u
          end
        end
      end

      @hassert :NfMaxOrd 1 !iszero(x)
      @hassert :NfMaxOrd 2 O*O(p) + O*x == P
      
      P.gen_one = p
      P.gen_two = x
      P.gens_normal = p
      P.gens_weakly_normal = 1
    else
      _assure_weakly_normal_presentation(P)
      assure_2_normal(P)
    end

    e = Int(valuation(nf(O)(p), P))
    P.splitting_type = e, f
    P.is_prime = 1
    push!(result, (P, e))
  end
  return result
end

function uniformizer(P::NfMaxOrdIdl)
  p = minimum(P)
  if P.gens_normal == p
    return P.gen_two
  else
    if p > 250
      r = 500  # should still have enough elements...
    else
      r = Int(div(p, 2))
    end
    while true
      z = rand(P, r)
      if valuation(z, P) == 1
        break
      end
    end
  end
end

# Belabas p. 40
function anti_uniformizer(P::NfMaxOrdIdl)
  if isdefined(P, :anti_uniformizer)
    return P.anti_uniformizer
  else
    p = minimum(P)
    M = representation_mat(uniformizer(P))
    Mp = MatrixSpace(ResidueRing(FlintZZ, p), rows(M), cols(M))(M)
    p > typemax(Int) && error("Not yet implemented")
    K = kernel(Mp)
    @assert length(K) > 0
    P.anti_uniformizer = elem_in_nf(order(P)(_lift(K[1])))//p
    return P.anti_uniformizer
  end
end

# Don't use the following function. It does not work for index divisors
# TH: Or does it?
function prime_decomposition_type(O::NfMaxOrd, p::Integer)
  if (mod(discriminant(O), p)) != 0 && (mod(fmpz(index(O)), p) != 0)
    K = nf(O)
    f = K.pol
    R = parent(f)
    Zx, x = PolynomialRing(ZZ,"x")
    Zf = Zx(f)
    fmodp = PolynomialRing(ResidueRing(ZZ,p, cached = false), "y", cached = false)[1](Zf)
    fac = factor_shape(fmodp)
    g = sum([ x for x in values(fac)])
    res = Array{Tuple{Int, Int}}(g)
    k = 1
    for (fi, ei) in fac 
      for j in 1:ei
        res[k] = (fi, 1)
        k = k + 1
      end
    end
  else
    lp = prime_decomposition(O, p)
    res = Array{Tuple{Int, Int}}(length(lp))
    for i in 1:length(lp)
      res[i] = (lp[i][1].splitting_type[2], lp[i][1].splitting_type[1])
    end
  end
  return res
end

doc"""
***
    prime_ideals_up_to(O::NfMaxOrd,
                       B::Int;
                       degree_limit::Int = 0) -> Array{NfMaxOrdIdl, 1}

> Computes the prime ideals $\mathcal O$ with norm up to $B$.
> 
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_up_to(O::NfMaxOrd, B::Int;
                            complete::Bool = false,
                            degree_limit::Int = 0)
  p = 1
  r = NfMaxOrdIdl[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    if !complete
      deg_lim = Int(floor(log(B)/log(p)))
      if degree_limit >0
        deg_lim = min(deg_lim, degree_limit)
      end
    else
      deg_lim = 0
    end
    @vprint :ClassGroup 2 "decomposing $p ... (bound is $B, deg_lim $deg_lim)\n"
    li = prime_decomposition(O, p, deg_lim)
    for P in li
      push!(r, P[1])
    end
  end
  return r
end

doc"""
***
    prime_ideals_over(O::NfMaxOrd,
                       lp::AbstractArray{Int, 1};
                       degree_limit::Int = 0) -> Array{NfMaxOrdIdl, 1}

> Computes the prime ideals $\mathcal O$ over prime numbers in $lp$.
> 
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_over{T <: Union{fmpz, Integer}}(O::NfMaxOrd, lp::AbstractArray{T};
                            degree_limit::Int = 0)
  p = 1
  r = NfMaxOrdIdl[]
  for p in lp
    @vprint :ClassGroup 2 "decomposing $p ... (deg_lim $deg_lim)"
    li = prime_decomposition(O, p, degree_limit)
    for P in li
      push!(r, P[1])
    end
  end
  return r
end


doc"""
***
    prime_ideals_up_to(O::NfMaxOrd,
                       B::Int;
                       complete::Bool = false,
                       degree_limit::Int = 0,
                       F::Function,
                       bad::fmpz)

> Computes the prime ideals $\mathcal O$ with norm up to $B$.
> 
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
>
> The function $F$ must be a function on prime numbers not dividing `bad` such that
> $F(p) = \deg(\mathfrak p)$ for all prime ideals $\mathfrak p$ lying above $p$.
"""
function prime_ideals_up_to(O::NfMaxOrd, B::Int, F::Function, bad::fmpz = discriminant(O);
                            complete::Bool = false,
                            degree_limit::Int = 0)
  p = 1
  r = NfMaxOrdIdl[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    if !complete
      deg_lim = flog(fmpz(B), p) # Int(floor(log(B)/log(p)))
      if degree_limit > 0
        deg_lim = min(deg_lim, degree_limit)
      end
    else
      deg_lim = 0
    end
    @vprint :ClassGroup 2 "decomposing $p ... (bound is $B)"
    if mod(bad, p) == 0
      li = prime_decomposition(O, p, deg_lim)
      for P in li
        push!(r, P[1])
      end
    else
      if F(p) <= deg_lim
        li = prime_decomposition(O, p, deg_lim)
        for P in li
          push!(r, P[1])
        end
      end
    end
  end
  return r
end

################################################################################
#
#  Coprime
#
################################################################################
function coprime_base(A::Array{NfMaxOrdIdl, 1}, p::fmpz)
  Ap = [gcd(x, p) for x = A if minimum(x) % p == 0]
  return Hecke.coprime_base_steel(Ap)
end

doc"""
***
    coprime_base(A::Array{NfMaxOrdIdl, 1}) -> Array{NfMaxOrdIdl, 1}
    coprime_base(A::Array{NfOrdElem{NfMaxOrd}, 1}) -> Array{NfMaxOrdIdl, 1}
> A coprime base for the (principal) ideals in $A$, ie. the returned array
> generated multiplicatively the same ideals as the input and are pairwise 
> coprime.
"""
function coprime_base(A::Array{NfMaxOrdIdl, 1})
  a = collect(Set(map(minimum, A)))
  a = coprime_base(a)
  C = Array{NfMaxOrdIdl, 1}()

  for p = a
    cp = coprime_base(A, p)
    append!(C, cp)
  end
  return C
end

function coprime_base(A::Array{NfOrdElem{NfMaxOrd}, 1})
  O = parent(A[1])
  return coprime_base([ideal(O, x) for x = A])
end

function integral_split(A::NfMaxOrdIdl)
  return A, ideal(Order(A), fmpz(1))
end

################################################################################
#
#  Division
#
################################################################################

# We need to fix the two normal presentation of the trivial ideal
doc"""
***
    divexact(A::NfMaxOrdIdl, y::fmpz) -> NfMaxOrdIdl

> Returns $A/y$ assuming that $A/y$ is again an integral ideal.
"""
function divexact(A::NfMaxOrdIdl, y::fmpz)
#  if has_2_elem(A)
#    z = ideal(order(A), divexact(A.gen_one, y), divexact(A.gen_two, y))
#    if has_basis_mat(A)
#      z.basis_mat = divexact(A.basis_mat, y)
#    end
#  elseif has_basis_mat(A)
  if norm(order(A)(y)) == norm(A)
    return ideal(order(A), one(FlintZZ), order(A)(1))
  else
    m = basis_mat(A)
    z = ideal(order(A), divexact(m, y))
    _assure_weakly_normal_presentation(z)
    assure_2_normal(z)
    return z
  end
end

doc"""
***
    divexact(A::NfMaxOrdIdl, B::NfMaxOrdIdl) -> NfMaxOrdIdl

> Returns $AB^{-1}$ assuming that $AB^{-1}$ is again an integral ideal.
"""
function divexact(A::NfMaxOrdIdl, B::NfMaxOrdIdl)
  # It is assumed that B divides A, that is, A \subseteq B
  t_prod = 0.0
  t_simpl = 0.0
  t_b_mat = 0.0
  t_2_elem_weak = 0.0
  t_2_elem = 0.0

  if norm(A) == norm(B)
    return ideal(order(A), one(FlintZZ), order(A)(1))
  else
    t_prod += @elapsed I = A*inv(B)
    t_simpl += @elapsed simplify_exact(I)
    #t_b_mat += @elapsed B = basis_mat(I)
    I.den != 1 && error("Division not exact")
    #I = ideal(order(A), B.num)
    #t_2_elem_weak += @elapsed _assure_weakly_normal_presentation(I)
    #t_2_elem += @elapsed assure_2_normal(I)
    
    #println("  computation for product: $t_prod")
    #println("  simplification         : $t_simpl")
    #println("  basis matrix           : $t_b_mat")
    #println("  2 weak presentation    : $t_2_elem_weak")
    #println("  2 elem presentation    : $t_2_elem")

    return I.num

  end
end

################################################################################
#
#  Facotrization into prime ideals
#
################################################################################
#TODO: factoring type??? (with unit)
doc"""
***
    factor(A::NfMaxOrdIdl) -> Dict{NfMaxOrdIdl, Int}

> Computes the prime ideal factorization $A$ as a dictionary, the keys being
> the prime ideal divisors:
> If `lp = factor_dict(A)`, then `keys(lp)` are the prime ideal divisors of A
> and `lp[P]` is the `P`-adic valuation of `A` for all `P` in `keys(lp)`.
"""
factor(A::NfMaxOrdIdl) = factor_dict(A)

function factor_dict(A::NfMaxOrdIdl)
  ## this should be fixed
  lf = factor(minimum(A))
  lF = Dict{NfMaxOrdIdl, Int}()
  n = norm(A)
  O = order(A)
  for (i, (p, v)) in enumerate(lf)
    try
      p = Int(p)
    catch
      error("Prime divisor lying over prime > 2^63. Too large.")
    end
    lP = prime_decomposition(O, p)
    for P in lP
      v = valuation(A, P[1])
      if v != 0
        lF[P[1]] = v
        n = n//norm(P[1])^v
      end
      if n == 1 
        return lF
      end
    end
  end
  return lF
end

################################################################################
#
#  Functions for index divisor splitting
#
################################################################################

type quoringalg <: Ring
  base_order::NfMaxOrd
  ideal::NfMaxOrdIdl
  prime::Int
  basis::Array{NfOrdElem, 1}

  function quoringalg(O::NfMaxOrd, I::NfMaxOrdIdl, p::Int)
    z = new()
    z.base_order = O
    z.ideal = I
    z.prime = p

    # compute a basis
    Amodp = MatrixSpace(ResidueRing(ZZ, p), degree(O), degree(O))(basis_mat(I))
    Amodp = vcat(Amodp, MatrixSpace(ResidueRing(ZZ, p), 1, degree(O))())
    Amodp[1,1] = 1
    Amodp = sub(Amodp, 1:degree(O), 1:degree(O))

    # I think rref can/should also return the rank
    B = rref(Amodp)
    r = rank(B)
    C = zero(MatrixSpace(ResidueRing(ZZ, p), degree(O)-r, degree(O)))
    BB = Array{NfOrdElem}(degree(O) - r)
    pivots = Array{Int}(0)
#    # get he pivots of B
    for i in 1:r
      for j in 1:degree(O)
        if !iszero(B[i,j])
          push!(pivots, j)
          break
        end
      end
    end
    i = 1
    k = 1
    while i <= degree(O)-r
      for j in k:degree(O)
        if !in(j, pivots)
          BB[i] = basis(O)[j]
          C[i,j] = 1
          k = j + 1
          i = i + 1
          break
        end
      end
    end
    insert!(BB, 1, basis(O)[1])
    z.basis = BB
    return z
  end
end

type quoelem
  parent::quoringalg
  elem::NfOrdElem
  coord::Array{fmpz, 1}

  function quoelem(R::quoringalg, x::NfOrdElem)
    z = new()
    z.parent = R
    z.elem = x
    
    return z
  end
end
    
function _kernel_of_frobenius(R::quoringalg)
  O = R.base_order
  BB = R.basis
  p = R.prime
  C = zero(MatrixSpace(ResidueRing(ZZ, R.prime), length(BB)+1, degree(O)))
  D = zero(MatrixSpace(ResidueRing(ZZ, R.prime), length(BB), degree(O)))
  for i in 1:length(BB)
    A = elem_in_basis(mod(BB[i]^p - BB[i], R.ideal))
    for j in 1:degree(O)
      D[i,j] = A[j]
    end
  end

  DD = NfOrdElem[ dot(BB, _lift(r)) for r in kernel(D) ]

  return [ quoelem(R, r) for r in DD ]
end

function _lift(T::Array{GenRes{fmpz}, 1})
  return [ z.data for z in T ]
end

function *(x::quoelem, y::quoelem)
  z = mod(x.elem * y.elem, x.parent.ideal)
  return quoelem(x.parent, z)
end

function ^(x::quoelem, y::Int)
  z = mod(x.elem^y, x.parent.ideal)
  return quoelem(x.parent, z)
end

function ==(x::quoelem, y::quoelem)
  z = mod(x.elem - y.elem, x.parent.ideal)
  return zero(parent(z)) == z
end

function minpoly(x::quoelem)
  O = x.parent.base_order
  p = x.parent.prime

  A = MatrixSpace(ResidueRing(ZZ, p), 0, degree(O))()
  B = MatrixSpace(ResidueRing(ZZ, p), 1, degree(O))()

  for i in 0:degree(O)
    ar =  elem_in_basis( (x^i).elem)
    for j in 1:degree(O)
      B[1, j] = ar[j]
    end
    A = vcat(A, B)
    K = kernel(A)
    if length(K)>0
      @assert length(K)==1
      f = PolynomialRing(ResidueRing(ZZ, p), "x")[1](K[1])
      return f
    end
  end
  error("cannot find minpoly")
end

function split(R::quoringalg)
  if length(R.basis) == 1
    return [ R ]
  end
  K = _kernel_of_frobenius(R)
  O = R.base_order
  p = R.prime

  k = length(K)

  if k == 1
    # the algebra is a field over F_p
    # the ideal Ip is a prime ideal!
    return [ R ]
  end

  maxit = 1 

  while true
    maxit = maxit + 1
    r = rand(0:p-1, length(K))

    x = quoelem(R, dot([ x.elem for x in K], r))

    if mod((x^p).elem, R.ideal) != mod(x.elem, R.ideal)
      #println("element^p: $(mod((x^p).elem, R.ideal))")
      #println("element: $(mod(x.elem, R.ideal))")
      #println(R.ideal.basis_mat)
      #println(K)
      error("Strange")
    end

    f = minpoly(x)


    if degree(f) < 2 
      continue
    end
    @assert  issquarefree(f)

#    # By theory, all factors should have degree 1 # exploit this if p is small!
    fac = factor(f)
    F = first(keys(fac.fac))
    @assert length(fac) == degree(f)
    H = divexact(f,F)
    E, U, V = gcdx(F, H)
    @assert E == 1
    H = U*F;
    idem = O(coeff(H,0).data)
    for i in 1:degree(H)
      idem = idem + coeff(H,i).data*x.elem^i
    end

    I1 = R.ideal + ideal(O, idem)
    I2 = R.ideal + ideal(O, O(1)-idem)

    return vcat(split(quoringalg(O, I1, p)), split(quoringalg(O, I2, p)))
    break
  end
end



doc"""
*
  extended_euclid(A::NfMaxOrdIdl, B::NfMaxOrdIdl) -> (NfOrdElem{NfMaxOrd},NfOrdElem{NfMaxOrd})

> Returns elements $a \in A$ and $b \in B$ such that $a + b = 1$.
"""
function extended_euclid(A::NfMaxOrdIdl, B::NfMaxOrdIdl)
  @assert order(A) == order(B)
  O = order(A)
  n = degree(O)
  A_mat = hnf(basis_mat(A))
  B_mat = hnf(basis_mat(B))
  @hassert :NfMaxOrd 2 size(A_mat) == (n,n)
  @hassert :NfMaxOrd 2 size(B_mat) == (n,n)
  C = [ A_mat ; B_mat ]
  H, T = hnf_with_transform(C)
  @hassert :NfMaxOrd 2 submat(H,n+1,1,n,n) == 0
  H = submat(H,1,1,n,n)
  H != 1 && error("A and B not coprime")
  X = MatrixSpace(ZZ,1,n)()
  for i in 1:n
    X[1,i] = T[1,i]
  end
  coeffs = X*A_mat
  a = O(vec(Array(coeffs)))
  b = 1 - a
  @hassert :NfMaxOrd 2 a in A
  @hassert :NfMaxOrd 2 b in B
  return a, b
end


function trace_matrix(A::NfMaxOrdIdl)
  g = trace_matrix(order(A))
  b = basis_mat(A)
#  mul!(b, b, g)   #b*g*b' is what we want.
#                  #g should not be changed? b is a copy.
#  mul!(b, b, b')  #TODO: find a spare tmp-mat and use transpose
  return b*g*b'
end

function random_init(I::AbstractArray{NfMaxOrdIdl, 1}; reduce::Bool = true)
  J = collect(I)
  for i=1:length(J)
    a = rand(1:length(J))
    b = rand(1:length(J))
    if reduce && isodd(rand(1:2))
      J[a] = reduce_ideal(J[a]*inv(J[b]))
    else
      J[a] *= J[b]
      if reduce
        J[a] = reduce_ideal(J[a])
      end
    end
  end
  return J
end  

function random_get(J::Array{NfMaxOrdIdl, 1}; reduce::Bool = true)
  a = rand(1:length(J))
  I = J[a]
  b = rand(1:length(J))
  if reduce && isodd(rand(1:2))
    J[a] = reduce_ideal(J[a]*inv(J[b]))
  else
    J[a] *= J[b]
    if reduce
      J[a] = reduce_ideal(J[a])
    end
  end
  return I
end

################################################################################
#
#  Conversion to Magma
#
################################################################################
function toMagma(f::IOStream, clg::NfMaxOrdIdl, order::String = "M")
  print(f, "ideal<$(order)| ", clg.gen_one, ", ",
                    elem_in_nf(clg.gen_two), ">")
end

function toMagma(s::String, c::NfMaxOrdIdl, order::String = "M")
  f = open(s, "w")
  toMagma(f, c, order)
  close(f)
end

