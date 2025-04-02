################################################################################
#
#  Constructors
#
################################################################################


mutable struct Divisor
  function_field::AbstractAlgebra.Generic.FunctionField
  finite_ideal::GenOrdFracIdl
  infinite_ideal::GenOrdFracIdl
  finite_support::Dict{Hecke.GenOrdIdl, Int64}
  infinite_support::Dict{Hecke.GenOrdIdl, Int64}

  function Divisor(I::GenOrdFracIdl, J::GenOrdFracIdl)
    r = new()

    O = order(I)
    Oinf = order(J)
    K = function_field(O)

    @req K == function_field(Oinf) "Ideals need to belong to orders of the same function field."
    @req isa(base_ring(O), PolyRing) "First ideal needs to be an ideal over the finite order"
    @req isa(base_ring(Oinf), KInftyRing) "Second ideal needs to be an ideal over the infinite order"

    r.function_field = K
    r.finite_ideal = I
    r.infinite_ideal = J

    return r
  end

end

@attributes AbstractAlgebra.Generic.FunctionField

function trivial_divisor(F::Generic.FunctionField)
  return divisor(one(F))
end


@doc raw"""
    divisor(I::GenOrdFracIdl, J::GenOrdFracIdl) -> Divisor

Return the divisor corresponding to the factorization of the ideal I (for the finite places) and ideal J (for the infinite places)
"""
function divisor(I::GenOrdFracIdl, J::GenOrdFracIdl)
  return Divisor(I, J)
end

function divisor(I::GenOrdIdl, J::GenOrdIdl)
  return Divisor(GenOrdFracIdl(I), GenOrdFracIdl(J))
end

function divisor(I::GenOrdFracIdl, J::GenOrdIdl)
  return Divisor(I, GenOrdFracIdl(J))
end

function divisor(I::GenOrdIdl, J::GenOrdFracIdl)
  return Divisor(GenOrdFracIdl(I), J)
end

function divisor(I::GenOrdIdl)
  divisor(GenOrdFracIdl(I))
end

function divisor(I::GenOrdFracIdl)
  O = order(I)
  F = function_field(O)
  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)
  if O == Ofin
    return divisor(I, ideal(Oinf, one(Oinf)))
  elseif O == Oinf
    return divisor(ideal(Ofin, one(Ofin)), I)
  else
    error("There is a bug in divisor")
  end
end


@doc raw"""
    divisor(f::Generic.FunctionFieldElem) -> Divisor

Return the principal divisor consisting of the sum of zeroes and poles of f
"""
function divisor(f::Generic.FunctionFieldElem)
  @req !is_zero(f) "Element must be non-zero"
  F = parent(f)

  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)

  f_num, f_denom = integral_split(f, Ofin)
  g_num, g_denom = integral_split(f, Oinf)

  return divisor(colon(ideal(Ofin, f_num), ideal(Ofin, f_denom)), colon(ideal(Oinf, g_num), ideal(Oinf, g_denom)))
end

@doc raw"""
    zero_divisor(f::Generic.FunctionFieldElem) -> Divisor

Return the divisor consisting of the zeroes of f
"""
function zero_divisor(f::Generic.FunctionFieldElem)
  F = parent(f)

  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)

  f_num, f_denom = integral_split(f, Ofin)
  g_num, g_denom = integral_split(f, Oinf)

  return divisor(ideal(Ofin, f_num), ideal(Oinf, g_num))
end

@doc raw"""
    pole_divisor(f::Generic.FunctionFieldElem) -> Divisor

Return the divisor consisting of the poles of f
"""
function pole_divisor(f::Generic.FunctionFieldElem)
  F = parent(f)

  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)

  f_num, f_denom = integral_split(f, Ofin)
  g_num, g_denom = integral_split(f, Oinf)

  return divisor(ideal(Ofin, f_denom), ideal(Oinf, g_denom))
end

################################################################################
#
#  IO
#
################################################################################

function show(io::IO, id::Divisor)
  print(io, "Divisor in ideal representation:")
  print(io, "\nFinite ideal: ", id.finite_ideal)
  print(io, "\nInfinite ideal: ", id.infinite_ideal)
end

################################################################################
#
#  Field Access
#
################################################################################

@doc raw"""
    function_field(D::Divisor) -> FunctionField

Return the function field to which D belongs
"""
function function_field(D::Divisor)
  return D.function_field
end

@doc raw"""
    ideals(D::Divisor) -> GenOrdFracIdl, GenOrdFracIdl

Return a pair of ideals I, J that represent the divisor D. Here I is the ideal for the finite maximal order
and J is the ideal of the infinite maximal order.
"""
function ideals(D)
  return D.finite_ideal, D.infinite_ideal
end

@doc raw"""
    function_field(O::GenOrd) -> FunctionField

Return the function field of O.
"""
function function_field(O::GenOrd)
  return O.F
end

@doc raw"""
    constant_field(K::FunctionField) -> Field

Return the field of constants of K.
"""
function constant_field(K::AbstractAlgebra.Generic.FunctionField)
  return base_ring(base_ring(K))
end

@doc raw"""
    finite_maximal_order(K::FunctionFIeld) -> GenOrd

Return the finite maximal order of K
"""
function finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  get_attribute!(K, :finite_maximal_order) do
    return _finite_maximal_order(K)
  end
end

function _finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  kx = parent(numerator(gen(base_ring(K))))
  return integral_closure(kx, K)
end

@doc raw"""
    infinite_maximal_order(K::FunctionFIeld) -> GenOrd

Return the infinite maximal order of K
"""
function infinite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  get_attribute!(K, :infinite_maximal_order) do
    return _infinite_maximal_order(K)
  end
end

function _infinite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  R = localization(base_ring(K),degree)
  Oinf = integral_closure(R, K)
  return Oinf
end

################################################################################
#
#  Equality
#
################################################################################


Base.:(==)(D1::Divisor, D2::Divisor) = ideals(D1) == ideals(D2)
Base.isequal(D1::Divisor, D2::Divisor) = a == b

Base.hash(D::Divisor, h::UInt) = hash(ideals(D), h)

################################################################################
#
#  Divisor arithmetic
#
################################################################################

function Base.:+(D1::Divisor, D2::Divisor)
  D1_fin, D1_inf = ideals(D1)
  D2_fin, D2_inf = ideals(D2)
  Dnew = Divisor(D1_fin * D2_fin, D1_inf * D2_inf)

  if has_support(D1) && has_support(D2)
    P = union(keys(D1.finite_support), keys(D2.finite_support))
    fin_support = Dict{GenOrdIdl,Int}()
    for p in P
      p_val = valuation(D1, p) + valuation(D2, p)
      if p_val != 0
        fin_support[p] = p_val
      end
    end

    inf_support = Dict{GenOrdIdl,Int}()
    P_inf = union(keys(D1.infinite_support), keys(D2.infinite_support))
    for p in P_inf
      p_val = valuation(D1, p) + valuation(D2, p)
      if p_val != 0
        inf_support[p] = p_val
      end
    end

    Dnew.finite_support = fin_support
    Dnew.infinite_support = inf_support
  end

  return Dnew
end

function Base.:*(n::Int, D::Divisor)
  I, J = ideals(D)

  Dnew = Divisor(I^n, J^n)

  if has_support(D)
    fin_supp = finite_support(D)
    inf_supp = infinite_support(D)
    Dnew.finite_support = Dict((p, n*e) for (p, e) in fin_supp)
    Dnew.infinite_support = Dict((p, n*e) for (p, e) in inf_supp)
  end

  return Dnew
end

function gcd(D1::Divisor, D2::Divisor)
  D1_fin, D1_inf = ideals(D1)
  D2_fin, D2_inf = ideals(D2)
  Dnew = Divisor(D1_fin + D2_fin, D1_inf + D2_inf)

  if has_support(D1) && has_support(D2)
    P = union(keys(D1.finite_support), keys(D2.finite_support))
    fin_support = Dict{GenOrdIdl,Int}()
    for p in P
      p_val = min(valuation(D1, p), valuation(D2, p))
      if p_val != 0
        fin_support[p] = p_val
      end
    end

    inf_support = Dict{GenOrdIdl,Int}()
    P_inf = union(keys(D1.infinite_support), keys(D2.infinite_support))
    for p in P_inf
      p_val = min(valuation(D1, p), valuation(D2, p))
      if p_val != 0
        inf_support[p] = p_val
      end
    end

    Dnew.finite_support = fin_support
    Dnew.infinite_support = inf_support
  end

  return Dnew
end

Base.:*(D::Divisor, n::Int) = n * D

function -(D::Divisor)
  return (-1)*D
end

function Base.:(-)(D1::Divisor, D2::Divisor)
  return D1 + (-D2)
end

################################################################################
#
#  Support
#
################################################################################

has_support(D::Divisor) = isdefined(D, :finite_support) && isdefined(D, :infinite_support)

function assure_has_support(D::Divisor)
  if has_support(D)
    return nothing
  else
    D1, D2 = ideals(D)
    D1_fac = factor(D1)
    D2_fac = factor(D2)
    D.finite_support = D1_fac
    D.infinite_support = D2_fac
    return nothing
  end
end

@doc raw"""
    support(D::Divisor) -> Vector{(GenOrdIdl, Int)}

Return an array of ideals and multiplicities corresponding to the support of D.
"""
function support(D::Divisor)
  assure_has_support(D)
  return vcat(finite_support(D), infinite_support(D))
end

@doc raw"""
    valuation(D::Divisor, p::GenOrdIdl) -> Int

Return the multiplicity of D at the prime ideal p.
"""
function valuation(D::Divisor, p::GenOrdIdl)
@assert is_prime(p)

  #Might not always want to compute support for a simple valuation
  assure_has_support(D)

  O = order(p)
  if !isa(base_ring(O), KInftyRing)
    fin_supp = D.finite_support
    if haskey(fin_supp, p)
      return fin_supp[p]
    else
      return 0
    end
  else
    inf_supp = D.infinite_support
    if haskey(inf_supp, p)
      return inf_supp[p]
    else
      return 0
    end
  end
end

function finite_support(D::Divisor)
  assure_has_support(D)
  return collect(D.finite_support)
end

function infinite_support(D::Divisor)
  assure_has_support(D)
  return collect(D.infinite_support)
end

function Base.isless(D1::Divisor, D2::Divisor)
  all([valuation(D2, f) >= e  for (f, e) in support(D1)]) && D1 != D2
end

################################################################################
#
#  Related Divisors
#
################################################################################

@doc raw"""
    finite_divisor(D::Divisor) -> Divisor

Return the divisor whose support is equal to the support of D in the finite places
"""
function finite_divisor(D::Divisor)
  return divisor(D.finite_ideal)
end

@doc raw"""
    infinite_divisor(D::Divisor) -> Divisor

Return the divisor whose support is equal to the support of D in the infinite places
"""
function infinite_divisor(D::Divisor)
  return divisor(D.finite_ideal)
end


@doc raw"""
    finite_split(D::Divisor) -> Divisor, Divisor

Return the tuple consisitng of the 'finite_divisor' and the 'infinite' divisor.
"""
function finite_split(D::Divisor)
  return finite_divisor(D), infinite_divisor(D)
end

@doc raw"""
    zero_divisor(D::Divisor) -> Divisor

Return the divisor whose support consists exactly of all zeroes in the support of D.
"""
function zero_divisor(D::Divisor)
  supp_fin = finite_support(D)
  supp_inf = infinite_support(D)

  F = function_field(D)

  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)

  supp_fin = filter(t -> t[2]>0, supp_fin)
  supp_inf = filter(t -> t[2]>0, supp_inf)

  D1 = prod(map(t -> t[1]^t[2], supp_fin);init = Ofin(1)*Ofin)
  D2 = prod(map(t -> t[1]^t[2], supp_inf);init = Oinf(1)*Oinf)

  return divisor(D1, D2)
end

@doc raw"""
    pole_divisor(D::Divisor) -> Divisor

Return the divisor whose support consists exactly of all poles in the support of D.
"""
function pole_divisor(D::Divisor)
  supp_fin = finite_support(D)
  supp_inf = infinite_support(D)

  F = function_field(D)

  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)

  supp_fin = filter(t -> t[2]<0, supp_fin)
  supp_inf = filter(t -> t[2]<0, supp_inf)

  D1 = prod(map(t -> t[1]^t[2], supp_fin);init = Ofin(1)*Ofin)
  D2 = prod(map(t -> t[1]^t[2], supp_inf);init = Oinf(1)*Oinf)

  return divisor(D1, D2)
end

################################################################################
#
#  Properties
#
################################################################################

@doc raw"""
    degree(D::Divisor) -> Int

Return the degree of D.
"""
function degree(D::Divisor)
  L = support(D)
  return sum(degree(f)*e for (f,e) in L; init = zero(ZZ))
end

@doc raw"""
    is_effective(D::Divisor) -> Bool

Return true if D is an effective divisor.
"""
function is_effective(D::Divisor)
  return isempty(support(pole_divisor(D)))
end

@doc raw"""
    is_principal(D::Divisor) -> Bool

Return true if D is a principal divisor.
"""
function is_principal(D::Divisor)
  return degree(D) == 0 && dimension(D) == 1
end

@doc raw"""
    is_principal(D::Divisor) -> Bool

Return true if D is the trivial divisor.
"""
function is_zero(D::Divisor)
  D1, D2 = ideals(D)
  return is_one(D1) && is_one(D2)
end

################################################################################
#
#  Different
#
################################################################################
@doc raw"""
    different_divisor(F::FunctionField) -> Divisor

Return the different divisor of F.
"""
function different_divisor(F::AbstractAlgebra.Generic.FunctionField)
  return divisor(different(finite_maximal_order(F)), different(infinite_maximal_order(F)))
end

@doc raw"""
    complementary_divisor(D::Divisor) -> Divisor

Return the complementary divisor of D, which is D_F - D, where D_F is the different divisor of F.
"""
function complementary_divisor(D::Divisor)
  F = function_field(D)
  return different_divisor(F) - D
end

################################################################################
#
#  Canonical Divisor
#
################################################################################
@doc raw"""
    canonical_divisor(F::FunctionField) -> Divisor

Return the canonical divisor of F.
"""
function canonical_divisor(F::AbstractAlgebra.Generic.FunctionField)
  dx = differential(separating_element(F))
  return divisor(dx)
end

function separating_element(F::AbstractAlgebra.Generic.FunctionField)
  return F(gen(base_ring(F)))
end

@doc raw"""
    genus(F::FunctionField) -> Int

Return the genus of F.
"""
function genus(F::AbstractAlgebra.Generic.FunctionField)
  return length(basis_of_differentials(F))
end

################################################################################
#
#  Riemann-Roch computation
#
################################################################################
@doc raw"""
    riemann_roch_space(D::Divisor) -> Vector{FunFieldElem}

Return a basis of the Riemann-Roch space L(D).
"""
function riemann_roch_space(D::Divisor)
  I_fin, I_inf = ideals(D)
  J_fin = inv(I_fin)
  J_inf = inv(I_inf)

  F = function_field(D)
  x = gen(base_ring(F))
  n = degree(F)

  basis_gens = basis(J_fin)

  B_fin = matrix(map(coordinates, basis_gens))
  B_inf = matrix(map(coordinates, basis(J_inf)))

  M = solve(B_inf, B_fin; side = :left)
  d = lcm(vec(map(denominator,collect(M))))
  d_deg = degree(d)
  Mnew = change_base_ring(parent(d), d*M)

  T, U = weak_popov_with_transform(Mnew)

  basis_gens = change_base_ring(F, U) * basis(J_fin)

  RR_basis = []
  for i in (1:n)
    d_i = maximum(map(degree, T[i,1:n]))
    for j in (0: - d_i + d_deg)
      push!(RR_basis, x^(j) * basis_gens[i])
    end
  end
  return RR_basis
end

@doc raw"""
    dimension(D::Divisor) -> Int

Return the dimension l(D) of the Riemann-Roch space L(D).
"""
function dimension(D::Divisor)
  return length(riemann_roch_space(D))
end

@doc raw"""
    index_of_speciality(D::Divisor) -> Int

Return the index of speciality of D, which is the dimension Riemann-Roch space
L(K - D), where K is the canonical divisor of the function field of D.
"""
function index_of_speciality(D::Divisor)
  F = function_field(D)
  K = canonical_divisor(F)
  return length(riemann_roch_space(K - D))
end

