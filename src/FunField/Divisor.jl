using Hecke

export Divisor

export finite_maximal_order, infinite_maximal_order, function_field, field_of_fractions, divisor, ideals, riemann_roch_space, support, zero_divisor, pole_divisor, finite_support, infinite_support, canonical_divisor, different_divisor, basis_of_differentials, degree, dimension, index_of_speciality, is_effective

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

function divisor(I::GenOrdFracIdl, J::GenOrdFracIdl)
  return Divisor(I, J)
end

function divisor(I::GenOrdIdl, J::GenOrdIdl)
  return Divisor(GenOrdFracIdl(I), GenOrdFracIdl(J))
end

function divisor(I::GenOrdIdl)
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


function divisor(f::Generic.FunctionFieldElem)
  F = parent(f)
 
  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)
 
  f_num, f_denom = integral_split(f, Ofin)
  g_num, g_denom = integral_split(f, Oinf)  
  
  return divisor(colon(ideal(Ofin, f_num), ideal(Ofin, f_denom)), colon(ideal(Oinf, g_num), ideal(Oinf, g_denom)))
end

function zero_divisor(f::Generic.FunctionFieldElem)
  F = parent(f)
 
  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)
 
  f_num, f_denom = integral_split(f, Ofin)
  g_num, g_denom = integral_split(f, Oinf)  
  
  return divisor(ideal(Ofin, f_num), ideal(Oinf, g_num))
end

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


function function_field(D::Divisor)
  return D.function_field
end

function ideals(D)
  return D.finite_ideal, D.infinite_ideal
end

function field_of_fractions(O::GenOrd)
  return O.F
end

function function_field(O::GenOrd)
  return O.F
end

function constant_field(K::AbstractAlgebra.Generic.FunctionField)
  return base_ring(base_ring(K))
end

function finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  get_attribute!(K, :finite_maximal_order) do
    return _finite_maximal_order(K)
  end
end

function _finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  kx = parent(numerator(gen(base_ring(K))))
  return integral_closure(kx, K)
end

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

function Base.:-(D1::Divisor, D2::Divisor)
  D1_fin, D1_inf = ideals(D1)
  D2_fin, D2_inf = ideals(D2)
  return Divisor(D1_fin // D2_fin, D1_inf // D2_inf)
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

Base.:*(D::Divisor, n::Int) = n * D

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

function support(D::Divisor)
  assure_has_support(D)
  return vcat(finite_support(D), infinite_support(D))
end

function valuation(D::Divisor, p::GenOrdIdl)
  #TODO: Check p is prime
  
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


function degree(D::Divisor)
  L = support(D)
  return sum(e for (f,e) in L)
end

function is_effective(D::Divisor)
  return isempty(support(pole_divisor(D)))
end

################################################################################
#
#  Different
#
################################################################################

function different_divisor(F::AbstractAlgebra.Generic.FunctionField)
  return divisor(different(finite_maximal_order(F)), different(infinite_maximal_order(F)))
end

################################################################################
#
#  Canonical Divisor
#
################################################################################

function canonical_divisor(F::AbstractAlgebra.Generic.FunctionField)
  x = gen(base_ring(F))
  return - 2*pole_divisor(F(x)) + different_divisor(F)
end

function basis_of_differentials(F::AbstractAlgebra.Generic.FunctionField)
  return riemann_roch_space(canonical_divisor(F))
end

################################################################################
#
#  Riemann-Roch computation
#
################################################################################

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
  
  M = solve_left(B_inf, B_fin)
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

function dimension(D::Divisor)
  return length(riemann_roch_space(D))
end

function index_of_speciality(D::Divisor)
  F = function_field(D)
  K = canonical_divisor(F)
  return length(riemann_roch_space(K - D))
end

