#TODO: move to Divisor.jl
mutable struct RiemannRochCtx
 RR_basis::Vector{Generic.FunctionFieldElem} #Fq-basis
 basis_gens::Generic.MatSpaceElem #k(x)-generators via coordinates in power basis
 dlist::Vector{Int}
 iso::Generic.MapWithSection
 gens #Fp-basis
 function RiemannRochCtx(RR_basis, basis_gens, dlist)
    return new(RR_basis, basis_gens, dlist)
  end
end

function riemann_roch_space_with_ctx(D::Divisor)
  I_fin, I_inf = ideals(D)
  return _riemann_roch_space_with_ctx(inv(I_fin), inv(I_inf), function_field(D))
end


function _riemann_roch_space_with_ctx(J_fin, J_inf, F)
  x = gen(base_ring(F))
  n = degree(F)

  B_fin = _coordinate_matrix(J_fin)
  B_inf = _coordinate_matrix(J_inf)
  dM, d_deg = _riemann_roch_common_setup(B_fin, B_inf)

  # weak Popov reduction of dM (no denominators)
  T, U = weak_popov_with_transform(dM)

  # v_i in Hess paper
  basis_gens = change_base_ring(base_ring(B_fin), U) * B_fin

  RR_basis = elem_type(F)[]
  dlist = Int[]
  for i in 1:n
    d_i = maximum(degree(T[i, k]) for k in 1:n)
    push!(dlist, d_deg - d_i)
    g = F(vec(collect(basis_gens[i, :])))
    for _ in 0:(d_deg - d_i)
      push!(RR_basis, g)
      g = x*g # this is x^j * basis_gens[i] for j = 0 .. d_deg - d_i
    end
  end

  ctx = RiemannRochCtx(RR_basis, basis_gens, dlist)
  
  #disclog
  Uinv = inv(U) #basis(J_fin) = Uinv * basis_gens
  M = inv(basis_matrix(J_fin)) #basis(F) = M * basis(J_fin)
  coord_basis_gens = a -> coordinates(a) * M * Uinv

  Fq = constant_field(F)
  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i)
  p = characteristic(Fq)
  l = degree(Fq) #q = p^l

  r = 0
  for i in 1:length(dlist)
    if dlist[i] >=0
      r += l*(dlist[i] + 1)
    end
  end

  gens = [c*g for g in RR_basis for c in Fp_basis]

  #=
  #abelian group
  rels = diagonal_matrix(p, r)
  G = abelian_group(rels)
  G.rels = rels

  function disclog_RR(a, dlist, G)
    y = coord_basis_gens(a)
    v = zeros(ZZ, ngens(G))
    idx = 1
    for i in 1:length(y)
      lambda = numerator(y[i])
      for j in 0:dlist[i]
        c = coeff(lambda, j)
        if iszero(c)
          idx += l
          continue
        end
        for k in 0:l-1
          v[idx] = lift(ZZ, coeff(c, k))
          idx += 1
        end
      end
    end
    return G(v)
  end

  function G_to_RR(v, gens)
    z = 0
    len = length(v.coeff)
    @assert len == length(gens)
    for i in 1:len
      z += v[i]*gens[i]
    end
    return z
  end
  =#

  #Fp-vectorspace
  Fp = base_field(Fq)
  V = vector_space(Fp, length(gens))

  #RR space -> Fp-vectorspace
  function disclog_RR(a, dlist, V)
    Fp = base_ring(V)
    y = coord_basis_gens(a)
    v = zeros(Fp, ngens(V))
    idx = 1
    for i in 1:length(y)
      lambda = numerator(y[i])
      for j in 0:dlist[i]
        c = coeff(lambda, j)
        if iszero(c)
          idx += l
          continue
        end
        for k in 0:l-1
          v[idx] = coeff(c, k)
          idx += 1
        end
      end
    end
    return V(v)
  end

  #Fp-vectorspace
  function V_to_RR(v, gens)
    z = 0
    len = length(v.v)
    @assert len == length(gens)
    for i in 1:len
      z += v[i]*gens[i]
    end
    return z
  end
  
  ctx.gens = gens
  ctx.iso = map_with_preimage_from_func(v->V_to_RR(v, gens), a -> disclog_RR(a, dlist, V), V, F)
  return ctx
end


################################################################################
#
#  Tests
#
################################################################################

function test_RR_iso(ctx)
  V = ctx.iso.map.domain
  for v in collect(V)
    #@show(v)
    a = ctx.iso(v)
    @assert ctx.iso.section(a) == v
  end
end