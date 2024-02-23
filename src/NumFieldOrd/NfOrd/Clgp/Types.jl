mutable struct MapClassGrp <: Map{FinGenAbGroup, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}, HeckeMap, MapClassGrp}
  header::MapHeader{FinGenAbGroup, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}

  quo::Int
  princ_gens::Vector{Tuple{FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}}
  small_gens::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}
  function MapClassGrp()
    mp = new()
    mp.quo = -1
    return mp
  end
end


mutable struct SmallLLLRelationsCtx{T}
  A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  b::Vector{T}
  bd::Int
  cnt::Int
  elt::T
  function SmallLLLRelationsCtx(a::T) where {T}
    n = new{T}()
    n.bd = 1
    n.cnt = 0
    return n
  end

  function SmallLLLRelationsCtx(::Type{T}) where T
    n = new{T}()
    n.bd = 1
    n.cnt = 0
    return n
  end
end

mutable struct NormCtx_split <: NormCtx
  O::AbsSimpleNumFieldOrder
  lp::Vector{Int}  #the primes
  lR::Vector{fpField} #the local (finite field) splitting field
  nb::Int #bound on the number of bits the norm is allowed to have
  lC::Vector{fpMatrix} # for each p in lp, the conjugates of the basis of O
  mp::Vector{fpMatrix} # temp. variable
  np::Vector{fpMatrix} # temp. variable
  #= used in 
    NumFieldOrder/AbsSimpleNumFieldOrder/Clgp/Rel_LLL.jl
    a coordinate vector of an order element is mapped mod p into mp
    multiplied by lC into np
  =#
  e::crt_env
  function NormCtx_split(O::AbsNumFieldOrder, nb::Int)
    p = p_start
    NC = new()
    NC.O = O
    NC.nb = nb
    NC.lp = Vector{Int}()
    NC.lR = Vector{fpField}()
    NC.lC = Vector{fpMatrix}()
    NC.mp = Vector{fpMatrix}()
    NC.np = Vector{fpMatrix}()
    B = basis(O)
    n = degree(O)
    while (true)
      p = next_prime(p)
      lP = prime_decomposition(O, p)
      if length(lP) < degree(O)
        continue
      end
      push!(NC.lp, p)
      R = Native.GF(p, cached = false)
      push!(NC.lR, R)
      push!(NC.mp, zero_matrix(R, 1, degree(O)))
      push!(NC.np, zero_matrix(R, 1, degree(O)))
      M = Vector{Nemo.elem_type(R)}()
      for P = lP
        F, mF = ResidueFieldSmall(O, P[1])
        for x = B
          xp = mF(x)
          push!(M, R(coeff(xp, 0)))
        end
      end
      push!(NC.lC, transpose(matrix(R, n, n, M)))
      nb -= nbits(p)
      if nb <= 0
        NC.e = crt_env(ZZRingElem[p for p = NC.lp])
        return NC
      end
    end
  end
end

mutable struct NormCtx_simple <: NormCtx
  nb::Int
  O::AbsNumFieldOrder

  function NormCtx_simple(O::AbsNumFieldOrder, nb::Int)
    NC = new()
    NC.nb = nb
    NC.O = O
    return NC
  end
end
 
mutable struct NormCtx_gen <: NormCtx
  nb::Int
  O::AbsNumFieldOrder
  lp::Vector{Int} #the primes
  basis::Vector{fpMatrix} # for each prime, the order basis (coefficients)
                          # as polynomial
  mp::Vector{fpMatrix} # temp. variable
  np::Vector{fpMatrix} # temp. variable

  fp::Vector{fpPolyRingElem}
  gp::Vector{fpPolyRingElem}

  e::crt_env
  function NormCtx_gen(O::AbsNumFieldOrder, nb::Int)
    NC = new()
    NC.nb = nb
    NC.O = O
    p = p_start
    NC.lp = Int[]

    NC.basis = Vector{fpMatrix}[]
    NC.mp = Vector{fpMatrix}[]
    NC.np = Vector{fpMatrix}[]

    NC.fp = Vector{fpPolyRingElem}[]
    NC.gp = Vector{fpPolyRingElem}[]
    bas = basis(O, nf(O))
    f = defining_polynomial(nf(O))
    while true
      p = next_prime(p)
      push!(NC.lp, p)
      k = Native.GF(p, cached = false)
      kx, x = polynomial_ring(k, cached = false)
      b = zero_matrix(k, degree(O), degree(O))
      for i=1:degree(O)
        g = kx(bas[i])
        for j=1:degree(g)+1
          b[i, j] = coeff(g, j-1)
        end
      end
      push!(NC.basis, b)
      push!(NC.mp, zero_matrix(k, 1, degree(O)))
      push!(NC.np, zero_matrix(k, 1, degree(O)))

      push!(NC.fp, kx(f))
      push!(NC.gp, kx())
      nb -= nbits(p)
      if nb < 0
        NC.e = crt_env(ZZRingElem[p for p = NC.lp])
        return NC
      end
    end
  end
end

mutable struct MapUnitGrp{T} <: Map{FinGenAbGroup, T, HeckeMap, MapUnitGrp}
  header::Hecke.MapHeader{FinGenAbGroup, T}

  # Only for non-maximal orders:
  OO_mod_F_mod_O_mod_F::GrpAbFinGenToAbsOrdQuoRingMultMap # a map from (OO/F*OO)^\times/(O/F)^\times to OO where OO is a maximal order and F the conductor

  function MapUnitGrp{T}() where {T}
    return new{T}()
  end
end


mutable struct MapSUnitModUnitGrpFacElem <: Map{FinGenAbGroup, FacElemMon{AbsSimpleNumField}, HeckeMap, MapSUnitModUnitGrpFacElem}
  header::MapHeader{FinGenAbGroup, FacElemMon{AbsSimpleNumField}}
  idl::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}
  valuations::Vector{SRow{ZZRingElem}}

  function MapSUnitModUnitGrpFacElem()
    return new()
  end
end

mutable struct MapSUnitGrpFacElem <: Map{FinGenAbGroup, FacElemMon{AbsSimpleNumField}, HeckeMap, MapSUnitGrpFacElem}
  header::MapHeader{FinGenAbGroup, FacElemMon{AbsSimpleNumField}}
  idl::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}
  valuations::Vector{SRow{ZZRingElem}}
  isquotientmap::Int

  function MapSUnitGrpFacElem()
    z = new()
    z.isquotientmap = -1
    return z
  end
end

mutable struct MapSUnitGrp <: Map{FinGenAbGroup, AbsSimpleNumField, HeckeMap, MapSUnitGrp}
  header::MapHeader{FinGenAbGroup, AbsSimpleNumField}
  idl::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}

  function MapSUnitGrp()
    return new()
  end
end

