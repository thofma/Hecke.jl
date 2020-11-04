mutable struct MapClassGrp <: Map{GrpAbFinGen, NfOrdIdlSet, HeckeMap, MapClassGrp}
  header::MapHeader{GrpAbFinGen, NfOrdIdlSet}
  
  quo::Int
  princ_gens::Array{Tuple{FacElem{NfOrdIdl,NfOrdIdlSet}, FacElem{nf_elem, AnticNumberField}},1}
  small_gens::Vector{NfOrdIdl}
  function MapClassGrp()
    mp = new()
    mp.quo = -1
    return mp
  end
end


mutable struct SmallLLLRelationsCtx{T}
  A::NfOrdIdl
  b::Array{T, 1}
  bd::Int
  cnt::Int
  elt::T
  function SmallLLLRelationsCtx(a::T) where {T}
    n = new{T}()
    n.bd = 1
    n.cnt = 0
    return n
  end
end

mutable struct NormCtx_split <: NormCtx
  O::NfAbsOrd{AnticNumberField, nf_elem}
  lp::Array{Int, 1}  #the primes
  lR::Array{GaloisField, 1} #the local (finite field) splitting field
  nb::Int #bound on the number of bits the norm is allowed to have
  lC::Array{gfp_mat, 1} # for each p in lp, the conjugates of the basis of O
  mp::Array{gfp_mat, 1} # for each p in lp, the conjugates of the basis of O
  np::Array{gfp_mat, 1} # for each p in lp, the conjugates of the basis of O
  e::crt_env
  function NormCtx_split(O::NfAbsOrd, nb::Int)
    p = p_start
    NC = new()
    NC.O = O
    NC.nb = nb
    NC.lp = Array{Int, 1}()
    NC.lR = Array{GaloisField, 1}()
    NC.lC = Array{gfp_mat, 1}()
    NC.mp = Array{gfp_mat, 1}()
    NC.np = Array{gfp_mat, 1}()
    B = basis(O)
    n = degree(O)
    while (true)
      p = next_prime(p)
      lP = prime_decomposition(O, p)
      if length(lP) < degree(O)
        continue
      end
      push!(NC.lp, p)
      R = GF(p, cached = false)
      push!(NC.lR, R)
      push!(NC.mp, zero_matrix(R, 1, degree(O)))
      push!(NC.np, zero_matrix(R, 1, degree(O)))
      M = Array{Nemo.elem_type(R), 1}()
      for P = lP
        F, mF = ResidueFieldSmall(O, P[1])
        for x = B
          xp = mF(x)
          push!(M, R(coeff(xp, 0)))
        end
      end
      push!(NC.lC, matrix(R, n, n, M)')
      nb -= nbits(p)
      if nb <= 0
        NC.e = crt_env(fmpz[p for p = NC.lp])
        return NC
      end
    end
  end
end

mutable struct NormCtx_gen <: NormCtx
  nb::Int
  O::NfAbsOrd
  function NormCtx_gen(O::NfAbsOrd, nb::Int)
    NC = new()
    NC.nb = nb
    NC.O = O
    return NC
  end
end

mutable struct MapUnitGrp{T} <: Map{GrpAbFinGen, T, HeckeMap, MapUnitGrp}
  header::Hecke.MapHeader{GrpAbFinGen, T}

  # Only for non-maximal orders:
  OO_mod_F_mod_O_mod_F::GrpAbFinGenToAbsOrdQuoRingMultMap # a map from (OO/F*OO)^\times/(O/F)^\times to OO where OO is a maximal order and F the conductor

  function MapUnitGrp{T}() where {T}
    return new{T}()
  end
end


mutable struct MapSUnitModUnitGrpFacElem <: Map{GrpAbFinGen, FacElemMon{AnticNumberField}, HeckeMap, MapSUnitModUnitGrpFacElem}
  header::MapHeader{GrpAbFinGen, FacElemMon{AnticNumberField}}
  idl::Array{NfOrdIdl, 1}
  valuations::Vector{SRow{fmpz}}

  function MapSUnitModUnitGrpFacElem()
    return new()
  end
end

mutable struct MapSUnitGrpFacElem <: Map{GrpAbFinGen, FacElemMon{AnticNumberField}, HeckeMap, MapSUnitGrpFacElem}
  header::MapHeader{GrpAbFinGen, FacElemMon{AnticNumberField}}
  idl::Array{NfOrdIdl, 1}
  valuations::Vector{SRow{fmpz}}
  isquotientmap::Int

  function MapSUnitGrpFacElem()
    z = new()
    z.isquotientmap = -1
    return z
  end
end

mutable struct MapSUnitGrp <: Map{GrpAbFinGen, AnticNumberField, HeckeMap, MapSUnitGrp}
  header::MapHeader{GrpAbFinGen, AnticNumberField}
  idl::Array{NfOrdIdl, 1}

  function MapSUnitGrp()
    return new()
  end
end

