## `ZZRingElem` to GAP integer
function _julia_to_gap(obj::ZZRingElem)
  Nemo._fmpz_is_small(obj) && return GAP.julia_to_gap(Int(obj))
  GC.@preserve obj begin
    x = Nemo._as_bigint(obj)
    return ccall((:MakeObjInt, GAP.libgap), GAP.GapObj, (Ptr{UInt64}, Cint), x.d, x.size)
  end
end

# Basically the same as the usual image function but without a type check since
# we don't have elem_type(C) in this case
function _image(M::MapFromFunc{D, C}, a) where {D, C <: GAP.GapObj}
  if isdefined(M, :header)
    if isdefined(M.header, :image)
      return M.header.image(a)
    else
      error("No image function known")
    end
  else
    return M(a)
  end
end

function _preimage(M::MapFromFunc{D, C}, a) where {D, C <: GAP.GapObj}
  if isdefined(M, :header)
    if isdefined(M.header, :preimage)
      return M.header.preimage(a)
    else
      error("No preimage function known")
    end
  else
    return M\(a)
  end
end

################################################################################
#
#  Ring isomorphism
#
################################################################################

# computes the isomorphism between the Oscar field F and the corresponding GAP field
function _ring_iso_oscar_gap(F::T) where T <: Union{Nemo.fpField, Nemo.FpField}
   p = characteristic(F)
   G = GAP.Globals.GF(_julia_to_gap(p))
   e = GAP.Globals.One(G)

   f(x::Union{Nemo.fpFieldElem, Nemo.FpFieldElem}) = _julia_to_gap(lift(x))*e
   finv(x) = F(ZZRingElem(GAP.Globals.IntFFE(x)))

   return MapFromFunc(F, G, f, finv)
end

function _ring_iso_oscar_gap(F::T) where T <: Union{Nemo.fqPolyRepField, Nemo.FqPolyRepField}
   p = characteristic(F)
   d = degree(F)
   p_gap = GAP.Obj(p)
   Fp_gap = GAP.Globals.GF(p_gap) # the prime field in GAP
   e = GAP.Globals.One(Fp_gap)

   # prime fields are easy and efficient to deal with, handle them separately
   if d == 1
      f1(x::Union{Nemo.fqPolyRepFieldElem, Nemo.FqPolyRepFieldElem}) = GAP.Obj(coeff(x, 0))*e
      finv1(x) = F(ZZRingElem(GAP.Globals.IntFFE(x)))
      return MapFromFunc(F, Fp_gap, f1, finv1)
   end

   # non-prime fields: convert the defining polynomial to GAP...
   L = [ GAP.Obj(lift(coeff(defining_polynomial(F), i)))*e for i in 0:d - 1 ]
   push!(L, e)
   L_gap = GAP.GapObj(L)
   f_gap = GAP.Globals.UnivariatePolynomial(Fp_gap, L_gap)

   # ... and compute a GAP field G defined via this polynomial
   # (If the given polynomial is a Conway polynomial then we may call
   # GAP's `GF(p, d)`, which avoids GAP's `AlgebraicExtension`.)
   if GAP.Globals.IsCheapConwayPolynomial(p_gap, d) &&
      f_gap == GAP.Globals.ConwayPolynomial(p_gap, d)
      G = GAP.Globals.GF(p_gap, d)
   else
      G = GAP.Globals.GF(Fp_gap, f_gap)
   end

   # compute matching bases of both fields
   if GAP.Globals.IsAlgebraicExtension(G)
#FIXME:
# As soon as the problem from https://github.com/gap-system/gap/issues/4694
# is fixed, go back to `Basis_G = GAP.Globals.Basis(G)` also in this case.
# Note that the above `GF` call delegates to `FieldExtension`,
# and we want a basis in the filter `IsCanonicalBasisAlgebraicExtension`.
      Basis_G = GAP.Globals.Objectify(GAP.Globals.NewType(
                GAP.Globals.FamilyObj(G),
                GAP.Globals.IsCanonicalBasisAlgebraicExtension),
                GAP.NewPrecord(0))
      GAP.Globals.SetUnderlyingLeftModule(Basis_G, G)
   else
      Basis_G = GAP.Globals.Basis(G)
   end
   Basis_F = Vector{elem_type(F)}(undef, d)
   Basis_F[1] = F(1)
   for i = 2:d
      Basis_F[i] = Basis_F[i - 1]*gen(F)
   end

   function f(x::Union{fqPolyRepFieldElem, FqPolyRepFieldElem})
      v = [ GAP.Obj(coeff(x, i)) for i in 0:d - 1 ]
      return sum([ v[i]*Basis_G[i] for i in 1:d ])
   end

   # For "small" primes x should be an FFE, but for bigger ones it's GAP_jll.Mptr (?)
   function finv(x)
      v = GAP.Globals.Coefficients(Basis_G, x)
      v_int = [ ZZRingElem(GAP.Globals.IntFFE(v[i])) for i = 1:length(v) ]
      return sum([ v_int[i]*Basis_F[i] for i = 1:d ])
   end

   return MapFromFunc(F, G, f, finv)
end

function __to_gap(h, x::Vector)
  return GAP.Globals.GModuleByMats(GAP.julia_to_gap([GAP.julia_to_gap(map(x -> _image(h, x), Matrix(y))) for y in x]), codomain(h))
end

function __gap_matrix_to_julia(h, g)
  return matrix(domain(h), [map(y -> _preimage(h, y), gg) for gg in GAP.gap_to_julia(g)])
end

function __to_julia(h, C)
  return [ matrix(domain(h), [map(y -> _preimage(h, y), gg) for gg in GAP.gap_to_julia(g)]) for g in GAP.Globals.MTX.Generators(C)]
end

function Hecke.stub_composition_factors(x::Vector{T}) where {T <: MatElem}
  F = base_ring(x[1])
  h = _ring_iso_oscar_gap(F)
  V = __to_gap(h, x)
  Vcf = GAP.Globals.MTX.CompositionFactors(V)
  res = Vector{T}[]
  for C in Vcf
    push!(res, _to_julia(h, C))
  end
  return res
end

function Hecke.stub_basis_hom_space(x::Vector{T}, y::Vector{T}) where {T <: MatElem}
  F = base_ring(x[1])
  h = _ring_iso_oscar_gap(F)
  @assert base_ring(x[1]) == base_ring(y[1])
  @assert length(x) == length(y)
  hb = GAP.Globals.MTX.BasisModuleHomomorphisms(__to_gap(h, x), __to_gap(h, y))
  hbb = [__gap_matrix_to_julia(h, g) for g in GAP.gap_to_julia(hb)]
  return hbb
end
