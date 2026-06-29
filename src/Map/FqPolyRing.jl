# This function constructs the field F_q \cong parent(h)/h and a homomorphism
# from parent(h) to F_q.
function field_extension(h::Union{ fqPolyRepPolyRingElem, FqPolyRepPolyRingElem })
  m = FqPolyRingToFqMor(h)
  return codomain(m), m
end

field_extension(h::FqPolyRingElem) = Nemo._residue_field(h)

mutable struct FqPolyRingToFqMor{S, T, PolyType, MatType} <: Map{S, T, HeckeMap, FqPolyRingToFqMor}
  header::MapHeader{S, T}
  h::PolyType
  mat::MatType
  mat_inv::MatType

  function FqPolyRingToFqMor{S, T, PolyType, MatType}(h::PolyType) where {
           S, T, PolyType, MatType
           #S <: Union{ fqPolyRepPolyRing, FqPolyRepPolyRing },
           #T <: Union{ fqPolyRepField, FqPolyRepField },
           #PolyType <: Union{ fqPolyRepPolyRingElem, FqPolyRepPolyRingElem },
           #MatType <: Union{ fpMatrix, Generic.MatSpaceElem{EuclideanRingResidueFieldElem{ZZRingElem}} }
    }

    z = new{S, T, PolyType, MatType}()
    z.h = h

    isnmod = (T == fqPolyRepField)

    Fq = base_ring(h)
    p = characteristic(Fq)
    if isnmod
      Fp = Native.GF(Int(p); cached = false)
    else
      Fp = Native.GF(p; cached = false)
    end
    Fpx = polynomial_ring(Fp, "x", cached = false)[1]
    g = Fpx()
    if isnmod
      pt = ccall((:fq_nmod_ctx_modulus, libflint), Ptr{zzModPolyRingElem}, (Ref{fqPolyRepField}, ), Fq)
      ccall((:nmod_poly_set, libflint), Nothing, (Ref{fpPolyRingElem}, Ptr{zzModPolyRingElem}), g, pt)
    else
      pt = ccall((:fq_ctx_modulus, libflint), Ptr{ZZModPolyRingElem}, (Ref{FqPolyRepField}, ), Fq)
      ccall((:fmpz_mod_poly_set, libflint), Nothing, (Ref{FpPolyRingElem}, Ptr{ZZModPolyRingElem}, Ref{fmpz_mod_ctx_struct}), g, pt, g.parent.base_ring.ninv)
    end
    n = degree(Fq)
    @assert n == degree(g)
    m = degree(h)
    if isnmod
      Fqm = fqPolyRepField(p, n*m, :$, false)
    else
      Fqm = FqPolyRepField(p, n*m, :$, false)
    end
    Fqmy, y = polynomial_ring(Fqm, "y", cached = false)
    gy = Fqmy([ Fqm(coeff(g, i)) for i = 0:degree(g) ])
    a = roots(gy)[1]
    aa = Vector{typeof(a)}()
    push!(aa, Fqm(1))
    for i = 2:n
      push!(aa, aa[i - 1]*a)
    end
    @assert parent(a) == Fqm
    hy = Fqmy()
    for i = 0:m
      c = coeff(h, i)
      d = Fqm()
      for j = 0:n - 1
        d += coeff(c, j)*aa[j + 1]
      end
      setcoeff!(hy, i, d)
    end

    b = roots(hy)[1]
    bb = Vector{typeof(b)}()
    push!(bb, Fqm(1))
    for i = 2:m
      push!(bb, bb[i - 1]*b)
    end
    @assert parent(b) == Fqm

    # We have now a second basis for Fqm given by a^ib^j for 0 \leq i\leq n - 1, 0 \leq j\leq m - 1
    M = zero_matrix(Fp, n*m, n*m)
    c = Fqm()
    for i = 0:n - 1
      for j = 0:m - 1
        c = mul!(c, aa[i + 1], bb[j + 1])
        for k = 0:n*m - 1
          M[k + 1, i + j*n + 1] = Fp(coeff(c, k))
        end
      end
    end
    z.mat = M
    invM = inv(M)
    z.mat_inv = invM

    function _image(f::PolyType)
      f = mod(f, h)
      x_mat = zero_matrix(Fp, n*m, 1)
      for j = 0:m - 1
        t = coeff(f, j)
        for i = 0:n - 1
          x_mat[i + j*n + 1, 1] = Fp(coeff(t, i))
        end
      end
      x_mat = M*x_mat
      t = parent(g)([ x_mat[k, 1] for k = 1:n*m ])
      x = Fqm()
      if isnmod
        ccall((:fq_nmod_set, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}), x, t, Fqm)
      else
        ccall((:fq_set, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}), x, t, Fqm)
      end
      return x
    end

    function _preimage(x::Union{ fqPolyRepFieldElem, FqPolyRepFieldElem })
      @assert typeof(x) == elem_type(T)
      x_mat = zero_matrix(Fp, n*m, 1)
      for k = 0:n*m - 1
        x_mat[k + 1, 1] = Fp(coeff(x, k))
      end
      x_mat = invM*x_mat
      f = parent(h)()
      t = Fqm()
      for j = 0:m - 1
        tt = parent(g)([ x_mat[i + n*j + 1, 1] for i = 0:n - 1 ])
        if isnmod
          ccall((:fq_nmod_set, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}), t, tt, Fq)
        else
          ccall((:fq_set, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}), t, tt, Fq)
        end
        setcoeff!(f, j, t)
      end
      return f
    end
    z.header = MapHeader{S, T}(parent(h), Fqm, _image, _preimage)
    return z
  end

  function FqPolyRingToFqMor{S, T, PolyType, MatType}(F::T, h::FqPolyRingElem) where {
           S, T, PolyType, MatType
           #S <: Union{ fqPolyRepPolyRing, FqPolyRepPolyRing },
           #T <: Union{ fqPolyRepField, FqPolyRepField },
           #PolyType <: Union{ fqPolyRepPolyRingElem, FqPolyRepPolyRingElem },
           #MatType <: Union{ fpMatrix, Generic.MatSpaceElem{EuclideanRingResidueFieldElem{ZZRingElem}} }
    }
    z = new{S, T, PolyType, MatType}()
    z.h = h

    function _image(f::FqPolyRingElem)
      return F.forwardmap(f)
    end

    function _preimage(f::FqFieldElem)
      return F.backwardmap(f)
    end
    z.header = MapHeader{S, T}(parent(h), F, _image, _preimage)
    return z
  end
end

function FqPolyRingToFqMor(h::FqPolyRepPolyRingElem)
  return FqPolyRingToFqMor{FqPolyRepPolyRing, FqPolyRepField, FqPolyRepPolyRingElem, FpMatrix}(h)
end

function FqPolyRingToFqMor(h::fqPolyRepPolyRingElem)
  return FqPolyRingToFqMor{fqPolyRepPolyRing, fqPolyRepField, fqPolyRepPolyRingElem, fpMatrix}(h)
end
