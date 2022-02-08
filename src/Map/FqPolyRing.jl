# This function constructs the field F_q \cong parent(h)/h and a homomorphism
# from parent(h) to F_q.
function field_extension(h::Union{ fq_nmod_poly, fq_poly })
  m = FqPolyRingToFqMor(h)
  return codomain(m), m
end

mutable struct FqPolyRingToFqMor{S, T, PolyType, MatType} <: Map{S, T, HeckeMap, FqPolyRingToFqMor}
  header::MapHeader{S, T}
  h::PolyType
  mat::MatType
  mat_inv::MatType

  function FqPolyRingToFqMor{S, T, PolyType, MatType}(h::PolyType) where {
           S, T, PolyType, MatType
           #S <: Union{ FqNmodPolyRing, FqPolyRing },
           #T <: Union{ FqNmodFiniteField, FqFiniteField },
           #PolyType <: Union{ fq_nmod_poly, fq_poly },
           #MatType <: Union{ gfp_mat, Generic.MatSpaceElem{Generic.ResF{fmpz}} }
    }

    z = new{S, T, PolyType, MatType}()
    z.h = h

    isnmod = (T == FqNmodFiniteField)

    Fq = base_ring(h)
    p = characteristic(Fq)
    if isnmod
      Fp = GF(Int(p); cached = false)
    else
      Fp = GF(p; cached = false)
    end
    Fpx = PolynomialRing(Fp, "x", cached = false)[1]
    g = Fpx()
    if isnmod
      pt = ccall((:fq_nmod_ctx_modulus, libflint), Ptr{nmod_poly}, (Ref{FqNmodFiniteField}, ), Fq)
      ccall((:nmod_poly_set, libflint), Nothing, (Ref{gfp_poly}, Ptr{nmod_poly}), g, pt)
    else
      pt = ccall((:fq_ctx_modulus, libflint), Ptr{fmpz_mod_poly}, (Ref{FqFiniteField}, ), Fq)
      ccall((:fmpz_mod_poly_set, libflint), Nothing, (Ref{gfp_fmpz_poly}, Ptr{fmpz_mod_poly}, Ref{fmpz_mod_ctx_struct}), g, pt, g.parent.base_ring.ninv)
    end
    n = degree(Fq)
    @assert n == degree(g)
    m = degree(h)
    if isnmod
      Fqm = FqNmodFiniteField(p, n*m, :$, false)
    else
      Fqm = FqFiniteField(p, n*m, :$, false)
    end
    Fqmy, y = PolynomialRing(Fqm, "y", cached = false)
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
        ccall((:fq_nmod_set, libflint), Nothing, (Ref{fq_nmod}, Ref{gfp_poly}, Ref{FqNmodFiniteField}), x, t, Fqm)
      else
        ccall((:fq_set, libflint), Nothing, (Ref{fq}, Ref{gfp_fmpz_poly}, Ref{FqFiniteField}), x, t, Fqm)
      end
      return x
    end

    function _preimage(x::Union{ fq_nmod, fq })
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
          ccall((:fq_nmod_set, libflint), Nothing, (Ref{fq_nmod}, Ref{gfp_poly}, Ref{FqNmodFiniteField}), t, tt, Fq)
        else
          ccall((:fq_set, libflint), Nothing, (Ref{fq}, Ref{gfp_fmpz_poly}, Ref{FqFiniteField}), t, tt, Fq)
        end
        setcoeff!(f, j, t)
      end
      return f
    end
    z.header = MapHeader{S, T}(parent(h), Fqm, _image, _preimage)
    return z
  end
end

if Nemo.version() > v"0.28.0"
  function FqPolyRingToFqMor(h::fq_poly)
    return FqPolyRingToFqMor{FqPolyRing, FqFiniteField, fq_poly, gfp_fmpz_mat}(h)
  end
end

function FqPolyRingToFqMor(h::fq_nmod_poly)
  return FqPolyRingToFqMor{FqNmodPolyRing, FqNmodFiniteField, fq_nmod_poly, gfp_mat}(h)
end
