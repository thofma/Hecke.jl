# This function constructs the field F_q \cong parent(h)/h and a homomorphism
# from parent(h) to F_q.
function field_extension(h::fq_poly)
  m = FqPolyRingToFqMor(h)
  return codomain(m), m
end

mutable struct FqPolyRingToFqMor <: Map{FqPolyRing, FqFiniteField, HeckeMap, FqPolyRingToFqMor}
  header::MapHeader{FqPolyRing, FqFiniteField}
  h::fq_poly
  mat::Generic.Mat{Generic.Res{fmpz}}
  mat_inv::Generic.Mat{Generic.Res{fmpz}}

  function FqPolyRingToFqMor(h::fq_poly)
    z = new()
    z.h = h

    Fq = base_ring(h)
    p = characteristic(Fq)
    Fp = ResidueRing(FlintZZ, p)
    Fpx = Fp["x"][1]
    g = Fpx()
    pt = ccall((:fq_ctx_modulus, :libflint), Ptr{Nemo.fmpz_mod_poly}, (Ref{Nemo.FqFiniteField}, ), Fq)
    ccall((:fmpz_mod_poly_set, :libflint), Nothing, (Ref{Nemo.fmpz_mod_poly}, Ptr{Nemo.fmpz_mod_poly}), g, pt)
    n = degree(Fq)
    @assert n == degree(g)
    m = degree(h)
    Fqm = FqFiniteField(p, n*m, :$)
    Fqmy, y = Fqm["y"]
    gy = Fqmy([ Fqm(fmpz(coeff(g, i))) for i = 0:degree(g) ])
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
    invM, t = inv(M)
    invM = inv(t)*invM
    z.mat_inv = invM

    function _image(f::fq_poly)
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
      ccall((:fq_set, :libflint), Nothing, (Ref{fq}, Ref{fmpz_mod_poly}, Ref{FqFiniteField}), x, t, Fqm)
      return x
    end

    function _preimage(x::fq)
      x_mat = zero_matrix(Fp, n*m, 1)
      for k = 0:n*m - 1
        x_mat[k + 1, 1] = Fp(coeff(x, k))
      end
      x_mat = invM*x_mat
      f = parent(h)()
      t = Fqm()
      for j = 0:m - 1
        tt = parent(g)([ x_mat[i + n*j + 1, 1] for i = 0:n - 1 ])
        ccall((:fq_set, :libflint), Nothing, (Ref{fq}, Ref{fmpz_mod_poly}, Ref{FqFiniteField}), t, tt, Fq)
        setcoeff!(f, j, t)
      end
      return f
    end
    z.header = MapHeader{FqPolyRing, FqFiniteField}(parent(h), Fqm, _image, _preimage)
    return z
  end
end
