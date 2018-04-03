mutable struct NfRelOrdToFqMor{T, S} <: Map{NfRelOrd{T, S}, FqFiniteField}
  header::MapHeader
  poly_of_the_field::fq_poly
  P::NfRelOrdIdl{T, S}

  function NfRelOrdToFqMor{T, S}(O::NfRelOrd{T, S}, P::NfRelOrdIdl{T, S}) where {T, S}
    z = new{T, S}()
    z.P = P
    p = minimum(P, Val{false})
    F, mF = ResidueField(order(p), p)
    mmF = extend(mF, nf(order(p)))
    Fx = F["x"][1]
    if isindex_divisor(O, p)
      A, OtoA = AlgAss(O, P, p)
      AtoO = inv(OtoA)
      x = rand(A)
      h = minpoly(x)
      while degree(h) != dim(A)
        x = rand(A)
        h = minpoly(x)
      end
      # F and base_ring(h) are the same as in "==" but not as in "==="
      hh = Fx()
      ccall((:fq_poly_set, :libflint), Void, (Ptr{fq_poly}, Ptr{fq_poly}, Ptr{FqFiniteField}), &hh, &h, &F)
      z.poly_of_the_field = hh
      FF, mFF = field_extension(hh)

      #= M1 = zero_matrix(base_ring(nf(O)), degree(O), dim(A)) =#
      #= for i = 1:dim(A) =#
      #=   c = elem_in_basis(AtoO(A[i])) =#
      #=   for j = 1:degree(O) =#
      #=     M1[j, i] = c[j] =#
      #=   end =#
      #= end =#

      M2 = zero_matrix(F, dim(A), dim(A))
      t = one(A)
      for i = 1:dim(A)
        for j = 1:dim(A)
          M2[j, i] = t.coeffs[j]
        end
        t = t*x
      end
      M2inv = inv(M2)

      function _image_index_div(a::NfRelOrdElem)
        #= amodP = mod(a, P) =#
        #= c = elem_in_basis(amodP) =#
        #= N = zero_matrix(base_ring(nf(O)), degree(O), 1) =#
        #= for i = 1:degree(O) =#
        #=   N[i, 1] = c[i] =#
        #= end =#
        #= MN = hcat(M1, N) =#
        #= d, MN = rref(MN) =#
        #= MN = inv(base_ring(nf(O))(d))*MN =#
        #= MM = sub(MN, 1:dim(A), 1:dim(A)) =#
        #= NN = sub(MN, 1:dim(A), dim(A) + 1:dim(A) + 1) =#
        #= if dim(A) + 1 >= rows(MN) =#
        #=   @assert all([ iszero(MN[dim(A) + 1, i]) for i = dim(A) + 1:degree(O) ]) =#
        #= end =#
        #= b = solve_ut(MM, NN) =#
        b = OtoA(a)
        bb = zero_matrix(F, dim(A), 1)
        for i = 1:dim(A)
          #= bb[i, 1] = mmF(b[i, 1]) =#
          bb[i, 1] = b.coeffs[i]
        end
        @assert mod(AtoO(A([ bb[i, 1] for i = 1:dim(A) ])), P) == mod(a, P)
        bb = M2inv*bb
        g = Fx([ bb[i, 1] for i = 1:dim(A) ])
        return mFF(g)
      end

      function _preimage_index_div(a::fq)
        g = inv(mFF)(a)
        c = zero_matrix(F, dim(A), 1)
        for i = 1:dim(A)
          c[i, 1] = coeff(g, i - 1)
        end
        c = M2*c
        b = A([ c[i, 1] for i = 1:dim(A) ])
        return AtoO(b)
      end
      z.header = MapHeader(O, FF, _image_index_div, _preimage_index_div)
    else
      h = P.non_index_div_poly
      # F and base_ring(h) are the same as in "==" but not as in "==="
      hh = Fx()
      ccall((:fq_poly_set, :libflint), Void, (Ptr{fq_poly}, Ptr{fq_poly}, Ptr{FqFiniteField}), &hh, &h, &F)
      z.poly_of_the_field = hh
      FF, mFF = field_extension(hh)

      function _image(x::NfRelOrdElem)
        f = parent(nf(O).pol)(elem_in_nf(x))
        if iszero(f)
          ff = Fx()
        else
          ff = Fx([ mmF(coeff(f, i)) for i = 0:degree(f) ])
        end
        return image(mFF, ff)
      end

      function _preimage(x::fq)
        f = preimage(mFF, x)
        immF = inv(mmF)
        y = nf(O)([ immF(coeff(f, i)) for i = 0:degree(f) ])
        return O(y)
      end
      z.header = MapHeader(O, FF, _image, _preimage)
    end
    return z
  end
end

image(f::NfRelOrdToFqMor, x::fq_poly) = f.header.image(x)

preimage(f::NfRelOrdToFqMor, x::fq) = f.header.preimage(x)

mutable struct NfRelOrdToAlgAssMor{T1, T2, T3} <: Map{NfRelOrd{T1, T2}, AlgAss{T3}}
  header::MapHeader

  function NfRelOrdToAlgAssMor{T1, T2, T3}(O::NfRelOrd{T1, T2}, A::AlgAss{T3}, _image::Function, _preimage::Function) where {T1, T2, T3}
    z = new{T1, T2, T3}()
    z.header = MapHeader(O, A, _image, _preimage)
    return z
  end
end

image(f::NfRelOrdToAlgAssMor{T1, T2, T3}, x::NfRelOrdElem{T1}) where {T1, T2, T3} = f.header.image(x)

preimage(f::NfRelOrdToAlgAssMor{T1, T2, T3}, x::AlgAssElem{T3}) where {T1, T2, T3} = f.header.preimage(x)
