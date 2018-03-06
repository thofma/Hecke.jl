mutable struct NfRelOrdToFqMor <: Map{NfRelOrd, FqFiniteField}
  header::MapHeader
  poly_of_the_field::fq_poly
  P::NfRelOrdIdl

  function NfRelOrdToFqMor(O::NfRelOrd, P::NfRelOrdIdl)
    if isindex_divisor(O, minimum(P, Val{false}))
      error("Not implemented yet.")
    end
    z = new()
    z.P = P
    p = minimum(P)
    F, mF = ResidueField(order(p), p)
    mmF = extend(mF, nf(order(p)))
    h = P.non_index_div_poly
    # F and base_ring(h) are the same as in "==" but not as in "==="
    Fx = F["x"][1]
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
    return z
  end
end

image(f::NfRelOrdToFqMor, x::fq_poly) = f.header.image(x)

preimage(f::NfRelOrdToFqMor, x::fq) = f.header.preimage(x)
