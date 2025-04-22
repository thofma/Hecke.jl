mutable struct NfRelOrdToFqMor{T, S, U} <: Map{RelNumFieldOrder{T, S, U}, FqField, HeckeMap, NfRelOrdToFqMor}
  header::MapHeader{RelNumFieldOrder{T, S, U}, FqField}
  poly_of_the_field::FqPolyRingElem
  P::RelNumFieldOrderIdeal{T, S, U}
  function NfRelOrdToFqMor{T, S, U}() where {T, S, U}
    return new{T, S, U}()
  end
end

function NfRelOrdToFqMor(O::RelNumFieldOrder{T, S, U}, P::RelNumFieldOrderIdeal{T, S, U}) where {T, S, U}
  z = NfRelOrdToFqMor{T, S, U}()
  z.P = P
  p = minimum(P, copy = false)
  F, mF = residue_field(order(p), p)
  mmF = extend(mF, nf(order(p)))
  Fx, = polynomial_ring(F, "x", cached = false)
  if is_index_divisor(O, p)
    A, OtoA = StructureConstantAlgebra(O, P, p, mF)
    AtoO = pseudo_inv(OtoA)
    x = rand(A)
    h = minpoly(x)
    while degree(h) != dim(A)
      x = rand(A)
      h = minpoly(x)
    end
    # F and base_ring(h) are the same as in "==" but not as in "==="
    #hh = h
    hh = Fx()
    ccall((:fq_default_poly_set, libflint), Nothing, (Ref{FqPolyRingElem}, Ref{FqPolyRingElem}, Ref{FqField}), hh, h, F)
    z.poly_of_the_field = hh
    FF, mFF = Nemo._residue_field(hh; absolute = true)

    M = zero_matrix(F, dim(A), dim(A))
    t = one(A)
    for i = 1:dim(A)
      for j = 1:dim(A)
        M[j, i] = t.coeffs[j]
      end
      t = t*x
    end
    Minv = inv(M)

    function _image_index_div(a::RelNumFieldOrderElem)
      b = OtoA(a)
      bb = zero_matrix(F, dim(A), 1)
      for i = 1:dim(A)
        bb[i, 1] = b.coeffs[i]
      end
      @assert mod(AtoO(A([ bb[i, 1] for i = 1:dim(A) ])), P) == mod(a, P)
      bb = Minv*bb
      g = Fx([ bb[i, 1] for i = 1:dim(A) ])
      return mFF(g)
    end

    function _preimage_index_div(a::FqFieldElem)
      #g = pseudo_inv(mFF)(a)
      c = zero_matrix(F, dim(A), 1)
      aa = preimage(mFF, a)
      for i = 1:dim(A)
        c[i, 1] = coeff(aa, i - 1)
      end
      c = M*c
      b = A([ c[i, 1] for i = 1:dim(A) ])
      res = AtoO(b)
      return res
    end
    z.header = MapHeader(O, FF, _image_index_div, _preimage_index_div)
  else
    h = P.non_index_div_poly
    # F and base_ring(h) are the same as in "==" but not as in "==="
    hh = Fx()
    ccall((:fq_default_poly_set, libflint), Nothing, (Ref{FqPolyRingElem}, Ref{FqPolyRingElem}, Ref{FqField}), hh, h, F)
    z.poly_of_the_field = hh
    d = degree(hh)
    FF, mFF2 = Nemo._residue_field(hh; absolute = true)

    function _image(x::RelNumFieldOrderElem)
      f = parent(nf(O).pol)(elem_in_nf(x))
      if iszero(f)
        ff = Fx()
      else
        ff = Fx([ mmF(coeff(f, i)) for i = 0:degree(f) ])
      end
      return mFF2(ff)
    end

    function _preimage(x::FqFieldElem)
      f = preimage(mFF2, x)
      immF = pseudo_inv(mmF)
      #xp = Nemo._as_poly(x)
      y = nf(O)([ immF(coeff(f, i)) for i = 0:(d - 1) ])
      res = O(y)
      return res
    end
    z.header = MapHeader(O, FF, _image, _preimage)
  end
  return z
end

function extend(f::NfRelOrdToFqMor{T, S}, K::RelSimpleNumField{T}) where {T, S}
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  g = NfRelToFqMor{T}()
  g.header.domain = K
  g.header.codomain = f.header.codomain

  O = domain(f)
  P = f.P
  u = anti_uniformizer(P)

  function _image(x::RelSimpleNumFieldElem{T})
    m = denominator(x, O)
    a = O(m*x)
    b = O(m)
    l = valuation(m, P)
    if l != 0
      a = O(elem_in_nf(a)*u^l)
      b = O(elem_in_nf(b)*u^l)
    end
    return f(a)//f(b)
  end

  function _preimage(x::FqFieldElem)
    return elem_in_nf(preimage(f, x))
  end

  g.header.image = _image
  g.header.preimage = _preimage

  return g
end

mutable struct RelOrdToAlgAssMor{S, T} <: Map{S, StructureConstantAlgebra{T}, HeckeMap, RelOrdToAlgAssMor}
  header::MapHeader{S, StructureConstantAlgebra{T}}

  function RelOrdToAlgAssMor{S, T}(O::S, A::StructureConstantAlgebra{T}, _image::Function, _preimage::Function) where { S <: Union{ RelNumFieldOrder, AlgAssRelOrd }, T }
    z = new{S, T}()
    z.header = MapHeader(O, A, _image, _preimage)
    return z
  end
end

function RelOrdToAlgAssMor(O::Union{ RelNumFieldOrder, AlgAssRelOrd }, A::StructureConstantAlgebra{T}, _image, _preimage) where {T}
  return RelOrdToAlgAssMor{typeof(O), T}(O, A, _image, _preimage)
end

mutable struct RelOrdQuoMap{T1, T2, T3, S} <: Map{T1, RelOrdQuoRing{T1, T2, T3}, HeckeMap, RelOrdQuoMap}
  header::MapHeader{T1, RelOrdQuoRing{T1, T2, T3}}

  function RelOrdQuoMap{T1, T2, T3, S}(O::T1, Q::RelOrdQuoRing{T1, T2, T3}) where { T1, T2, T3, S }
    z = new{T1, T2, T3, S}()

    _image = function (x::S)
      return Q(x)
    end

    _preimage = function (x::RelOrdQuoRingElem{T1, T2, T3, S})
      return x.elem
    end

    z.header = MapHeader(O, Q, _image, _preimage)
    return z
  end
end

function RelOrdQuoMap(O::T1, Q::RelOrdQuoRing{T1, T2, T3}) where { T1, T2, T3 }
  S = elem_type(O)
  return RelOrdQuoMap{T1, T2, T3, S}(O, Q)
end

mutable struct NfRelOrdToFqFieldRelMor{S} <: Map{S, FqField, HeckeMap, NfRelOrdToFqFieldRelMor}
  header::MapHeader{S, FqField}
  poly_of_the_field
  P
  map_subfield::Union{NfOrdToFqFieldMor, NfRelOrdToFqFieldRelMor}

    function NfRelOrdToFqFieldRelMor{S}(O::S, P, mapsub) where {S}
    z = new{S}()
    z.P = P
    z.map_subfield = mapsub
    p = minimum(P, copy = false)
    FK, mK = codomain(mapsub), mapsub
    mmK = extend(mK, nf(order(p)))
    FKx, = polynomial_ring(FK, "x", cached = false)
    if is_index_divisor(O, p)
      A, OtoA = StructureConstantAlgebra(O, P, p, mK)
      AtoO = pseudo_inv(OtoA)
      x = rand(A)
      h = minpoly(x)
      while degree(h) != dim(A)
        x = rand(A)
        h = minpoly(x)
      end
      hh = FKx()
      ccall((:fq_default_poly_set, libflint), Nothing, (Ref{FqPolyRingElem}, Ref{FqPolyRingElem}, Ref{FqField}), hh, h, FK)
      z.poly_of_the_field = hh

      FE, mE = Nemo._residue_field(hh)
#
#      FE = RelFinField(hh, :v)
#      FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
#      FE2, mE2 = field_extension(hh)
#      FE2toFEabs = hom(FE2, FEabs, gen(FEabs))
#      mE = compose(mE2, compose(FE2toFEabs, FEabstoFE))
#
      M = zero_matrix(FK, dim(A), dim(A))
      t = one(A)
      for i = 1:dim(A)
        for j = 1:dim(A)
          M[j, i] = t.coeffs[j]
        end
        t = t*x
      end
      Minv = inv(M)

      function _image_index_div(a::RelNumFieldOrderElem)
        b = OtoA(a)
        bb = zero_matrix(FK, dim(A), 1)
        for i = 1:dim(A)
          bb[i, 1] = b.coeffs[i]
        end
        @assert mod(AtoO(A([ bb[i, 1] for i = 1:dim(A) ])), P) == mod(a, P)
        bb = Minv*bb
        g= FKx([ bb[i, 1] for i = 1:dim(A) ])
        return mE(g)
      end

      function _preimage_index_div(a::FqFieldElem)
        g = pseudo_inv(mE)(a)
        c = zero_matrix(FK, dim(A), 1)
        for i = 1:dim(A)
          c[i,1] = coeff(g, i-1)
        end
        c = M*c
        b = A([c[i,1] for i=1:dim(A)])
        res = AtoO(b)
        return res
      end
      z.header = MapHeader(O, FE, _image_index_div, _preimage_index_div)
    else
      h = P.non_index_div_poly
      hh = FKx()
      ccall((:fq_default_poly_set, libflint), Nothing, (Ref{FqPolyRingElem}, Ref{FqPolyRingElem}, Ref{FqField}), hh, h, FK)
      z.poly_of_the_field = hh

      FE, mE = Nemo._residue_field(hh)

      #FE = RelFinField(hh, :v)
      #FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
      #FE2, mE2 = field_extension(hh)
      #FE2toFEabs = hom(FE2, FEabs, gen(FEabs))
      #mE = compose(mE2, compose(FE2toFEabs, FEabstoFE))

      function _image(x::RelNumFieldOrderElem)
        f = parent(nf(O).pol)(elem_in_nf(x))
        if iszero(f)
          ff = FKx()
        else
          ff = FKx([ mmK(coeff(f, i)) for i =0:degree(f)])
        end
        return image(mE, ff)
      end

      function _preimage(x::FqFieldElem)
        f = preimage(mE, x)
        immK = pseudo_inv(mmK)
        y = nf(O)([ immK(coeff(f,i)) for i=0:degree(f)])
        res = O(y)
        return res
      end
      z.header = MapHeader(O, FE, _image, _preimage)
    end
    return z
  end
end

mutable struct NfRelOrdToRelFinFieldMor{S, T} <: Map{S, RelFinField{T}, HeckeMap, NfRelOrdToRelFinFieldMor}
  header::MapHeader{S, RelFinField{T}}
  poly_of_the_field
  P
  map_subfield::Union{NfOrdToFqMor, NfRelOrdToRelFinFieldMor}

    function NfRelOrdToRelFinFieldMor{S, T}(O::S, P, mapsub::NfOrdToFqMor) where {S, T <: FqPolyRepFieldElem}
    z = new{S, T}()
    z.P = P
    z.map_subfield = mapsub
    p = minimum(P, copy = false)
    FK, mK = codomain(mapsub), mapsub
    mmK = extend(mK, nf(order(p)))
    FKx, = polynomial_ring(FK, "x", cached = false)
    if is_index_divisor(O, p)
      A, OtoA = StructureConstantAlgebra(O, P, p)
      AtoO = pseudo_inv(OtoA)
      x = rand(A)
      h = minpoly(x)
      while degree(h) != dim(A)
        x = rand(A)
        h = minpoly(x)
      end
      hh = FKx()
      ccall((:fq_poly_set, libflint), Nothing, (Ref{FqPolyRepPolyRingElem}, Ref{FqPolyRepPolyRingElem}, Ref{FqPolyRepField}), hh, h, FK)
      z.poly_of_the_field = hh

      FE = RelFinField(hh, :v)
      FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
      FE2, mE2 = field_extension(hh)
      FE2toFEabs = hom(FE2, FEabs, gen(FEabs))
      mE = compose(mE2, compose(FE2toFEabs, FEabstoFE))

      M = zero_matrix(FK, dim(A), dim(A))
      t = one(A)
      for i = 1:dim(A)
        for j = 1:dim(A)
          M[j, i] = t.coeffs[j]
        end
        t = t*x
      end
      Minv = inv(M)

      function _image_index_div(a::RelNumFieldOrderElem)
        b = OtoA(a)
        bb = zero_matrix(FK, dim(A), 1)
        for i = 1:dim(A)
          bb[i, 1] = b.coeffs[i]
        end
        @assert mod(AtoO(A([ bb[i, 1] for i = 1:dim(A) ])), P) == mod(a, P)
        bb = Minv*bb
        g= FKx([ bb[i, 1] for i = 1:dim(A) ])
        return mE(g)
      end

      function _preimage_index_div(a::RelFinFieldElem)
        g = pseudo_inv(mE)(a)
        c = zero_matrix(FK, dim(A), 1)
        for i = 1:dim(A)
          c[i,1] = coeff(g, i-1)
        end
        c = M*c
        b = A([c[i,1] for i=1:dim(A)])
        return AtoO(b)
      end
      z.header = MapHeader(O, FE, _image_index_div, _preimage_index_div)
    else
      h = P.non_index_div_poly
      hh = FKx()
      ccall((:fq_poly_set, libflint), Nothing, (Ref{FqPolyRepPolyRingElem}, Ref{FqPolyRepPolyRingElem}, Ref{FqPolyRepField}), hh, h, FK)
      z.poly_of_the_field = hh

      FE = RelFinField(hh, :v)
      FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
      FE2, mE2 = field_extension(hh)
      FE2toFEabs = hom(FE2, FEabs, gen(FEabs))
      mE = compose(mE2, compose(FE2toFEabs, FEabstoFE))

      function _image(x::RelNumFieldOrderElem)
        f = parent(nf(O).pol)(elem_in_nf(x))
        if iszero(f)
          ff = FKx()
        else
          ff = FKx([ mmK(coeff(f, i)) for i =0:degree(f)])
        end
        return image(mE, ff)
      end

      function _preimage(x::RelFinFieldElem)
        f = preimage(mE, x)
        immK = pseudo_inv(mmK)
        y = nf(O)([ immK(coeff(f,i)) for i=0:degree(f)])
        return O(y)
      end
      z.header = MapHeader(O, FE, _image, _preimage)
    end
    return z
  end

  function NfRelOrdToRelFinFieldMor{S, T}(O::S, P, mapsub::NfRelOrdToRelFinFieldMor) where {S, T <: RelFinFieldElem}
    z = new{S, T}()
    z.P = P
    z.map_subfield = mapsub
    p = minimum(P, copy = false)
    FK, mK = codomain(mapsub), mapsub
    mmK = extend(mK, nf(order(p)))
    FKx, = polynomial_ring(FK, "x", cached = false)
    FKabs, FKabstoFK = Hecke.absolute_field(FK, cached = false)
    FKtoFKabs = pseudo_inv(FKabstoFK)
    FKabsz, _ = polynomial_ring(FKabs, "z", cached = false)
    if is_index_divisor(O, p)
      A, OtoA = StructureConstantAlgebra(O, P, p, mK)
      AtoO = pseudo_inv(OtoA)
      x = rand(A)
      h = minpoly(x)
      while degree(h) != dim(A)
        x = rand(A)
        h = minpoly(x)
      end
      hh = FKabsz()
      ccall((:fq_poly_set, libflint), Nothing, (Ref{FqPolyRepPolyRingElem}, Ref{FqPolyRepPolyRingElem}, Ref{FqPolyRepField}), hh, h, FKabs)
      h = map_coefficients(FKabstoFK, hh, cached = false)
      h = FKx(collect(coefficients(h)))
      z.poly_of_the_field = h

      FE = RelFinField(h, :v)
      FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
      FKxtoFKabsz = MapFromFunc(FKx, FKabsz, f -> FKabsz(FKtoFKabs.(collect(coefficients(f)))))
      FE2, mE2 = field_extension(hh)
      FE2toFEabs = hom(FE2, FEabs, gen(FEabs))
      mE = compose(FKxtoFKabsz,compose(mE2, compose(FE2toFEabs, FEabstoFE)))

      M = zero_matrix(FK, dim(A), dim(A))
      t = one(A)
      for i = 1:dim(A)
        for j = 1:dim(A)
          M[j, i] = t.coeffs[j]
        end
        t = t*x
      end
      Minv = inv(M)

      function _image_index_div(a::RelNumFieldOrderElem)
        b = OtoA(a)
        bb = zero_matrix(FK, dim(A), 1)
        for i = 1:dim(A)
          bb[i, 1] = b.coeffs[i]
        end
        @assert mod(AtoO(A([ bb[i, 1] for i = 1:dim(A) ])), P) == mod(a, P)
        bb = Minv*bb
        g= FKx([ bb[i, 1] for i = 1:dim(A) ])
        return mE(g)
      end

      function _preimage_index_div(a::RelFinFieldElem)
        g = pseudo_inv(mE)(a)
        c = zero_matrix(FK, dim(A), 1)
        for i = 1:dim(A)
          c[i,1] = coeff(g, i-1)
        end
        c = M*c
        b = A([c[i,1] for i=1:dim(A)])
        return AtoO(b)
      end
      z.header = MapHeader(O, FE, _image_index_div, _preimage_index_div)
    else
      h = P.non_index_div_poly
      hh = FKabsz()
      ccall((:fq_poly_set, libflint), Nothing, (Ref{FqPolyRepPolyRingElem}, Ref{FqPolyRepPolyRingElem}, Ref{FqPolyRepField}), hh, h, FKabs)
      h = map_coefficients(FKabstoFK, hh, cached = false)
      h = FKx(collect(coefficients(h)))
      z.poly_of_the_field = h

      FE = RelFinField(h, :v)
      FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
      FKxtoFKabsz = MapFromFunc(FKx, FKabsz, f -> FKabsz(FKtoFKabs.(collect(coefficients(f)))))
      FE2, mE2 = field_extension(hh)
      FE2toFEabs = hom(FE2, FEabs, gen(FEabs))
      mE = compose(FKxtoFKabsz,compose(mE2, compose(FE2toFEabs, FEabstoFE)))

      function _image(x::RelNumFieldOrderElem)
        f = parent(nf(O).pol)(elem_in_nf(x))
        if iszero(f)
          ff = FKx()
        else
          ff = FKx([ mmK(coeff(f, i)) for i =0:degree(f)])
        end
        return image(mE, ff)
      end

      function _preimage(x::RelFinFieldElem)
        f = preimage(mE, x)
        immK = pseudo_inv(mmK)
        y = nf(O)([ immK(coeff(f,i)) for i=0:degree(f)])
        return O(y)
      end
      z.header = MapHeader(O, FE, _image, _preimage)
    end
    return z
  end

end

mutable struct NfRelToFqFieldRelMor{S} <: Map{S, FqField, HeckeMap, NfRelToFqFieldRelMor}
  header::MapHeader{S, FqField}

  function NfRelToFqFieldRelMor{S}() where {S <: RelSimpleNumField}
    z = new{S}()
    z.header = MapHeader{S, FqField}()
    return z
  end
end

function extend(f::NfRelOrdToFqFieldRelMor{S}, E::RelSimpleNumField) where {S}
  nf(domain(f)) != E && error("Number field is not the number field of the order")

  g = NfRelToFqFieldRelMor{typeof(E)}()
  g.header.domain = E
  g.header.codomain = f.header.codomain

  OE = domain(f)
  P = f.P
  u = anti_uniformizer(P)

  function _image(x::RelSimpleNumFieldElem)
    m = denominator(x, OE)
    a = OE(m*x)
    b = OE(m)
    l = valuation(m, P)
    if l != 0
      a = OE(elem_in_nf(a)*u^l)
      b = OE(elem_in_nf(b)*u^l)
    end
    return f(a)//f(b)
  end

  function _preimage(x::FqFieldElem)
    return elem_in_nf(preimage(f, x))
  end

  g.header.image = _image
  g.header.preimage = _preimage

  return g
end

