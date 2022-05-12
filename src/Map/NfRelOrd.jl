mutable struct NfRelOrdToFqMor{T, S, U} <: Map{NfRelOrd{T, S, U}, FqFiniteField, HeckeMap, NfRelOrdToFqMor}
  header::MapHeader{NfRelOrd{T, S, U}, FqFiniteField}
  poly_of_the_field::fq_poly
  P::NfRelOrdIdl{T, S, U}

  function NfRelOrdToFqMor{T, S, U}(O::NfRelOrd{T, S, U}, P::NfRelOrdIdl{T, S, U}) where {T, S, U}
    z = new{T, S, U}()
    z.P = P
    p = minimum(P, copy = false)
    F, mF = ResidueField(order(p), p)
    mmF = extend(mF, nf(order(p)))
    Fx, = PolynomialRing(F, "x", cached = false)
    if is_index_divisor(O, p)
      A, OtoA = AlgAss(O, P, p)
      AtoO = pseudo_inv(OtoA)
      x = rand(A)
      h = minpoly(x)
      while degree(h) != dim(A)
        x = rand(A)
        h = minpoly(x)
      end
      # F and base_ring(h) are the same as in "==" but not as in "==="
      hh = Fx()
      ccall((:fq_poly_set, libflint), Nothing, (Ref{fq_poly}, Ref{fq_poly}, Ref{FqFiniteField}), hh, h, F)
      z.poly_of_the_field = hh
      FF, mFF = field_extension(hh)

      M = zero_matrix(F, dim(A), dim(A))
      t = one(A)
      for i = 1:dim(A)
        for j = 1:dim(A)
          M[j, i] = t.coeffs[j]
        end
        t = t*x
      end
      Minv = inv(M)

      function _image_index_div(a::NfRelOrdElem)
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

      function _preimage_index_div(a::fq)
        g = pseudo_inv(mFF)(a)
        c = zero_matrix(F, dim(A), 1)
        for i = 1:dim(A)
          c[i, 1] = coeff(g, i - 1)
        end
        c = M*c
        b = A([ c[i, 1] for i = 1:dim(A) ])
        return AtoO(b)
      end
      z.header = MapHeader(O, FF, _image_index_div, _preimage_index_div)
    else
      h = P.non_index_div_poly
      # F and base_ring(h) are the same as in "==" but not as in "==="
      hh = Fx()
      ccall((:fq_poly_set, libflint), Nothing, (Ref{fq_poly}, Ref{fq_poly}, Ref{FqFiniteField}), hh, h, F)
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
        immF = pseudo_inv(mmF)
        y = nf(O)([ immF(coeff(f, i)) for i = 0:degree(f) ])
        return O(y)
      end
      z.header = MapHeader(O, FF, _image, _preimage)
    end
    return z
  end
end

function extend(f::NfRelOrdToFqMor{T, S}, K::NfRel{T}) where {T, S}
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  g = NfRelToFqMor{T}()
  g.header.domain = K
  g.header.codomain = f.header.codomain

  O = domain(f)
  P = f.P
  u = anti_uniformizer(P)

  function _image(x::NfRelElem{T})
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

  function _preimage(x::fq)
    return elem_in_nf(preimage(f, x))
  end

  g.header.image = _image
  g.header.preimage = _preimage

  return g
end

mutable struct RelOrdToAlgAssMor{S, T} <: Map{S, AlgAss{T}, HeckeMap, RelOrdToAlgAssMor}
  header::MapHeader{S, AlgAss{T}}

  function RelOrdToAlgAssMor{S, T}(O::S, A::AlgAss{T}, _image::Function, _preimage::Function) where { S <: Union{ NfRelOrd, AlgAssRelOrd }, T }
    z = new{S, T}()
    z.header = MapHeader(O, A, _image, _preimage)
    return z
  end
end

function RelOrdToAlgAssMor(O::Union{ NfRelOrd, AlgAssRelOrd }, A::AlgAss{T}, _image, _preimage) where {T}
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


mutable struct NfRelOrdToRelFinFieldMor{S, T} <: Map{S, RelFinField{T}, HeckeMap, NfRelOrdToRelFinFieldMor}
  header::MapHeader{S, RelFinField{T}}
  poly_of_the_field
  P
  map_subfield::Union{NfOrdToFqMor, NfRelOrdToRelFinFieldMor}

    function NfRelOrdToRelFinFieldMor{S, T}(O::S, P, mapsub::NfOrdToFqMor) where {S, T <: fq}
    z = new{S, T}()
    z.P = P
    z.map_subfield = mapsub
    p = minimum(P, copy = false)
    FK, mK = codomain(mapsub), mapsub
    mmK = extend(mK, nf(order(p)))
    FKx, = PolynomialRing(FK, "x", cached = false)
    if is_index_divisor(O, p)
      A, OtoA = AlgAss(O, P, p)
      AtoO = pseudo_inv(OtoA)
      x = rand(A)
      h = minpoly(x)
      while degree(h) != dim(A)
        x = rand(A)
        h = minpoly(x)
      end
      hh = FKx()
      ccall((:fq_poly_set, libflint), Nothing, (Ref{fq_poly}, Ref{fq_poly}, Ref{FqFiniteField}), hh, h, FK)
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
   
      function _image_index_div(a::NfRelOrdElem)
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
      ccall((:fq_poly_set, libflint), Nothing, (Ref{fq_poly}, Ref{fq_poly}, Ref{FqFiniteField}), hh, h, FK)
      z.poly_of_the_field = hh
    
      FE = RelFinField(hh, :v)
      FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
      FE2, mE2 = field_extension(hh)
      FE2toFEabs = hom(FE2, FEabs, gen(FEabs))
      mE = compose(mE2, compose(FE2toFEabs, FEabstoFE))

      function _image(x::NfRelOrdElem)
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
    FKx, = PolynomialRing(FK, "x", cached = false)
    FKabs, FKabstoFK = Hecke.absolute_field(FK, cached = false)
    FKtoFKabs = pseudo_inv(FKabstoFK)
    FKabsz, _ = PolynomialRing(FKabs, "z", cached = false)
    if is_index_divisor(O, p)
      A, OtoA = AlgAss(O, P, p)
      AtoO = pseudo_inv(OtoA)
      x = rand(A)
      h = minpoly(x)
      while degree(h) != dim(A)
        x = rand(A)
        h = minpoly(x)
      end
      hh = FKabsz()
      ccall((:fq_poly_set, libflint), Nothing, (Ref{fq_poly}, Ref{fq_poly}, Ref{FqFiniteField}), hh, h, FKabs)
      h = map_coefficients(FKabstoFK, hh)
      h = FKx(collect(coefficients(h)))
      z.poly_of_the_field = h

      FE = RelFinField(h, :v)
      FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
      FKxtoFKabsz = MapFromFunc(f -> FKabsz(FKtoFKabs.(collect(coefficients(f)))), FKx, FKabsz)
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
   
      function _image_index_div(a::NfRelOrdElem)
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
      ccall((:fq_poly_set, libflint), Nothing, (Ref{fq_poly}, Ref{fq_poly}, Ref{FqFiniteField}), hh, h, FKabs)
      h = map_coefficients(FKabstoFK, hh)
      h = FKx(collect(coefficients(h)))
      z.poly_of_the_field = h
    
      FE = RelFinField(h, :v)
      FEabs, FEabstoFE = Hecke.absolute_field(FE, cached = false)
      FKxtoFKabsz = MapFromFunc(f -> FKabsz(FKtoFKabs.(collect(coefficients(f)))), FKx, FKabsz)
      FE2, mE2 = field_extension(hh)
      FE2toFEabs = hom(FE2, FEabs, gen(FEabs))
      mE = compose(FKxtoFKabsz,compose(mE2, compose(FE2toFEabs, FEabstoFE)))

      function _image(x::NfRelOrdElem)
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

mutable struct NfRelToRelFinFieldMor{S, T} <: Map{S, Hecke.RelFinField{T}, HeckeMap, NfRelToRelFinFieldMor}
  header::MapHeader{S, Hecke.RelFinField{T}}

  function NfRelToRelFinFieldMor{S, T}() where {S <: NfRel, T <: FinFieldElem}
    z = new{S, T}()
    z.header = MapHeader{S, Hecke.RelFinField{T}}()
    return z
  end
end

function extend(f::NfRelOrdToRelFinFieldMor{S, T}, E::NfRel) where {S, T}
  nf(domain(f)) != E && error("Number field is not the number field of the order")

  g = NfRelToRelFinFieldMor{typeof(E), T}()
  g.header.domain = E
  g.header.codomain = f.header.codomain

  OE = domain(f)
  P = f.P
  u = anti_uniformizer(P)

  function _image(x::NfRelElem)
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

  function _preimage(x::RelFinFieldElem)
    return elem_in_nf(preimage(f, x))
  end

  g.header.image = _image
  g.header.preimage = _preimage

  return g
end

