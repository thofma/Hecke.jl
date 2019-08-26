
################################################################################
#
#  Print functions
#
################################################################################
function _print_to_file(list::Vector{FieldsTower}, f::String)
  c = open(f, "a+")
  _print_to_file(list, c)
  close(c)
end

function _print_to_file(list::Vector{FieldsTower}, f::IOStream)
  for i = 1:length(list)
    K = list[i].field
    auts = list[i].generators_of_automorphisms
    embs = list[i].subfields
    p = K.pol
    p1 = fmpz[numerator(coeff(p, i)) for i = 0:degree(p)]
    Qx = parent(p)
    imgs = fmpq_poly[Qx(x.prim_img) for x in auts]
    imgs_coeff = Vector{fmpq}[fmpq[coeff(x1, i) for i = 0:degree(x1)] for x1 in imgs]
    embs_imgs = Tuple{fmpq_poly, fmpq_poly}[(codomain(x2).pol, parent(codomain(x2).pol)(x2.prim_img)) for x2 in embs]
    embs_imgs_coeff = Vector{Tuple{Vector{fmpq}, Vector{fmpq}}}(undef, length(embs_imgs))
    for i = 1:length(embs_imgs)
      y, z = embs_imgs[i]
      embs_imgs_coeff[i] = ([coeff(y, j) for j = 0:degree(y)], [coeff(z, k) for k = 0:degree(z)])
    end
    write(f, "$(p1),$(imgs_coeff),$(embs_imgs_coeff)\n")
  end
  return nothing
end

Base.convert(::Type{fmpq}, a::Rational{<: Integer}) = fmpq(a)

function _read_from_file(f::String)
  c = open(f, "r")
  v = _read_from_file(c)
  close(c)
  return v
end

function _read_from_file(f::IOStream)
  Qx, x = PolynomialRing(FlintQQ, "x")
  list = Vector{FieldsTower}()
  for l in eachline(f)
    a = eval(Meta.parse(l))
    K = number_field(Qx(a[1]), "a", cached = false, check = false)[1]
    auts = Vector{NfToNfMor}(undef, length(a[2]))
    for i = 1:length(auts)
      img = K(Qx(a[2][i]))
      auts[i] = NfToNfMor(K, K, img)
    end
    embs = Vector{NfToNfMor}(undef, length(a[3]))
    Kdomain = number_field(x-1)[1]
    Kcodomain = number_field(Qx(a[3][1][1]), cached = false, check = false)[1]
    embs[1] = NfToNfMor(Kdomain, Kcodomain, Kcodomain(Qx(a[3][1][2])))
    for i = 2:(length(a[3]))
      Kdomain = Kcodomain
      Kcodomain = number_field(Qx(a[3][i][1]), cached = false, check = false)[1]
      embs[i] = NfToNfMor(Kdomain, Kcodomain, Kcodomain(Qx(a[3][i][2])))
    end
    push!(list, FieldsTower(K, auts, embs))
  end
  return list
end

