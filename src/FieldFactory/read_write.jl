
################################################################################
#
#  Print functions
#
################################################################################
function _print_to_file(list::Vector{FieldsTower}, f::String; separator = '#')
  c = open(f, "w+")
  _print_to_file(list, c, separator = separator)
  close(c)
end

function _print_to_file(list::Vector{FieldsTower}, f::IOStream; separator = '#')
  for i = 1:length(list)
    K = list[i].field
    auts = list[i].generators_of_automorphisms
    embs = list[i].subfields
    p = K.pol
    p1 = ZZRingElem[numerator(coeff(p, i)) for i = 0:degree(p)]
    Qx = parent(p)
    imgs = QQPolyRingElem[Qx(image_primitive_element(x)) for x in auts]
    imgs_coeff = Vector{QQFieldElem}[QQFieldElem[coeff(x1, i) for i = 0:degree(x1)] for x1 in imgs]
    embs_imgs = Tuple{QQPolyRingElem, QQPolyRingElem}[(codomain(x2).pol, parent(codomain(x2).pol)(image_primitive_element(x2))) for x2 in embs]
    embs_imgs_coeff = Vector{Tuple{Vector{QQFieldElem}, Vector{QQFieldElem}}}(undef, length(embs_imgs))
    for i = 1:length(embs_imgs)
      y, z = embs_imgs[i]
      embs_imgs_coeff[i] = ([coeff(y, j) for j = 0:degree(y)], [coeff(z, k) for k = 0:degree(z)])
    end
    Base.write(f, "$(p1)$(separator)$(imgs_coeff)$(separator)$(embs_imgs_coeff)\n")
  end
  return nothing
end

Base.convert(::Type{QQFieldElem}, a::Rational{<: Integer}) = QQFieldElem(a)

function _read_from_file(f::String)
  c = open(f, "r")
  v = _read_from_file(c)
  close(c)
  return v
end

function _read_from_file(f::IOStream)
  Qx, x = polynomial_ring(FlintQQ, "x")
  list = Vector{FieldsTower}(undef, countlines(f))
  seekstart(f)
  QQ = number_field(x-1, "b", cached = false, check = false)[1]
  for (k, l) in enumerate(eachline(f))
    a = _parse_fields_tower_blurb(l)
    K = number_field(Qx(a[1]), "a", cached = false, check = false)[1]
    auts = Vector{morphism_type(AbsSimpleNumField, AbsSimpleNumField)}(undef, length(a[2]))
    for i = 1:length(auts)
      img = K(Qx(a[2][i]))
      auts[i] = hom(K, K, img, check = false)
    end
    embs = Vector{morphism_type(AbsSimpleNumField, AbsSimpleNumField)}(undef, length(a[3]))
    def_pol = Qx(a[3][1][1])
    if def_pol == K.pol
      Kcodomain = K
    else
      Kcodomain = number_field(def_pol, cached = false, check = false)[1]
    end
    embs[1] = hom(QQ, Kcodomain, Kcodomain(Qx(a[3][1][2])), check = false)
    for i = 2:(length(a[3]))
      Kdomain = Kcodomain
      def_pol = Qx(a[3][i][1])
      if def_pol == K.pol
        Kcodomain = K
      else
        Kcodomain = number_field(def_pol, cached = false, check = false)[1]
      end
      embs[i] = hom(Kdomain, Kcodomain, Kcodomain(Qx(a[3][i][2])), check = false)
    end
    list[k] = FieldsTower(K, auts, embs)
  end
  return list
end

function _parse_as_fmpq_vector(s)
  res = QQFieldElem[]
  i = 1
  while s[i] != '['
    i += 1
  end
  i += 1
  is_rational = false
  j = i
  last_parsed = 0
  while true
    while s[j] == ' '
      j += 1
    end
    if s[j] == ']'
      z = parse(ZZRingElem, s[i:j-1])
      if is_rational
        push!(res, last_parsed//z)
        is_rational = false
      else
        push!(res, QQFieldElem(z))
      end
      break
    end
    if s[j] == ','
      z = parse(ZZRingElem, s[i:j-1])
      if is_rational
        push!(res, last_parsed//z)
        is_rational = false
      else
        push!(res, QQFieldElem(z))
      end
      i = j + 1
    end
    if s[j] == '/'
      last_parsed = parse(ZZRingElem, s[i:j-1])
      is_rational = true
      j += 2
      i = j
    end
    j += 1
  end
  res
end

function _parse_array_of_array_of_fmpq(s)
  res = Vector{QQFieldElem}[]
  i = 1
  while s[i] != '['
    i += 1
  end
  i += 1
  while s[i] != ']'
    k = _find_end_of_array_not_nested(s, i)
    v = _parse_as_fmpq_vector(s[i:k])
    i = k + 1
    push!(res, v)
  end
  return res
end

function _skip_head(s)
  i = 1
  while s[i] != '['
    i += 1
  end
  return i
end

function _parse_array_of_tuples_of_arrays(s)
  res = Tuple{Vector{QQFieldElem}, Vector{QQFieldElem}}[]
  i = _skip_head(s)
  i += 1
  end_sbraket = _find_closing_sbraket(s, i)
  while i < end_sbraket
    while s[i] != '('
      i += 1
    end
    i += 1
    while s[i] != '['
      i += 1
    end
    i += 1
    k = _find_closing_sbraket(s, i)
    vec1 = _parse_as_fmpq_vector(s[i-1:k-1])
    i = k
    while s[i] != ','
      i += 1
    end
    i += 1
    while s[i] != '['
      i += 1
    end
    i += 1
    k = _find_closing_sbraket(s, i)
    vec2 = _parse_as_fmpq_vector(s[i-1:k-1])
    i = k
    while s[i] != ')'
      i += 1
    end
    i += 1
    push!(res, (vec1, vec2))
    while s[i] != ','
      i += 1
      if i == end_sbraket
        return res
      end
    end
    i += 1
  end
  res
end

function _find_closing_sbraket(s, start = 1)
  @assert s[start - 1] == '['
  i = start
  open = 1
  while open != 0
    if s[i] == '['
      open += 1
    elseif s[i] == ']'
      open -= 1
    end
    i += 1
  end
  return i
end

function _find_closing_braket(s, start = 1)
  i = start
  open = 1
  while open != 0
    if s[i] == '('
      open += 1
    elseif s[i] == ')'
      open -= 1
    end
    i += 1
  end
  return i
end

# return value will point to the closing ]
function _find_end_of_array_not_nested(s, start = 1)
  i = start + 1
  while s[i] != ']'
    i += 1
  end
  return i
end

function _parse_fields_tower_blurb(s)
  s_split = split(s, '#')
  @assert length(s_split) == 3
  res1 = _parse_as_fmpq_vector(String(s_split[1]))
  res2 = _parse_array_of_array_of_fmpq(String(s_split[2]))
  res3 = _parse_array_of_tuples_of_arrays(String(s_split[3]))
  return res1, res2, res3
end
