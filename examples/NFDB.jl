function _class_group(c::Vector{BigInt})
  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = Qx(c)
  K, a = number_field(f, cached = false)
  OK = lll(maximal_order(K))
  C, mC = class_group(OK)
  return BigInt(order(C))
end

function _class_group_batch(polys::Vector{QQPolyRingElem})
  res = Dict()
  for i in 1:length(polys)
    f = polys[i]
    c = BigInt[FlintZZ(coeff(f, j)) for j in 0:degree(f)]
    res[i] = @spawn _class_group(c)
  end

  cls = Dict()

  @sync for i in 1:length(polys)
    @async cls[i] = fetch(res[i])
  end
  return cls
end

#mutable struct NFDB
#  path::String
#  metadata::Dict
#  head::Int
#  length::Int
#  mmapped::Bool
#  mmap::Vector{UInt}
#  hash::UInt
#  field_names::Vector{Symbol}
#
#  function NFDB(path::String)
#    metadata = Dict()
#    f = open(path)
#    head = 0
#    while true
#      line = readline(f)
#      if line[1] == '#'
#        head += 1
#        if !(':' in line)
#          continue
#        end
#        i = 2
#        while line[i] != ':'
#          i += 1
#        end
#        key = strip(line[2:i-1])
#        val = strip(line[i+1:end])
#        metadata[key] = val
#      else
#        break
#      end
#    end
#    seekstart(f)
#    length = countlines(f)
#    close(f)
#    z =  new()
#    z.path = path
#    z.metadata = metadata
#    z.head = head
#    z.length = length - head
#    z.mmapped = false
#    return z
#  end
#end

mutable struct NFDBRecord{T}
  data::Dict{Symbol, Any}
  K::AbsSimpleNumField

  function NFDBRecord{T}(data) where {T}
    z = new{T}()
    z.data = data
    return z
  end
end

mutable struct NFDB{T}
  meta::Dict{Symbol, Any}
  fields::Vector{NFDBRecord{T}}
  prop::Vector{Tuple{Symbol, Int}} # 0 not, 1 there, 2 partial

  function NFDB{T}() where {T}
    z = new{T}()
    z.meta = Dict{Symbol, Any}()
    z.fields = NFDBRecord{T}[]
    return z
  end
end

Base.length(D::NFDB) = length(D.fields)

function update_properties!(D::NFDB)
  prop = Tuple{Symbol, Int}[ (x[1], 0) for x in properties_comp ]

  if length(D.fields) == 0
    D.prop = prop
    return prop
  end

  for k in 1:length(prop)
    s = prop[k][1]
    j = 0
    for i in 1:length(D.fields)
      if haskey(D.fields[i], s)
        j += 1
      end
    end
    if j == length(D.fields)
      prop[k] = (s, 1)
    elseif j == 0
      prop[k] = (s, 0)
    else
      prop[k] = (s, 2)
    end
  end
  D.prop = prop

  return D
end

function NFDB(L::Vector{AbsSimpleNumField}; compute = [])
  res = NFDB{1}()
  for K in L
    D = _create_record(K, compute = compute)
    push!(res.fields, D)
  end

  update_properties!(res)
  return res
end

function NFDB(L::Vector{NFDBRecord{1}})
  z = NFDB{1}()
  z.fields = L
  update_properties!(z)
  return z
end


function add_meta!(D::NFDB, p::Pair)
  D.meta[p[1]] = p[2]
  return D
end

function get_meta!(D::NFDB, p::Symbol)
  if haskey(D.meta, p)
    return D.meta[p]
  else
    error("Information $p not found in metadata")
  end
end

function Base.get(D::NFDB, i::Int)
  it = Iterators.drop(eachline(D.path), D.head + i - 1)
  line = IOBuffer(first(it))
end

function _get_NFDBRecord()
end

struct NFDBRecordInfo
  name_tuples
end

const properties_comp = Dict(:id => (Int, x -> UInt(hash(x))),
                             :deg => (Int, x -> degree(x)),
                             :poly => (QQPolyRingElem, x -> defining_polynomial(x)),
                             :discriminant => (ZZRingElem, x -> discriminant(maximal_order(x))),
                             :signature => (Tuple{Int, Int}, x -> signature(x)),
                             :class_number => (ZZRingElem, x -> order(class_group(maximal_order(x))[1])),
                             :class_group => (Vector{ZZRingElem}, x -> elementary_divisors(class_group(maximal_order(x))[1])),
                             :is_cm => (Bool, x -> is_cm_field(x)[1]),
                             :relative_class_number => (ZZRingElem, x -> begin
                                                          fl, tau = is_cm_field(x)
                                                          @assert fl
                                                          k, mk = fixed_field(x, tau)
                                                          hk = order(class_group(lll(maximal_order(k)))[1])
                                                          hK = order(class_group(maximal_order(x))[1])
                                                          @assert mod(hK, hk) == 0
                                                          return divexact(hK, hk)
                                                        end),
                              :is_normal => (Bool, x -> is_normal(x)),
                              :automorphism_group => (Tuple{Int, Int}, x -> find_small_group(automorphism_group(x)[1])[1]),
                              :regulator => (ArbFieldElem, x -> regulator(maximal_order(x))),
                              :lmfdb_label => (String, x -> ""),
                              :is_abelian => (Bool, x -> is_abelian(automorphism_group(x)[1])),
                              :non_simple => (Vector{QQPolyRingElem}, x -> non_simple_extension(x)),
                              :galois_group => (Tuple{Int, Int}, x -> error()),
                              :p_adic_regulator => (Dict{ZZRingElem, QQFieldElem}, (x, y) -> _p_adic_regulator(x, y)))


for (k, v) in properties_comp
  @eval ($k)(D::NFDBRecord) = D[Symbol($k)]::($(v[1]))
end

Base.getindex(D::NFDBRecord, s, x...) = getindex(D.data, s, x...)

properties(D::NFDBRecord) = collect(keys(D.data))

function field(D::NFDBRecord; cached = false)
  if isdefined(D, :K)
    return D.K
  else
    f = D[:poly]
    K, a = number_field(f, "a", cached = false)
    if cached
      D.K = K
    end
    return K
  end
end

function setindex!(D::NFDBRecord, s, k::Symbol, x...)
  if !(k in record_info_v1.name_tuples)
    error("asdsD")
  end
  if haskey(D.data, k)
    if k !== :p_adic_regulator || (k === :p_adic_regulator && haskey(D.data[k], x...))
      error("Data for $k already exists")
    end
  end

  if (k === :p_adic_regulator && !(s isa Union{Integer, Rational{<:Integer}, QQFieldElem})) || (k !== :p_adic_regulator! && (s isa properties_comp[k][1]))
    error("$s has the wrong type (expected $(properties_comp[k][1]))")
  end

  if k === :p_adic_regulator
    if haskey(D.data, k)
      @assert !haskey(D.data[k], x)
      D.data[k][x...] = s
    else
      D.data[k] = Dict{ZZRingElem, QQFieldElem}(x... => s)
    end
  else
    D.data[k] = s
  end
  return D
end

function compute!(D::NFDBRecord, s::Symbol, x...)
  if haskey(D.data, s)
    if s === :p_adic_regulator && haskey(D.data[s], x)
      return D.data[s][x]
    elseif s !== :p_adic_regulator
      return D.data[s]
    end
  end
  K = field(D)
  d = _get(K, s, x...)
  if s === :p_adic_regulator
    if haskey(D.data, :p_adic_regulator)
      D.data[s][x...] = d
    else
      D.data[s] = Dict{ZZRingElem, QQFieldElem}(x... => d)
    end
  else
    D.data[s] = d
  end
  return d
end

function compute!(D::NFDB, S::Vector)
  for s in S
    compute!(D, s)
  end
end

function compute!(D::NFDB, s::Symbol, x...)
  #PB = Pkg.GitTools.MiniProgressBar(header = "Computing $s")
  #PB.max = length(D.fields)
  #rate = 0.0
  #length_eta = 0
  for i in 1:length(D.fields)
    compute!(D[i], s, x...)
    #PB.current = i
    #Pkg.GitTools.showprogress(stdout, PB)#ETA)
    #flush(stdout)
  end
end

# You may add stuff at the end
const record_info_v1 = NFDBRecordInfo([:id,
                                       :poly,
                                       :polredabs,
                                       :deg,
                                       :discriminant,
                                       :signature,
                                       :class_number,
                                       :class_group,
                                       :regulator,
                                       :is_cm,
                                       :relative_class_number,
                                       :is_tamely_ramified,
                                       :is_normal,
                                       :automorphism_group,
                                       :lmfdb_label,
                                       :is_abelian,
                                       :non_simple,
                                       :galois_group,
                                       :p_adic_regulator])


@assert length(record_info_v1.name_tuples) <= 56

function Base.write(io::IO, D::NFDBRecord{1})
  o = zero(UInt64)
  i = 1
  j = 0
  for d in record_info_v1.name_tuples
    o = _set_flag(o, i, haskey(D.data, d))
    if haskey(D.data, d)
      j += 1
    end
    i += 1
  end
  o = _set_version(o, UInt8(1))

  print(io, repr(o))
  print(io, ",")

  m = 0
  for d in record_info_v1.name_tuples
    if haskey(D.data, d)
      m += 1
      print(io, _stringify(D.data[d]))
      if m < j
        print(io, ",")
      end
    end
  end
  return nothing
end

Base.haskey(D::NFDBRecord, s::Symbol) = haskey(D.data, s)

function Base.get(D::NFDBRecord{1}, s::Symbol)
  if haskey(D, s)
    return D.data[s]
  else
    return missing
  end
end

function _get(K, s, x...)
  if haskey(properties_comp, s)
    return (properties_comp[s][2])(K, x...)
  else
    error("Invalid property :$(s) of number field")
  end
end

function _create_record(K::AbsSimpleNumField; compute = [], keep_field = true)
  f = defining_polynomial(K)
  data = Dict{Symbol, Any}()
  data[:poly] = f
  data[:signature] = signature(f)
  data[:deg] = degree(f)
  for p in compute
    c = _get(K, p)
    data[p] = c
  end
  D = NFDBRecord{1}(data)
  if keep_field
    D.K = K
  end
  return D
end

# 1 <= i <= 56
_get_flag(flags::UInt, i::Int; offset = 0) = Bool((flags >> (offset + i - 1)) & 1)

# 1 <= i <= 56
function _set_flag(flags::UInt, i::Int, b::Bool; offset = 0)
  if b
    return flags | 1 << (offset + i - 1)
  else
    return flags & ~(1 << (offset + i - 1))
  end
end

_get_version(flags::UInt) = (flags >> 56) % UInt8

_set_version(flags::UInt, v::UInt8) = flags |= (UInt(v) << 56)

_parse_as(x) = x

_parse_as(::Type{QQPolyRingElem}) = Vector{QQFieldElem}

_parse_as(::Type{Vector{QQPolyRingElem}}) = Vector{Vector{QQFieldElem}}

_parse_as(::Type{Dict{ZZRingElem, QQFieldElem}}) = Vector{Tuple{ZZRingElem, QQFieldElem}}

create(::Type{QQPolyRingElem}, v::Vector{QQFieldElem}) = Hecke.Globals.Qx(v)

create(::Type{Vector{QQPolyRingElem}}, v::Vector{Vector{QQFieldElem}}) = [ Hecke.Globals.Qx(w) for w in v]

create(::Type{Dict{ZZRingElem, QQFieldElem}}, v::Vector{Tuple{ZZRingElem, QQFieldElem}}) = Dict{ZZRingElem, QQFieldElem}(w[1] => w[2] for w in v)

create(T, v) = v

function _stringify(x::Dict{ZZRingElem, QQFieldElem})
  return replace(_stringify([(k, v) for (k, v) in x]), " " => "")
end

function _stringify(x::QQPolyRingElem)
  return _stringify([coeff(x, i) for i in 0:degree(x)])
end

function _stringify(x::Vector{T}) where {T}
  if isempty(x)
    return "[]"
  end
  s = "["
  for i in 1:(length(x) - 1)
    s = s * _stringify(x[i]) * ","
  end
  s = s * _stringify(x[end]) * "]"
  return s
end

_stringify(x::Tuple{Int, Int}) = string(x)

_stringify(x) = string(x)

_stringify(x::ArbFieldElem) = _string(x)

function _stringify(x::NumFieldElem)
  return _stringify.(coordinates(x))
end

function _stringify(x::PolyRingElem)
  return _stringify([_stringify(coeff(x, i)) for i in 0:degree(x)])
end

function get_record(io::IO)
  data = Dict{Symbol, Any}()
  b, v  = _parse(UInt, io)
  ver = _get_version(v)
  @assert ver == 1
  b = Base.read(io, UInt8)
  for (i, s) in enumerate(record_info_v1.name_tuples)
    if !_get_flag(v, i)
      continue
    end
    T = properties_comp[s][1]
    S = _parse_as(T)
    z = _parse(S, io, b)
    b, d = z
    dd = create(T, d)
    data[s] = dd

    if eof(io)
      break
    end
    while !eof(io) && b == UInt8(' ')
      b = Base.read(io, UInt8)
    end
    @assert b == UInt8(',')
    b = Base.read(io, UInt8)
  end
  return NFDBRecord{Int(ver)}(data)
end

function _parse(::Type{Bool}, io, start = Base.read(io, UInt8))
  if start == UInt8('t')
    fl = true
  elseif start == UInt8('f')
    fl = false
  else
    error("Not possible")
  end
  if eof(io)
    b = UInt8(255)
  else
    b = Base.read(io, UInt8)
  end
  return b, fl
end

# I am too lazy for UInt
function _parse(::Type{UInt}, io, start = Base.read(io, UInt8))
  n = IOBuffer()
  b = start
  while !eof(io) && b == UInt8(' ')
    b = Base.read(io, UInt8)
  end

  @assert b == UInt('0')
  b = Base.read(io, UInt8)
  @assert b == UInt('x')
  b = Base.read(io, UInt8)

  lo = UInt8('0')
  up = UInt8('9')
  lo2 = UInt8('a')
  up2 = UInt8('f')

  while (lo <= b <= up) || (lo2 <= b <= up2)
    Base.write(n, b)
    if eof(io)
      b = UInt8(255)
      break
    end
    b = Base.read(io, UInt8)
  end

  nu = String(take!(n))

  num = parse(UInt, nu, base = 16)

  return b, num
end

function _parse(::Type{Int}, io, start = Base.read(io, UInt8))
  w = UInt8(' ')
  b = start
  while !eof(io) && b == w
    b = Base.read(io, UInt8)
  end
  exp = 10
  res = 0
  neg = false
  if b == UInt8('-')
    neg = true
    b = Base.read(io, UInt8)
  end
  lo = UInt8('0')
  up = UInt8('9')

  if !(lo <= b <= up)
    error("Not a number")
  end

  while !eof(io) && lo <= b <= up
    res = res * exp + (b - lo)
    b = Base.read(io, UInt8)
  end
  if neg
    res = -res
  end
  return b, res
end

function _parse(::Type{String}, io, start = Base.read(io, UInt8))
  b = start
  res = IOBuffer()
  @assert b == UInt8('"')
  b = Base.read(io, UInt8)
  while b != UInt8('"')
    Base.write(res, b)
    b = Base.read(io, UInt8)
  end

  if eof(io)
    b = UInt8(255)
  else
    b = Base.read(io, UInt8)
  end

  return b, String(take!(res))
end

function _parse(::Type{Vector{T}}, io, start = Base.read(io, UInt8)) where {T}
  res = T[]
  w = UInt8(' ')
  b = start
  while !eof(io) && b == w
    b = Base.read(io, UInt8)
  end
  @assert b == UInt8('[')
  b = Base.read(io, UInt8)
  while !eof(io) && b == w
    b = Base.read(io, UInt8)
  end
  while b != UInt8(']')
    b, q = _parse(T, io, b)
    push!(res, q)
    if b == UInt8(']')
      break
    end
    while !eof(io) && b == w
      b = Base.read(io, UInt8)
    end
    b = Base.read(io, UInt8)
    while !eof(io) && b == w
      b = Base.read(io, UInt8)
    end
  end
  if eof(io)
    b = UInt8(255)
  else
    b = Base.read(io, UInt8)
  end
  return b, res
end

function _parse(::Type{ZZRingElem}, io, start = Base.read(io, UInt8))
  n = IOBuffer()
  b = start
  while !eof(io) && b == UInt8(' ')
    b = Base.read(io, UInt8)
  end
  lo = UInt8('0')
  up = UInt8('9')
  mi = UInt8('-')

  if !((lo <= b <= up) || b == mi)
    error("Not a number")
  end

  while (lo <= b <= up) || b == mi
    Base.write(n, b)
    if eof(io)
      b = UInt8(255)
      break
    end
    b = Base.read(io, UInt8)
  end

  nu = String(take!(n))

  if length(nu) < 18
    num = ZZRingElem(parse(Int, nu))
  else
    num = parse(ZZRingElem, nu)
  end

  return b, num
end

function _parse(::Type{QQFieldElem}, io, start = Base.read(io, UInt8))
  n = IOBuffer()
  d = IOBuffer()
  read_den = false
  b = start
  lo = UInt8('0')
  up = UInt8('9')
  mi = UInt8('-')
  while ((lo <= b <= up) || b == mi || (!read_den && b == UInt('/')))
    if b == UInt8('/')
      read_den = true
      skip(io, 1)
      @goto read
    end

    if !read_den
      Base.write(n, b)
    else
      Base.write(d, b)
    end

    @label read
    if eof(io)
      b = UInt8(255)
      break
    end
    b = Base.read(io, UInt8)
  end

  nu = String(take!(n))

  if length(nu) < 18
    num = ZZRingElem(parse(Int, nu))
  else
    num = parse(ZZRingElem, nu)
  end

  if !read_den
    return b, QQFieldElem(num)
  else
    de = String(take!(d))
    if length(de) < 18
      den = ZZRingElem(parse(Int, de))
    else
      den = parse(ZZRingElem, de)
    end
    return b, num//den
  end
end

function _parse(::Type{Tuple{Int, Int}}, io, start = Base.read(io, UInt8))
  w = UInt8(' ')
  b = start
  while !eof(io) && b == w
    b = Base.read(io, UInt8)
  end
  @assert b == UInt8('(')
  b, x1 = _parse(Int, io)
  while !eof(io) && b == UInt8(' ')
    b = Base.read(io, UInt8)
  end
  @assert b == UInt8(',')
  b, x2 = _parse(Int, io)
  @assert b == UInt8(')')
  if eof(io)
    return UInt8(255), (x1, x2)
  else
    b = Base.read(io, UInt8)
  end
  return b, (x1, x2)
end

function _parse(::Type{Tuple{S, T}}, io, start = Base.read(io, UInt8)) where {S, T}
  w = UInt8(' ')
  b = start
  while !eof(io) && b == w
    b = Base.read(io, UInt8)
  end
  @assert b == UInt8('(')
  b, x1 = _parse(S, io)
  while !eof(io) && b == UInt8(' ')
    b = Base.read(io, UInt8)
  end
  @assert b == UInt8(',')
  b, x2 = _parse(T, io)
  @assert b == UInt8(')')
  if eof(io)
    return UInt8(255), (x1, x2)
  else
    b = Base.read(io, UInt8)
  end
  return b, (x1, x2)
end

function perm_from_string(s)
  c, p = AbstractAlgebra.Generic.parse_cycles(s)
  if length(c) == 0
    n = 1
  else
    n = maximum(c)
  end
  cdec = AbstractAlgebra.Generic.cycledec(c, p, n)
  return SymmetricGroup(cdec.cptrs[end]-1)(cdec)
end

function _parse(::Type{Perm{Int}}, io, start = Base.read(io, UInt8))
  b = start
  @assert b == UInt8('p')
  b = Base.read(io, UInt8)
  @assert b == UInt8('e')
  b = Base.read(io, UInt8)
  @assert b == UInt8('r')
  b = Base.read(io, UInt8)
  @assert b == UInt8('m')
  b = Base.read(io, UInt8)
  @assert b == UInt8('"')
  b = Base.read(io, UInt8)
  res = IOBuffer()
  while b != UInt8('"')
    Base.write(res, b)
    b = Base.read(io, UInt8)
  end

  if eof(io)
    b = UInt8(255)
  else
    b = Base.read(io, UInt8)
  end

  return b, perm_from_string(String(take!(res)))
end

function _parse(::Type{ArbFieldElem}, io, start = Base.read(io, UInt8))
  n = IOBuffer()
  b = start
  while !eof(io) && b == UInt8(' ')
    b = Base.read(io, UInt8)
  end

  while b != UInt8(']')
    Base.write(n, b)
    if eof(io)
      b = UInt8(255)
      break
    end
    b = Base.read(io, UInt8)
  end
  nu = String(take!(n))

  RR = ArbField(64)

  if eof(io)
    b = UInt8(255)
  else
    b = Base.read(io, UInt8)
  end

  return b, RR(nu)
end

function _string(a::ArbFieldElem)
  s = string(a)
  if s[1] != '['
    s = "[" * s * "]"
  end
  return s
end

function _stringify(a::Bool)
  if a
    return "t"
  else
    return "f"
  end
end

function Base.show(io::IO, D::NFDB)
  k = length(D.meta)
  if k == 0
    println(io, "Number field table no metadata")
  else
    println(io, "Number field table with metadata:")
  end

  for (i, (p, e)) in enumerate(D.meta)
    print(io, p, ": ", e)
    print(io, "\n")
  end

  print(io, "Data present: ")
  for (s, i) in D.prop
    if i == 1
      print(io, s, ", ")
    elseif i == 1
      print(io, "(", s, "), ")
    end
  end
  println(io)

  print(io, "No. fields: ", length(D.fields))
end

function Base.show(io::IO, D::NFDBRecord)
  println(io, "Number field record with data:")
  for (p, e) in D.data
    print(io, p, ": ", e)
    print(io, "\n")
  end
end

function Base.write(f::String, D::NFDB)
  if isfile(f)
    error("File $f already exists. Please move first")
  end
  open(f, "w") do io
    Base.write(io, D)
  end
end

function Base.write(io::IO, D::NFDB)
  for (p, e) in D.meta
    print(io, "# ", p, ":", e, "\n")
  end
  for i in 1:length(D.fields)
    Base.write(io, D.fields[i])
    print(io, "\n")
  end
end

Base.getindex(D::NFDB, i::Int) = D.fields[i]

Base.eltype(::Type{NFDB{T}}) where {T} = NFDBRecord{T}

function Base.read(file::String, ::Type{NFDB})
  metadata = Dict()
  f = open(file)
  head = 0
  local line
  while !eof(f)
    line = readline(f)
    if line[1] == '#'
      head += 1
      if !(':' in line)
        continue
      end
      i = 2
      while line[i] != ':'
        i += 1
      end
      key = Symbol(strip(line[2:i-1]))
      val = strip(line[i+1:end])
      metadata[key] = val
    else
      break
    end
  end
  DB = NFDB{1}()
  if line[1] != '#'
    D = get_record(IOBuffer(line))
    push!(DB.fields, D)
    while !eof(f)
      line = readline(f)
      D = get_record(IOBuffer(line))
      push!(DB.fields, D)
    end
  end
  close(f)
  DB.meta = metadata

  update_properties!(DB)

  return DB
end

function _latexify(f::QQPolyRingElem, dollar = true)
  if dollar
    return "\$" * AbstractAlgebra.obj_to_latex_string(f) * "\$"
  else
    return AbstractAlgebra.obj_to_latex_string(f)
  end
end

function _latexify(fs::Vector{QQPolyRingElem})
  s = IOBuffer()
  print(s, "\$")
  for i in 1:length(fs)
    print(s, _latexify(fs[i], false))
    if i < length(fs)
      print(s, ", ")
    end
  end
  print(s, "\$")
  return String(take!(s))
end

_latexify(a::ZZRingElem) = AbstractAlgebra.obj_to_latex_string(a)

_latexify(a::Int) = AbstractAlgebra.obj_to_latex_string(a)

_latexify(a::Tuple{Int, Int}) = string(a)

function latex_table(d::NFDBRecord; entries = [:deg, :automorphism_group, :poly, :non_simple, :class_number, :discriminant], mpage_for_poly = true)
  io = IOBuffer()
  for i in 1:length(entries)
    if entries[i] == :discriminant
      print(io, _latexify(factor(d[entries[i]]), withnumber = false, approx = false))
    elseif entries[i] == :poly
      if mpage_for_poly
        print(io, "\\begin{minipage}{4cm}\\begin{center}\n\$\n\\begin{aligned}\n")
        print(io, _latexify(d[entries[i]], false))
        print(io, "\n\\end{aligned}\n\$\n\\end{center}\\end{minipage}\n")
      else
        print(io, _latexify(d[entries[i]]))
      end
    else
      print(io, _latexify(d[entries[i]]))
    end
    if i < length(entries)
      print(io, " & ")
    end
  end
  print(io, "\\\\")
  return String(take!(io))
end

function latex_table(D::NFDB; entries = [:deg, :automorphism_group, :poly, :non_simple, :class_number, :discriminant])
  io = IOBuffer()
  for d in D
    print(io, latex_table(d, entries = entries))
    print(io, "\n")
  end
  return String(take!(io))
end

function _latexify(f::Fac{ZZRingElem}; withnumber = true, approx = true, cdot = false, sign = true)
  l = Tuple{ZZRingElem, Int}[(p, e) for (p, e) in f]
  sort!(l, by = x -> x[1])
  if length(l) == 0
    return "\$1\$"
  end
  m = prod([p^e for (p, e) in f]) * unit(f)
  if withnumber
    s = "\$ $m = "
  else
    s = "\$"
  end
  if sign && m < 0
    s = s * "-"
  end
  for i in 1:(length(l) - 1)
    if l[i][2] == 1
      s = s * "$(l[i][1])\\cdot "
    else
      if cdot
        s = s * "$(l[i][1])^{$(l[i][2])} \\cdot "
      else
        s = s * "$(l[i][1])^{$(l[i][2])} "
      end
    end
  end
  if l[end][2] == 1
    s = s * "$(l[end][1])"
  else
    s = s * "$(l[end][1])^{$(l[end][2])}"
  end
  if approx
    s = s * "\\approx " * (m < 0 ? "-" : "") * "10^{$(Int(ceil(log(10, abs(m) * 1.0))))}"
  end
  s = s * "\$"
  return s
end

################################################################################
#
#    Merge
#
################################################################################

function Base.merge!(R::NFDB{1}, D1::NFDB{1}; skip_update = false)
  sizehint!(R.fields, length(R) + length(D1))
  append!(R.fields, D1.fields)
  if !skip_update
    update_properties!(R)
  end
  return R
end

function Base.merge(D1::NFDB{1}, D2::NFDB{1})
  D3 = NFDB{1}()
  merge!(D3, D1)
  merge!(D3, D2)
  return D3
end

function Base.merge(D::Vector{NFDB{1}})
  if length(D) == 1
    return D
  end

  R = NFDB{1}()
  sizehint!(R.fields, sum(length(d) for d in D))
  for i in 1:length(D)
    merge!(R, D[i], skip_update = true)
  end

  update_properties!(R)

  return R
end

# should call update_properties! afterwards
function unsafe_add!(DB::NFDB, K::AbsSimpleNumField)
  D = _create_record(K, keep_field = false)
  push!(DB.fields, D)
  return D
end

names32 = [ "C32", "C2.C4^2", "C4*C8", "C2.OD16", "C2^2:C8", "C2^2.D4",
           "C2^3.C4", "OD16.C2", "D4:C4", "Q8:C4", "C4wrC2", "C4:C8", "C8:C4",
           "C2.D8", "C8.C4", "C2*C16", "OD32", "D16", "SD32", "Q32", "C2*C4^2",
           "C2*C2^2:C4", "C2*C4:C4", "(C2*C4):C4", "C4*D4", "C4*Q8",
           "C2^2wrC2", "C2^2:D4", "C2^2:Q8", "(C2^2*C4):C2", "C4.D4", "C4.Q8",
           "C4^2:C2", "C4:D4", "C4:Q8", "C2^2*C8", "C2*OD16", "OD16:C2",
           "C2*D8", "C2*SD16", "C2*Q16", "D8:C2", "C8:C2^2", "SD16:C2",
           "C2^3*C4", "C2^2*D4", "C2^2*Q8", "C2*D4:C2", "Q8:C2^2", "C4.C2^3",
           "C2^5" ]

names64 = [ "C64", "C8^2", "C8:C8", "C2^3:C8", "(C2*C4):C8", "D4:C8", "Q8:C8",
           "C2^2.SD16", "C2.(C2^2.D4)", "C2.(C2^3.C4)", "C2.C4wrC2", "C4.D8",
           "C4.Q16", "C2.Q8:C4", "C2.C8:C4", "C2.(C2.D8)", "C2.(C4*C8)",
           "(C2*OD16).C2", "C2^3.Q8", "(C2*C4).D4", "C2.D4:C4", "OD16.C4",
           "C2^2:C4:C4", "OD16:C4", "(C2*C8):C4", "C4*C16", "C2.OD32",
           "OD32.C2", "C2^2:C16", "C2^3.C8", "D4.C8", "C2wrC4", "(C2^2*C4):C4",
           "C4^2:C4", "C2^2.D4.C2", "(OD16.C2):C2", "OD16.C2.C2", "C2^2.D8",
           "C2.Q32", "D8.C4", "OD32:C2", "(C2*D8).C2", "Q16.C4", "C4:C16",
           "C8.C8", "C16:C4", "C2.D16", "C2.SD32", "C16.C4", "C2*C32", "OD64",
           "D32", "SD64", "Q64", "C4^3", "C2*C2.C4^2", "C4.C4^2", "C4*C2^2:C4",
           "C4*C4:C4", "C2^5.C2", "(C2^3*C4).C2", "C2^2.(C2*D4)", "C4.C4:C4",
           "C2.C4^2.C2", "C2.C4:Q8", "C2^2:(C4:C4)", "C2^3.D4", "C4:C4:C4",
           "C2^4.C2^2", "C4:(C4:C4)", "C4:(C2^2:C4)", "C2.(C4*Q8)", "C2.C4:D4",
           "C2.(C4.D4)", "(C2^2*D4).C2", "(C2^2*Q8).C2", "(C2.C4^2):C2",
           "C2.C4^2:C2", "(C2*C4).Q8", "C2^2.(C2*Q8)", "C2.C2^2:Q8",
           "C2^2.D4:C2", "C2*C4*C8", "C2*C2.OD16", "C4*OD16", "C2.(C2*C4^2)",
           "C2*C2^2:C8", "C2^2:OD16", "(C2^2*C8):C2", "C2*C2^2.D4",
           "(C2*D4):C4", "C2*C2^3.C4", "C2*OD16.C2", "(C2^3.C4):C2",
           "C2*D4:C4", "C2*Q8:C4", "D4:C2:C4", "Q8:(C2*C4)", "(C2*C8):C2^2",
           "(C2*Q8):C4", "C2*C4wrC2", "OD16:C2^2", "C2*C4:C8", "C4:OD16",
           "(C2^2*C8).C2", "C2*C8:C4", "C2*C2.D8", "C8.(C2*C4)", "C8:(C2*C4)",
           "C2*C8.C4", "(C8.C4):C2", "C4.OD16", "C4^2.C4", "C2^3.(C2*C4)",
           "C8*D4", "C2.(C4*D4)", "(C2*D4).C4", "C4*D8", "C4*SD16", "C4*Q16",
           "SD16:C4", "Q16:C4", "D8:C4", "(C4*C8):C2", "OD16:C2:C2", "C8*Q8",
           "(C2*Q8).C4", "(C2*D8):C2", "C2.(C2*SD16)", "C4:C4.C2^2",
           "(C2*Q8):C2^2", "C2^2:Q16", "(C2*Q16):C2", "D4:D4", "C4wrC2:C2",
           "D4.D4", "C2.C2^2wrC2", "C2wrC2^2", "(C2^2.D4):C2", "C4:D8",
           "C4:D4.C2", "(C2*SD16).C2", "C4:Q16", "(C2*SD16):C2", "C4:C8:C2",
           "C2^2:SD16", "C2^2:D8", "(C2.D8):C2", "C4.(C2*D4)", "C2.C8:C2^2",
           "C2^2:Q8.C2", "SD16:C2:C2", "C8:C2^2:C2", "Q8.D4", "D4:Q8", "Q8:Q8",
           "D4:C4.C2", "C2.(C2*Q16)", "D4.Q8", "Q8.Q8", "C2^2:C8:C2",
           "C2^2:D4.C2", "C2.D8:C2", "C2^2:C8.C2", "C2^2.Q16", "C8:C4:C2",
           "C4.SD16", "(C4*C8).C2", "Q8:C4:C2", "C4:Q8:C2", "D4:C4:C2",
           "(C2*C8).C2^2", "C4:SD16", "(C2*D4).C2^2", "(C2*Q16).C2", "C8.D4",
           "C8:D4", "(C2.OD16):C2", "C8:Q8", "C8.Q8", "C2.(C2*D8)", "C8:C4.C2",
           "C2^2*C16", "C2*OD32", "C16.C2^2", "C2*D16", "C2*SD32", "C2*Q32",
           "D16:C2", "C16:C2^2", "Q32:C2", "C2^2*C4^2", "C2^2*C2^2:C4",
           "C2^2*C4:C4", "C2*(C2*C4):C4", "C2*C4*D4", "C2*C4*Q8", "C4*D4:C2",
           "C2^3:(C2*C4)", "C2.(C2^3*C4)", "D4:(C2*C4)", "C2*C2^2wrC2",
           "C2*C2^2:D4", "C2*C2^2:Q8", "C2*(C2^2*C4):C2", "C4^2:C2^2",
           "C2*C4.D4", "C2*C4.Q8", "C2*C4^2:C2", "(C2*C4^2):C2", "C2*C4:D4",
           "C2*C4:Q8", "(C2*C4):D4", "(C2*C4^2).C2", "C2^4:C2^2",
           "(C2^2*D4):C2", "(C2^2*Q8):C2", "C2.(C2^2*D4)", "C2.Q8:C2^2",
           "(C4*D4):C2", "C4:D4:C2", "(C4*Q8):C2", "C4^2:C2:C2", "C2^3:Q8",
           "(C2*C4):Q8", "D4^2", "(C2*D4):C2^2", "C4:(D4:C2)", "C2^2:(D4:C2)",
           "D4*Q8", "Q8:D4", "C2^2wrC2.C2", "(C4.Q8):C2", "C4^2.C2^2",
           "(C4*D4).C2", "(C4.D4):C2", "(C2*Q8).C2^2", "(C4*Q8).C2", "Q8^2",
           "C2^3.C2^3", "(C2*C4).C2^3", "C2^2wrC2:C2", "C2^2:D4:C2",
           "C2^2:Q8:C2", "C2^2.C2^4", "C2^3*C8", "C2^2*OD16", "C2*OD16:C2",
           "(C2*OD16):C2", "C2^2*D8", "C2^2*SD16", "C2^2*Q16", "C2*D8:C2",
           "C2*C8:C2^2", "C2*SD16:C2", "SD16:C2^2", "C8.C2^3", "C4.C2^4",
           "D10.C2^2", "C2^4*C4", "C2^3*D4", "C2^3*Q8", "C2^2*D4:C2",
           "C2*Q8:C2^2", "C2*C4.C2^3", "D4.C2^3", "C2^6" ]

function has_obviously_relative_class_number_not_one(K::AbsSimpleNumField, is_normal::Bool = true, maxdeg::Int = degree(K))
  if is_normal
    subs = subfields_normal(K)
  else
    subs = subfields(K)
  end

  sort!(subs, by = x -> degree(x[1]))

  for (L, mL) in subs
    if degree(L) > min(degree(K) - 1, maxdeg)
      continue
    end
    fl, tau = is_cm_field(L)
    if !fl
      continue
    end

    l = fixed_field(L, tau)[1]

    h = order(class_group(lll(maximal_order(L)))[1])
    hp = order(class_group(lll(maximal_order(l)))[1])
    @assert mod(h, hp) == 0
    hm = divexact(h, hp)
    if hm == 3 || hm > 4
      return true, L
    end
  end
  return false, K
end

################################################################################
#
#  Iterator interface
#
################################################################################

function Base.iterate(D::NFDB, i = 1)
  if i > length(D)
    return nothing
  end
  return D[i], i + 1
end

################################################################################
#
#  p-adic regulator
#
################################################################################

function _p_adic_regulator(K::AbsSimpleNumField, p::IntegerUnion)
  return _p_adic_regulator_coates(K, p)
end

function _p_adic_regulator_coates(K::AbsSimpleNumField, p::IntegerUnion)
  # Implementation due to Scheima Obeidi, 2024
  degK = degree(K)
  if degK == 1 # rationals
    return zero(QQ)
  end
  @req is_totally_real(K) "Field must be totally real"
  OK = ring_of_integers(K)
  dp = prime_ideals_over(OK, p)
  U, mU = unit_group_fac_elem(OK)
  rK = torsion_free_rank(U)
  EK = [mU(U[j]) for j in 2:(rK + 1)]
  push!(EK, FacElem(K(1+p))) # put 1+p in list with fundamental units
  prec = degK + 20 # precision for working Qp
  working_prec = prec + 20
  # The precision management:
  #
  # prec = precision of Qp/Zp, this is where the determinant of the matrix
  #        eventually resides. Might be zero, if prec < v(reg_p(K))
  #
  # working_prec = precision for the completion map (this does not guarentee
  #                the precision of the output)
  #
  # There are some gotos, because we need to distinguish low prec and low
  # working_prec.
  while true
    (prec > 2^12 || working_prec > 2^12) && error("Something wrong")
    imK =[LocalFieldValuationRingElem{PadicField, PadicFieldElem}[] for i in 1:degK]
    Qp = padic_field(p, precision = prec, cached = false)
    Zp = ring_of_integers(Qp)
    dK = discriminant(OK)
    r = maximum([ramification_index(P) for P in dp])
    ims = [[] for i in 1:degK]
    # In general  [LocalFieldElem{QadicFieldElem, EisensteinLocalField}[] for i in 1:degK]
    # In the easy case [QadicFieldElem[] for i in 1:degK]
    #
    # Compute the logarithm of all elements under all embeddings
    # We need a working precision independent of prec
    while length(ims[rK + 1]) < length(dp) # while not everything is filled
      empty!.(ims)
      for j in 1:length(dp)
        local C, mC
        try
          C, mC = completion_easy(K, dp[j], working_prec)
        catch e
          if !(e isa ErrorException && e.msg == "cannot deal with difficult primes yet")
            rethrow()
          end
          C, mC = completion(K, dp[j], working_prec)
        end
        for i in 1:(rK+1)
          try
            # the evaluation of the logarithm may fail, if the precision
            # is not high enough
            el = _evaluate_log_of_fac_elem(mC, dp[j], EK[i])
            if is_zero(el)
              @goto bad_working_prec
            end
            push!(ims[i], el)
          catch e
            if !(e isa ErrorException && e.msg == "precision too low")
              rethrow()
            end
            @goto bad_working_prec
          end
        end
      end
    end

    m = 0
    mj = minimum(QQFieldElem[valuation(ims[i][j]) for i in 1:length(ims) for j in 1:length(dp)])
    if mj >= 0
      m = zero(QQ)
    else
      m = mj
    end

    for i in 1:(rK+1)
      for j in 1:length(ims[i])
        OC = ring_of_integers(parent(ims[i][j]))
        try
          w = absolute_coordinates(Zp, OC(ims[i][j]*p^(Int(-m*r)))) #coates
          append!(imK[i], w)
        catch e
          if e isa ErrorException && startswith(e.msg, "Precision of field")
            @goto bad_working_prec
          else
            rethrow(e)
          end
        end
      end
    end
    X = matrix(Zp, imK)
    dX = AbstractAlgebra.det_df(X)
    if is_zero(dX)
      @goto bad_prec
    end
    vp = valuation(AbstractAlgebra.det_df(X))
    vp = vp +  m*r*degK + valuation(dK, p)//2 - 1
    return vp

    @label bad_prec
    prec = 2 * prec
    #@info "Increasing prec to $(prec)"
    working_prec = max(working_prec, prec + 20)
    continue

    @label bad_working_prec
    working_prec = 2 * working_prec
    #@info "Increasing working_prec to $(working_prec)"
    continue
  end
end

function _p_adic_regulator_normal(K, p, fast::Bool = false)
  OK = maximal_order(K)
  P = prime_ideals_over(OK, p)[1]
  U, mU = unit_group_fac_elem(OK)
  A, mA = automorphism_group(K)
  @req order(A) == degree(K) "Field must be normal"
  @req is_totally_real(K) "Field must be totally real"
  r = torsion_free_rank(U)
  prec = degree(K) + 10
  _det = Hecke.AbstractAlgebra.det_df
  while true
    if prec > 2^15
      error("Precision >= 2^15, something is wrong")
    end
    local C, mC
    if fast
      try
        C, mC = completion_easy(K, P, prec)
      catch e
        if !(e isa ErrorException && e.msg == "cannot deal with difficult primes yet")
          rethrow()
        end
        C, mC = completion(K, P, prec)
      end
    else
      C, mC = completion(K, P, prec)
    end
    Rmat = zero_matrix(C, r, r)
    D = Dict{AbsSimpleNumFieldElem, elem_type(C)}()
    good = true
    for i in 1:r
      for j in 1:r
        try
          Rmat[i, j] = _evaluate_log_of_fac_elem(mC, P, mA(A[i])(mU(U[j + 1])), D) # j + 1, because the fundamental units correspond to U[2],..,U[r + 1]
        catch e
          @show "asds"
          if !(e isa ErrorException && e.msg == "precision too low")
            rethrow()
          end
          good = false
          break
        end
      end
      if !good
        break
      end
    end
    if !good
      prec = 2*prec
      continue
    end
    z = _det(Rmat)
    if !is_zero(z)
      return valuation(z)
    else
      prec = 2*prec
    end
    if prec > 2^15
      error("Something wrong")
    end
  end
end

function _evaluate_log_of_fac_elem(mC, P, e::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, D = Dict{AbsSimpleNumFieldElem, elem_type(codomain(mC))}())
  C = codomain(mC)
  K = base_ring(e)
  pi = K(uniformizer(P))
  # We want to compute
  # sum(n * log(mC(pi^(-valuation(b, P)) * b)) for (b, n) in e; init = zero(C))
  # but we cache the result of the individual log(), since the elements we look
  # at have large intersection for their bases.
  #
  # At the moment log() works only for valuation == 0,
  # but since we have a unit, we can just scale in every factor
  res = zero(C)
  for (b, n) in e
    l = get!(D, b) do
      bb = mC(pi^(-valuation(b, P)) * b)
      if is_zero(bb)
        error("precision too low")
      end
      if bb isa QadicFieldElem
        return _log(bb)
      else
        return log(bb)
      end
    end
    res = res + n * l
  end
  return res
end

function _p_adic_regulator_non_normal(K, p)
  @req is_totally_real(K) "Field must be totally real"
  a = gen(K)
  N, KtoN = normal_closure(K)
  ON = maximal_order(N)
  P = prime_ideals_over(ON, p)[1]
  # first identify the distinct p-adic completions of K
  A, mA = automorphism_group(N)
  d = degree(N)
  prec = 32
  auts = Int[]
  while true
    empty!(auts)
    C, mC = completion(N, P, prec)
    images_of_primitive_element = elem_type(C)[]
    for i in 1:d
      z = mC(mA(A[i])(KtoN(a)))
      if z in images_of_primitive_element
        continue
      else
        push!(images_of_primitive_element, z)
        push!(auts, i)
      end
    end
    if length(images_of_primitive_element) == degree(K)
      break
    end
    prec = 2 * prec
  end

  OK = ring_of_integers(K)
  U, mU = unit_group_fac_elem(OK)
  r = torsion_free_rank(U)
  prec = 64
  _det = Hecke.AbstractAlgebra.det_df
  while true
    if prec > 2^15
      error("Precision >= 2^15, something is wrong")
    end
    C, mC = completion(N, P, prec)
    Rmat = zero_matrix(C, r, r)
    for i in 1:r
      for j in 1:r
        Rmat[i, j] = _evaluate_log_of_fac_elem(mC, P, mA(A[auts[i]])(KtoN(mU(U[j + 1])))) # j + 1, because the fundamental units correspond to U[2],..,U[r + 1]
      end
    end
    z = _det(Rmat)
    if !is_zero(z)
      return valuation(z)
    else
      prec = 2*prec
    end
  end
end

# Hack in some tables of relative fields

mutable struct NFDBRecordGeneric{T, S}
  data::Dict{Symbol, Any}
  K::S

  function NFDBRecordGeneric{T, S}(data) where {T, S}
    z = new{T, S}()
    z.data = data
    return z
  end
end

mutable struct NFDBGeneric{T, S}
  meta::Dict{Symbol, Any}
  fields::Vector{NFDBRecordGeneric{T, S}}
  prop::Vector{Tuple{Symbol, Int}} # 0 not, 1 there, 2 partial

   function NFDBGeneric{T, S}() where {T, S}
    z = new{T, S}()
    z.meta = Dict{Symbol, Any}()
    z.fields = NFDBRecordGeneric{T, S}[]
    return z
  end
end
   
function NFDBGeneric(L::Vector{RelSimpleNumField{AbsSimpleNumFieldElem}})
  res = NFDBGeneric{1, eltype(L)}()
  for K in L
    D = _create_record(K)
    push!(res.fields, D)
  end
  return res
end

function _create_record(K::RelSimpleNumField{AbsSimpleNumFieldElem}; keep_field = true)
  f = defining_polynomial(K)
  data = Dict{Symbol, Any}()
  data[:base_field_poly] = defining_polynomial(base_field(K))
  data[:poly] = f
  data[:deg] = degree(f)
  data[:absolute_discriminant] = norm(discriminant(maximal_order(K)))
  D = NFDBRecordGeneric{1, typeof(K)}(data)
  if keep_field
    D.K = K
  end
  return D
end

function Base.write(io::IO, D::NFDBRecordGeneric{1, RelSimpleNumField{AbsSimpleNumFieldElem}})
  m = 0
  prop = [:base_field_poly, :poly, :deg, :absolute_discriminant]
  j = length(prop)
  for d in prop
    if haskey(D.data, d)
      m += 1
      print(io, _stringify(D.data[d]))
      if m < j
        print(io, ",")
      end
    end
  end
  return nothing
end

function get_record_generic(io::IO)
  data = Dict{Symbol, Any}()
  b, v  = _parse(Vector{QQFieldElem}, io)
  @assert b == UInt8(',')
  f = Hecke.Globals.Qx(v)
  data[:base_field_poly] = f
  K, = number_field(f; cached = true)
  Kt, = polynomial_ring(K, "t", cached = false)
  b, v = _parse(Vector{Vector{QQFieldElem}}, io)
  poly = Kt([K(w) for w in v])
  data[:poly] = poly
  return NFDBRecordGeneric{1, RelSimpleNumField{AbsSimpleNumFieldElem}}(data)
end

function Base.write(io::IO, D::NFDBGeneric)
  for (p, e) in D.meta
    print(io, "# ", p, ":", e, "\n")
  end
  for i in 1:length(D.fields)
    Base.write(io, D.fields[i])
    print(io, "\n")
  end
end

function Base.show(io::IO, D::NFDBGeneric)
  k = length(D.meta)
  if k == 0
    println(io, "Number field table no metadata")
  else
    println(io, "Number field table with metadata:")
  end

  for (i, (p, e)) in enumerate(D.meta)
    print(io, p, ": ", e)
    print(io, "\n")
  end

  print(io, "No. fields: ", length(D.fields))
end

function Base.read(file::String, ::Type{NFDBGeneric})
  metadata = Dict()
  f = open(file)
  head = 0
  local line
  while !eof(f)
    line = readline(f)
    if line[1] == '#'
      head += 1
      if !(':' in line)
        continue
      end
      i = 2
      while line[i] != ':'
        i += 1
      end
      key = Symbol(strip(line[2:i-1]))
      val = strip(line[i+1:end])
      metadata[key] = val
    else
      break
    end
  end
  DB = NFDBGeneric{1, RelSimpleNumField{AbsSimpleNumFieldElem}}()
  if line[1] != '#'
    D = get_record_generic(IOBuffer(line))
    push!(DB.fields, D)
    while !eof(f)
      line = readline(f)
      D = get_record_generic(IOBuffer(line))
      push!(DB.fields, D)
    end
  end
  close(f)
  DB.meta = metadata
  return DB
end

function unsafe_add!(DB::NFDBGeneric, K)
  D = _create_record(K, keep_field = false)
  push!(DB.fields, D)
  return D
end

function add_meta!(D::NFDBGeneric, p::Pair)
  D.meta[p[1]] = p[2]
  return D
end

function get_meta!(D::NFDBGeneric, p::Symbol)
  if haskey(D.meta, p)
    return D.meta[p]
  else
    error("Information $p not found in metadata")
  end
end

