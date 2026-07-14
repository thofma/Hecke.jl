# Pxxxxs fro reconstruction from https://github.com/Thittho/Reconstruction/blob/main/magma/reconstruction_genus3.m
# With permission from Thomas
#
# useage: _G3_reconstruct_data_Pxxxx(inv) # inv must be a vector with length 13
const _default_g3_reconstruct_path = joinpath(artifact"Genus3ReconstructionData", "Genus3ReconstructionData", "data")

const _G3_reconstruct_data = Ref(Dict{Symbol, Any}())

const _G3_reconstruct_names = [:P11, :P12, :P13, :P21, :P22, :P23, :P31, :P32, :P33,
                       :P1111char17, :P1111nchar17,
                       :P1112char17, :P1112nchar17,
                       :P1113char17, :P1113nchar17,
                       :P1122char17, :P1122nchar17,
                       :P1123char17, :P1123nchar17,
                       :P1133char17, :P1133nchar17,
                       :P1222char17, :P1222nchar17,
                       :P1223char17, :P1223nchar17,
                       :P1233char17, :P1233nchar17,
                       :P1333char17, :P1333nchar17,
                       :P2222char17, :P2222nchar17,
                       :P2223char17, :P2223nchar17,
                       :P2233char17, :P2233nchar17,
                       :P2333char17, :P2333nchar17,
                       :P3333char17, :P3333nchar17]

function _load_G3_reconstruct_data()
  if !isempty(_G3_reconstruct_data[])
    return _G3_reconstruct_data[]
  end

  Qx,  = polynomial_ring(QQ,  [:I3, :I6, :I9, :J9, :I12, :J12, :I15, :J15, :I18, :J18, :I21, :J21, :I27])
  Zx,  = polynomial_ring(ZZ,  [:I3, :I6, :I9, :J9, :I12, :J12, :I15, :J15, :I18, :J18, :I21, :J21, :I27])

  open(_default_g3_reconstruct_path) do io
    for n in _G3_reconstruct_names
      s = Base.readuntil(io, '\n'; keep = false)
      @assert s == "#$n"
      _, Pc = _parse(Vector{QQFieldElem}, io)
      _, Pexp = _parse(Vector{Vector{Int}}, io)
      _, Plc = _parse(QQFieldElem, io)
      P = Plc * Qx(Pc, Pexp)
      if contains(String(n), "1c") || contains(String(n), "2c") || contains(String(n), "3c")
        _G3_reconstruct_data[][n] = map_coefficients(ZZ, P; parent = Zx)
      else
        _G3_reconstruct_data[][n] = P
      end
    end
  end
  _G3_reconstruct_data[]
end

for n in _G3_reconstruct_names
  fname = Symbol("_G3_reconstruct_data_$(n)")
  symb = QuoteNode(n)
  splitcase = false
  if contains(String(n), "1c") || contains(String(n), "2c") || contains(String(n), "3c")
    splitcase = true
    T = :ZZMPolyRingElem
  else
    T = :QQMPolyRingElem
  end
  @eval begin
    function ($fname)()
      return _load_G3_reconstruct_data()[$symb]::$T
    end
  end

  if splitcase
    basename = Symbol(:_G3_reconstruct_data_, String(split(String(n), "char17")[1]))
    mod17name = Symbol(basename, :char17)
    nmod17name = Symbol(basename, :nchar17)
    @eval begin
      function($basename)(inv)
        if characteristic(parent(inv[1])) == 17
          return evaluate($mod17name(), inv)
        else
          return evaluate($nmod17name(), inv)
        end
      end
    end
  else
    @eval begin
      function ($fname)(inv)
        return evaluate($fname(), inv)
      end
    end
  end
end


#function _parse_magma(f)
#  Qx,  = polynomial_ring(QQ,  [:I3, :I6, :I9, :J9, :I12, :J12, :I15, :J15, :I18, :J18, :I21, :J21, :I27])
#  I3,I6,I9,J9,I12,J12,I15,J15,I18,J18,I21,J21,I27 = gens(Qx)
#  f = replace(f, '/' => "//")
#
#  s = collect(readlines(IOBuffer(f)))
#  name = split(split(s[1], " ")[2], "(")[1]
#
#  if contains(f, "if Characteristic(Universe(inv)) eq 17 then")
#    head = split(f, "if Characteristic(Universe(inv)) eq 17 then")[1]
#    char17, body = split(split(f, "if Characteristic(Universe(inv)) eq 17 then")[2], "else")
#    char17 = String(split(char17, "return ")[2]);
#    char17 = reduce(*, collect(readlines(IOBuffer(char17))))
#    P = Main.eval(Meta.parse(char17))
#    println("#$(name)char17")
#    _parse_parse(P)
#    println(1)
#    s = readlines(IOBuffer(head * body))
#    #@info s
#    s = filter(x -> !startswith(x, "end if"), s)
#    filter!(x -> !isempty(x), s)
#    name = name * "nchar17"
#    #@info println(s)
#  end
#
#  lc = parse(Rational{BigInt}, String(split(split(s[end-1], "return ")[2], "*P")[1]))
#  s[3] = split(s[3], " := ")[2]
#  s = reduce(*, s[3:end-2])
#  P = Main.eval(Meta.parse(s))
#  P = P
#  println("#$name")
#  _parse_parse(P)
#  println(lc)
#  return P
#end
#
#function _parse_parse(P)
#  println(replace(replace(string(collect(coefficients(P))), " " => ""), "QQFieldElem" => ""))
#  println(replace(replace(string(collect(exponent_vectors(P))), " " => ""), "QQFieldElem" => ""))
#end
