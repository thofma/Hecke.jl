################################################################################
#
#  Embedding for QQ
#
################################################################################

struct QQEmb <: NumFieldEmb{QQField}
end

function Base.show(io::IO, ::QQEmb)
  if is_terse(io)
    print(io, "Complex embedding of QQ")
  else
    print(io, "Complex embedding of rational numbers")
  end
end

number_field(::QQEmb) = QQ

(::QQEmb)(x::Union{QQFieldElem, ZZRingElem}, prec::Int = 32) = ArbField(prec)(x)

real_embeddings(::QQField) = [QQEmb()]

complex_embeddings(::QQField) = [QQEmb()]

is_real(::QQEmb) = true

restrict(::NumFieldEmb, ::QQField) = QQEmb()

restrict(e::NumFieldEmb, f::NumFieldHom{QQField}) = QQEmb()

_embedding(::PosInf) = QQEmb()

evaluate(x::QQFieldElem, ::QQEmb, prec::Int = 32) = AcbField(prec)(x)

evaluate(x::ZZRingElem, ::QQEmb, prec::Int = 32) = AcbField(prec)(x)

is_positive(x::Union{ZZRingElem, QQFieldElem}, ::QQEmb) = x > 0

is_totally_positive(x::Union{ZZRingElem,QQFieldElem}) = x > 0

is_negative(x::Union{ZZRingElem, QQFieldElem}, ::QQEmb) = x < 0

sign(a::FacElem{QQFieldElem, QQField}) = prod(k -> Int(sign(k[1]))^(Int(k[2] % 2)), a, init = 1)

sign(::Type{Int}, a::FacElem{QQFieldElem}) = sign(a)

sign(x::QQFieldElem, ::QQEmb) = Int(sign(x))

sign(x::Union{ZZRingElem, FacElem{QQFieldElem}}, ::QQEmb) = sign(Int, x)

signs(x::Union{ZZRingElem, QQFieldElem, FacElem{QQFieldElem}}, ::Vector{QQEmb}) = Dict(QQEmb() => sign(x, QQEmb()))

signs(x::Union{ZZRingElem, QQFieldElem, FacElem{QQFieldElem}}) = Dict(QQEmb() => sign(x, QQEmb()))

complex_conjugation(K::QQField) = identity_map(K)
