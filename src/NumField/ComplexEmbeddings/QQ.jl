################################################################################
#
#  Embedding for QQ
#
################################################################################

struct QQEmb <: NumFieldEmb{FlintRationalField}
end

function Base.show(io::IO, ::QQEmb)
  print(io, "Complex embedding of rational numbers")
end

number_field(::QQEmb) = QQ

(::QQEmb)(x::fmpq, prec::Int = 32) = ArbField(prec)(x)

real_embeddings(::FlintRationalField) = [QQEmb()]

complex_embeddings(::FlintRationalField) = [QQEmb()]

is_real(::QQEmb) = true

restrict(::NumFieldEmb, ::FlintRationalField) = QQEmb()

_embedding(::PosInf) = QQEmb()

evaluate(x::fmpq, ::QQEmb, prec::Int = 32) = AcbField(prec)(x)

evaluate(x::fmpz, ::QQEmb, prec::Int = 32) = AcbField(prec)(x)

is_positive(x::Union{fmpz, fmpq}, ::QQEmb) = x > 0

is_totally_positive(x::Union{fmpz,fmpq}) = x > 0

is_negative(x::Union{fmpz, fmpq}, ::QQEmb) = x < 0

sign(a::FacElem{fmpq, FlintRationalField}) = prod(k -> Int(sign(k[1]))^(Int(k[2] % 2)), a, init = 1)

sign(::Type{Int}, a::FacElem{fmpq}) = sign(a)

sign(x::fmpq, ::QQEmb) = Int(sign(x))

sign(x::Union{fmpz, FacElem{fmpq}}, ::QQEmb) = sign(Int, x)

signs(x::Union{fmpz, fmpq, FacElem{fmpq}}, ::Vector{QQEmb}) = Dict(QQEmb() => sign(x, QQEmb()))

signs(x::Union{fmpz, fmpq, FacElem{fmpq}}) = Dict(QQEmb() => sign(x, QQEmb()))
