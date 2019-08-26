
############################################################
# IJulia/ Jupyter output
############################################################
function inNotebook()
  return isdefined(Main, :IJulia) && Main.IJulia.inited
end

function math_html(io::IO, a::PolyElem)
  f = "$a"
  f = replace(f, "*" => "")
  f = replace(f, r"\^([0-9]*)" => s"^{\1}")
  print(io, f)
end

function Base.show(io::IO, ::MIME"text/html", a::PolyElem)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, a::AnticNumberField)
  n = find_name(a)
  if n === nothing || !get(io, :compact, false)
    print(io, "\\text{Number field over Rational field with defining polynomial }")
    math_html(io, a.pol)
  else
    print(io, string(n))
  end
end

function Base.show(io::IO, ::MIME"text/html", a::AnticNumberField)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function Base.show(io::IO, ::MIME"text/html", A::Fac{T}) where {T}
  print(io, "\$")
  math_html(io, A)
  print(io, "\$")
end

function math_html(io::IO, a)
  try
    show(io, "text/html", a)
  catch e
    if isa(e, MethodError)
      show(io, a)
    else
      rethrow(e)
    end
  end
end

#=
function Base.show(io::IO, ::MIME"text/html", a)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end
=#

#=
function Base.show(io::IO, b::HTML{nf_elem})
  math_html(io, b.content)
end

function Base.show(io::IO, b::HTML{AnticNumberField})
  math_html(io, b.content)
end
=#


function Base.show(io::IO, ::MIME"text/html", T::Tuple)
  print(io, "(")
  for i =1:length(T)
    show(IOContext(io, :compact => true), "text/html", T[i])
    if i<length(T)
      print(io, ", ")
    end
  end
  print(io, ")")
end

function math_html(io::IO, a::nf_elem)
  s = parent(a).S
  if s in [:_a, Symbol("_\$")] 
    parent(a).S = Symbol("\\alpha")
    fs = string(a)
    parent(a).S = s
  else
    fs = string(a)
  end
  f = replace(fs, "*" => "")
  f = replace(f, r"\^([0-9]*)" => s"^{\1}")
  f = replace(f, r"([0-9]*)//([0-9]*)" => s"\\frac{\1}{\2}")
  if true
    print(io, f)
  else
    print(io, "\\toggle{$f}{$fs}\\endtoggle")
  end
end

function Base.show(io::IO, ::MIME"text/html", a::nf_elem)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, A::Fac{T}) where {T}
  empty = true
  if !isone(A.unit)
    math_html(io, A.unit)
    empty = false
  end
  for k = (collect(keys(A.fac)))
    if !empty
      print(io, "\\cdot")
    end
    empty = false
    AbstractAlgebra.needs_parentheses(k) && print(io, "(")
    math_html(io, k)
    AbstractAlgebra.needs_parentheses(k) && print(io, ")")
    if A.fac[k] != 1
      print(io, "^{")
      math_html(io, A.fac[k])
      print(io, "}")
    end
  end
end

Base.show(io::IO, ::MIME"text/html", a::Integer) = show(io, "text/html", fmpz(a))
math_html(io::IO, a::Integer) = math_html(io, fmpz(a))

function Base.show(io::IO, ::MIME"text/html", a::fmpz)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, a::fmpz)
  nd = ndigits(a, 10)
  if nd < 20
    print(io, a)
  else
    d = string(abs(a) % 10^5)
    d = "00000"[1:5-length(d)] * d
    d = "("*string(div(a, fmpz(10)^(nd-5))) *  "..($nd \\text{ digits}).." * d *")"
#    print(io, "\$\\require{action}\$")
    print(io, "\\toggle{$d}{$a}\\endtoggle")
  end
end

function math_html(io::IO, M::MatElem)
  print(io, "\\begin{bmatrix}")
  for i=1:nrows(M)
    for j=1:nrows(M)
      math_html(io, M[i,j])
      if j<nrows(M)
        print(io, "&")
      else
        print(io, "\\\\")
      end
    end
  end
  print(io, "\\end{bmatrix}")
end

function Base.show(io::IO, ::MIME"text/html", M::MatElem)
  print(io, "\$")
  math_html(io, M)
  print(io, "\$")
end

function math_html(io::IO, a::fmpq)
  if denominator(a) == 1
    math_html(io, numerator(a))
  else
    print(io, "\\frac{")
    math_html(io, numerator(a))
    print(io, "}{")
    math_html(io, denominator(a))
    print(io, "}")
  end
end

function Base.show(io::IO, ::MIME"text/html", a::fmpq)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

math_html(io::IO, a::Rational) = math_html(io, fmpq(a))
function Base.show(io::IO, ::MIME"text/html", a::Rational) 
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

#= infinite recursion through generic math_html, so don't
function Base.show(io::IO, ::MIME"text/html", a) 
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end
=#

function math_html(io::IO, l::Array{T, 1}) where {T}
  print(io, "[")
  for i in 1:length(l)
    if i>1
      print(io, ", ")
    end
    math_html(IOContext(io, :compact => true), l[i])
  end
  print(io, "]")
end

function Base.show(io::IO, ::MIME"text/html", l::Array{T, 1}) where {T}
  print(io, "\$")
  math_html(io, l)
  print(io, "\$")
end


function math_html(io::IO, a::NfAbsOrdElem)
  math_html(io, elem_in_nf(a))
end

function math_html(io::IO, O::NfAbsOrd{AnticNumberField, nf_elem})
  c = get(io, :compact, false)
  if !c
    print(io, "\\text{Maximal order of }")
    math_html(io, nf(O))
    print(io, "\\text{ with basis }")
    math_html(io, basis(O))
    return
  end

  n = find_name(O)
  if !(n===nothing)
    print(io, string(n))
    return
  end
  n = find_name(nf(O))
  if n === nothing 
    print(io, "\\text{Maximal order of }")
    math_html(io, nf(O))
  else
    print(io, "\\mathcal O_$(string(n))")
  end
end

function Base.show(io::IO, ::MIME"text/html", a::NfAbsOrd{AnticNumberField, nf_elem})
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end


function math_html(io::IO, M::Map)
  n = find_name(M)
  cio = IOContext(io, :compact => true)
  if n === nothing
    print(io, "\\text{Map from }")
  else
    print(io, string(n))
    print(io, ": ")
  end
  n = find_name(domain(M))
  if n === nothing
    math_html(cio, domain(M))
  else
    print(io, string(n))
  end
  print(io, "\\to ")
  n = find_name(codomain(M))
  if n === nothing
    math_html(cio, codomain(M))
  else
    print(io, string(n))
  end
end

function Base.show(io::IO, ::MIME"text/html", M::Map)
  print(io, "\$")
  math_html(io, M)
  print(io, "\$")
end

function math_html(io::IO, I::NfAbsOrdIdlSet)
  print(io, "\\text{Set of ideals of }")
  n = find_name(order(I))
  if n === nothing || !get(io, :compact, false)
    math_html(IOContext(io, :compact => true), order(I))
  else
    print(io, string(n))
  end
end

function Base.show(io::IO, ::MIME"text/html", G::GrpAbFinGen)
  print(io, "\$")
  math_html(io, G)
  print(io, "\$")
end

function math_html(io::IO, G::GrpAbFinGen)
  n = find_name(G)
  if !(n === nothing) && get(io, :compact, false)
    print(io, string(n))
    return 
  end
  if issnf(G)
    if get(io, :compact, false)
      print(io, "\\text{Abelian Group with Invariants: }")
    else
      print(io, "\\text{GrpAb: }")
    end
    show_snf_structure(io, G, "\\times")
  else
    print(io, G)
  end
end

function math_html(io::IO, R::PolyRing)
  n = find_name(R)
  if !(n === nothing) && get(io, :compact, false)
    print(io, string(n))
    return 
  end
  print(io, "\\text{Polynomial ring over }")
  print(IOContext(io, :compact => true), base_ring(R))
end

function Base.show(io::IO, ::MIME"text/html", K::PolyRing)
  print(io, "\$")
  math_html(io, K)
  print(io, "\$")
end

function math_html(io::IO, K::NfRel)
  n = find_name(K)
  if !(n === nothing) && get(io, :compact, false)
    print(io, string(n))
    return 
  end
  print(io, "\\text{Relative number field over }")
  math_html(IOContext(io, :compact => true), base_field(K))
  print(io, "\\text{ defined by }")
  math_html(io, K.pol)
end

function Base.show(io::IO, ::MIME"text/html", K::NfRel)
  print(io, "\$")
  math_html(io, K)
  print(io, "\$")
end

function Base.show(io::IO, ::MIME"text/html", b::Bool)
   print(io, b ? "true" : "false")
end


function find_name(A, M = Main)
  for a = names(Main)
    a === :ans && continue
    d = Meta.parse("$M.$a")
    try
      z = eval(d);
      if z === A
        return a
      end
    catch e
    end
  end
end


