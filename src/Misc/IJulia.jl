
############################################################
# IJulia/ Jupyter output
############################################################
function math_html(io::IO, a::Nemo.fpFieldElem)
  print(io, a)
end

function Base.show(io::IO, ::MIME"text/html", a::Nemo.fpFieldElem)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, a::PolyRingElem)
  f = "$a"
  if parent(a).S in [Symbol("_\$1")]
    f = replace(f, "_\$1" => "x")
  end
  f = replace(f, "*" => "")
  f = replace(f, r"\^([0-9]*)" => s"^{\1}")
  print(io, f)
end

function Base.show(io::IO, ::MIME"text/html", a::PolyRingElem)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, a::AbsSimpleNumField)
  n = get_name(a)
  if n === nothing || !get(io, :compact, false)
    print(io, "\\text{Number field over Rational field with defining polynomial }")
    math_html(io, a.pol)
  else
    print(io, string(n))
  end
end

function Base.show(io::IO, ::MIME"text/html", a::RelNonSimpleNumField)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, a::RelNonSimpleNumField)
  n = get_name(a)
  if n === nothing || !get(io, :compact, false)
    print(io, "\\text{non-simple Relative number field over }")
    math_html(io, base_field(a))
    print(io, "\\text{ with defining polynomials: }")
    math_html(io, a.pol)
  else
    print(io, string(n))
  end
end

function Base.show(io::IO, ::MIME"text/html", a::AbsNonSimpleNumField)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, a::AbsNonSimpleNumField)
  n = get_name(a)
  if n === nothing || !get(io, :compact, false)
    print(io, "\\text{non-simple number field with defining polynomials: }")
    math_html(io, a.pol)
  else
    print(io, string(n))
  end
end

function Base.show(io::IO, ::MIME"text/html", a::AbsSimpleNumField)
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
#    @show e
    if isa(e, MethodError)
      print(io, " \$")
      show(io, a)
      print(io, "\$ ")
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
function Base.show(io::IO, b::HTML{AbsSimpleNumFieldElem})
  math_html(io, b.content)
end

function Base.show(io::IO, b::HTML{AbsSimpleNumField})
  math_html(io, b.content)
end
=#


#function Base.show(io::IO, mime::MIME"text/html", T::Tuple)
#  print(io, "(")
#  for i =1:length(T)
#    try
#      show(IOContext(io, :compact => true), mime, T[i])
#    catch e
##      @show e
#      if isa(e, MethodError)
#        show(IOContext(io, :compact => true), T[i])
#      else
#        rethrow(e)
#      end
#    end
#    if i<length(T)
#      print(io, ", ")
#    end
#  end
#  print(io, ")")
#end

function math_html(io::IO, a::AbsSimpleNumFieldElem)
  s = t = parent(a).S
  f, c = is_cyclotomic_type(parent(a))
  if f
    if s == Symbol("z_$c")
      t = Symbol("\\zeta_{$c}")
    end
  end
  if s in [:_a, Symbol("_\$")]
    t = Symbol("\\alpha")
  end
  parent(a).S = t
  fs = string(a)
  parent(a).S = s

  f = replace(fs, "*" => "")
  f = replace(f, r"sqrt\(([-0-9]*)\)" => s"\\sqrt{\1}")
  f = replace(f, r"\^([0-9]*)" => s"^{\1}")
  f = replace(f, r"([0-9]*)//([0-9]*)" => s"\\frac{\1}{\2}")
  if true
    print(io, f)
  else
    print(io, "\\toggle{$f}{$fs}\\endtoggle")
  end
end

function Base.show(io::IO, ::MIME"text/html", a::AbsSimpleNumFieldElem)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, a::MapParent)
  print(io, "\\text{Set of all $(a.typ) from }")
  try
    math_html(io, a.dom)
  catch e
    show(io, a.dom)
  end
  print(io, "\\to")
  try
    math_html(io, a.codom)
  catch e
    show(io, a.dom)
  end
end

function Base.show(io::IO, ::MIME"text/html", a::MapParent)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

# Requires 0.12.1
function math_html(io::IO, A::Fac{T}) where {T}
  print(io, AbstractAlgebra.obj_to_latex_string(A))
end

#Base.show(io::IO, ::MIME"text/html", a::Integer) = show(io, "text/html", ZZRingElem(a))
math_html(io::IO, a::Integer) = math_html(io, ZZRingElem(a))

function Base.show(io::IO, ::MIME"text/html", a::ZZRingElem)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, a::ZZRingElem)
  nd = ndigits(a, 10)
  if nd < 20
    print(io, a)
  else
    d = string(abs(a) % 10^5)
    d = "00000"[1:5-length(d)] * d
    d = "("*string(div(a, ZZRingElem(10)^(nd-5))) *  "..($nd \\text{ digits}).." * d *")"
#    print(io, "\$\\require{action}\$")
    print(io, "\\toggle{$d}{$a}\\endtoggle")
  end
end

function math_html(io::IO, M::MatElem)
  print(io, "\\begin{bmatrix}")
  for i=1:nrows(M)
    for j=1:ncols(M)
      math_html(io, M[i,j])
      if j<ncols(M)
        print(io, "&")
      elseif i<nrows(M)
        print(io, "\\\\", "\n")
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

function math_html(io::IO, a::QQFieldElem)
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

function Base.show(io::IO, ::MIME"text/html", a::QQFieldElem)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

math_html(io::IO, a::Rational) = math_html(io, QQFieldElem(a))

#function Base.show(io::IO, ::MIME"text/html", a::Rational)
#  print(io, "\$")
#  math_html(io, a)
#  print(io, "\$")
#end

function Base.show(io::IO, ::MIME"text/html", ::QQField)
  print(io, "\$")
  math_html(io, FlintQQ)
  print(io, "\$")
end

function math_html(io::IO, ::QQField)
  print(io, "\\text{Rational Field}")
end

function Base.show(io::IO, ::MIME"text/html", ::ZZRing)
  print(io, "\$")
  math_html(io, FlintQQ)
  print(io, "\$")
end

function math_html(io::IO, ::ZZRing)
  print(io, "\\text{Integer Ring}")
end




#= infinite recursion through generic math_html, so don't
function Base.show(io::IO, ::MIME"text/html", a)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end
=#

function math_html(io::IO, l::Vector{T}) where {T}
  print(io, "[")
  for i in 1:length(l)
    if i>1
      print(io, ", ")
    end
    math_html(IOContext(io, :compact => true), l[i])
  end
  print(io, "]")
end

#function Base.show(io::IO, mime::MIME"text/html", l::Vector{T}) where {T}
#  io = IOContext(io, :compact => true)
#  first = true
#  print(io, "[")
#  for i = l
#    if first
#      first = false
#    else
#      print(io, ", ")
#    end
#    show(io, mime, i)
#  end
#  print(io, "]")
#end


function math_html(io::IO, a::AbsNumFieldOrderElem)
  math_html(io, elem_in_nf(a))
end

function Base.show(io::IO, ::MIME"text/html", a::AbsNumFieldOrderElem)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end

function math_html(io::IO, O::AbsSimpleNumFieldOrder)
  c = get(io, :compact, false)
  if is_maximal_known_and_maximal(O)
    n = "Maximal order of"
  else
    n = "Order of"
  end
  if !c
    print(io, "\\text{$n }")
    math_html(io, nf(O))
    print(io, "\\text{ with basis }")
    math_html(io, basis(O))
    return
  end

  n = get_name(O)
  if n !== nothing
    print(io, string(n))
    return
  end
  n = get_name(nf(O))
  if n === nothing
    print(io, "\\text{$n }")
    math_html(io, nf(O))
  else
    print(io, "\\mathcal O_$(string(n))")
  end
end

function Base.show(io::IO, ::MIME"text/html", a::AbsSimpleNumFieldOrder)
  print(io, "\$")
  math_html(io, a)
  print(io, "\$")
end


function math_html(io::IO, M::Map)
  n = get_name(M)
  cio = IOContext(io, :compact => true)
  if n === nothing
    print(io, "\\text{Map from }")
  else
    print(io, string(n))
    print(io, ": ")
  end
  n = get_name(domain(M))
  if n === nothing
    math_html(cio, domain(M))
  else
    print(io, string(n))
  end
  print(io, "\\to ")
  n = get_name(codomain(M))
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

function math_html(io::IO, I::AbsNumFieldOrderIdealSet)
  print(io, "\\text{Set of ideals of }")
  n = get_name(order(I))
  if n === nothing || !get(io, :compact, false)
    math_html(IOContext(io, :compact => true), order(I))
  else
    print(io, string(n))
  end
end

function Base.show(io::IO, ::MIME"text/html", G::FinGenAbGroup)
  print(io, "\$")
  math_html(io, G)
  print(io, "\$")
end

function show_tensor_product(io::IO, ::MIME"text/html", G::FinGenAbGroup)
  T = get_attribute(G, :tensor_product)
  @assert T !== nothing
  io = IOContext(io, :compact => true)
  math_html(io, T[1])
  for i=2:length(T)
    println(io, " \\otimes ")
    math_html(io, T[i])
  end
end
#TODO: other special show functions for abelian groups
#      add special(?) for class group
#      add parent of tuple... (occurs in tensor product)
function math_html(io::IO, G::FinGenAbGroup)
  n = get_name(G)
  if !(n === nothing) && get(io, :compact, false)
    print(io, string(n))
    return
  end
  s = get_attribute(G, :show)
  if s !== nothing
    try
      s(io, MIME("text/html"), G)
      return
    catch e
#      @show e
    end
  end
  if is_snf(G)
    if get(io, :compact, false)
      print(io, "\\text{GrpAb: }")
    else
      print(io, "\\text{Abelian Group with Invariants: }")
    end
    show_snf_structure(io, G, "\\times")
  else
    print(io, "\\text{General) abelian Group with relation matrix: }")
    math_html(io, G.rels)
  end
end

function math_html(io::IO, R::PolyRing)
  n = get_name(R)
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

function math_html(io::IO, K::RelSimpleNumField)
  n = get_name(K)
  if !(n === nothing) && get(io, :compact, false)
    print(io, string(n))
    return
  end
  print(io, "\\text{Relative number field over }")
  math_html(IOContext(io, :compact => true), base_field(K))
  print(io, "\\text{ defined by }")
  math_html(io, K.pol)
end

function Base.show(io::IO, ::MIME"text/html", K::RelSimpleNumField)
  print(io, "\$")
  math_html(io, K)
  print(io, "\$")
end

#function Base.show(io::IO, ::MIME"text/html", b::Bool)
#   print(io, b ? "true" : "false")
#end

function math_html(io::IO, S::FacElemMon)
  print(io, "\\text{Factored elements over }")
  math_html(io, base_ring(S))
end

function Base.show(io::IO, ::MIME"text/html", S::FacElemMon)
  print(io, "\$")
  math_html(io, S)
  print(io, "\$")
end

