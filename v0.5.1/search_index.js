var documenterSearchIndex = {"docs": [

{
    "location": "index.html#",
    "page": "Hecke",
    "title": "Hecke",
    "category": "page",
    "text": ""
},

{
    "location": "index.html#Hecke-1",
    "page": "Hecke",
    "title": "Hecke",
    "category": "section",
    "text": ""
},

{
    "location": "index.html#About-1",
    "page": "Hecke",
    "title": "About",
    "category": "section",
    "text": "Hecke is a software package for algebraic number theory maintained by Claus Fieker, Carlo Sircana and Tommy Hofmann. It is written in julia and is based on the computer algebra package Nemo.https://github.com/thofma/Hecke.jl (Source code)\nhttp://thofma.github.io/Hecke.jl/latest/ (Online documentation)So far, Hecke provides the following features:Orders (including element and ideal arithmetic) in number fields\nComputation of maximal orders\nVerified residue computations of Dedekind zeta functions\nClass and Unit group computation, S-units, PID testing\nLattice enumeration\nSparse linear algebra\nNormal forms for modules over maximal orders\nExtensions of number fields, non-simple extensions of number fields\nOrders and ideals in extensions of fields\nAbelian groups\nRay class groups, quotients of ray class groups\nInvariant subgroups\nClass Field Theory\nAssociative Algebras"
},

{
    "location": "index.html#Installation-1",
    "page": "Hecke",
    "title": "Installation",
    "category": "section",
    "text": "To use Hecke, a julia version of 1.0 is necessary (the latest stable julia version will do). Please see http://julialang.org/downloads for instructions on how to obtain julia for your system. Once a suitable julia version is installed, use the following steps at the julia prompt to install Hecke:julia> using Pkg\njulia> Pkg.add(\"Hecke\")"
},

{
    "location": "index.html#Quick-start-1",
    "page": "Hecke",
    "title": "Quick start",
    "category": "section",
    "text": "Here is a quick example of using Hecke:julia> using Hecke\n...\n\nWelcome to \n\n  _    _           _        \n | |  | |         | |       \n | |__| | ___  ___| | _____ \n |  __  |/ _ \\/ __| |/ / _ \\\n | |  | |  __/ (__|   <  __/\n |_|  |_|\\___|\\___|_|\\_\\___|\n  \nVersion 0.5.0 ... \n ... which comes with absolutely no warranty whatsoever\n(c) 2015-2018 by Claus Fieker, Tommy Hofmann and Carlo Sircana\n\njulia> Qx, x = PolynomialRing(FlintQQ, \"x\");\njulia> f = x^3 + 2;\njulia> K, a = NumberField(f, \"a\");\njulia> O = maximal_order(K);\njulia> O\nMaximal order of Number field over Rational Field with defining polynomial x^3 + 2 \nwith basis [1,a,a^2]The documentation of the single functions can also be accessed at the julia prompt. Here is an example:help?> signature\nsearch: signature\n\n  ----------------------------------------------------------------------------\n\n  signature(O::NfMaximalOrder) -> Tuple{Int, Int}\n\n  |  Returns the signature of the ambient number field of \\mathcal O."
},

{
    "location": "number_fields/intro.html#",
    "page": "Number Fields",
    "title": "Number Fields",
    "category": "page",
    "text": ""
},

{
    "location": "number_fields/intro.html#Number-Fields-1",
    "page": "Number Fields",
    "title": "Number Fields",
    "category": "section",
    "text": "CurrentModule = Hecke"
},

{
    "location": "number_fields/intro.html#NumberFieldsLink-1",
    "page": "Number Fields",
    "title": "Introduction",
    "category": "section",
    "text": "This chapter deals with number fields. Number fields, in Hecke, come in several different types:AnticNumberField: a finite simple extension of the rational numbers Q\nNfAbsNS: a finite extension of Q given by several polynomials.We will refer to this as a non-simple field - even though mathematically  we can find a primitive elements.NfRel: a finite simple extension of a number field. This is   actually parametried by the (element) type of the coefficient field.  The complete type of an extension of an absolute field (AnticNumberField)  is NfRel{nf_elem}. The next extension thus will be  NfRel{NfRelElem{nf_elem}}.\nNfRel_ns: extensions of number fields given by several polynomials.  This too will be refered to as a non-simple field.The simple types AnticNumberField and NfRel are also calle simple fields in the rest of this document, NfRel and NfRel_ns are referred to as relative extensions while AnticNumberField and NfAbsNS are called absolute.Internally, simple fields are essentially just (univariate) polynomial quotients in a dense representation, while non-simple fields are multivariate quotient rings, thus have a sparse presentation. In general, simple fields allow much faster arithmetic, while  the non-simple fields give easy access to large degree fields."
},

{
    "location": "number_fields/intro.html#Absolute-Simple-Fields-1",
    "page": "Number Fields",
    "title": "Absolute Simple Fields",
    "category": "section",
    "text": "The most basic number field type is that of AnticNumberField. Internally this is essentially represented as a unvariate quotient with the arithmetic provided by the antic-c-library and implemented in Nemo."
},

{
    "location": "number_fields/intro.html#Nemo.NumberField-Tuple{fmpq_poly}",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "method",
    "text": "NumberField(f::fmpq_poly; cached::Bool = true, check::Bool = true)\n\nThe number field Q[x]/f generated by f.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.cyclotomic_field-Tuple{Int64}",
    "page": "Number Fields",
    "title": "Hecke.cyclotomic_field",
    "category": "method",
    "text": "cyclotomic_field(n::Int) -> AnticNumberField, nf_elem\n\nThe n-th cyclotomic field defined by the n-the cyclotomic polynomial.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.wildanger_field-Tuple{Int64,fmpz}",
    "page": "Number Fields",
    "title": "Hecke.wildanger_field",
    "category": "method",
    "text": "wildanger_field(n::Int, B::fmpz) -> AnticNumberField, nf_elem\nwildanger_field(n::Int, B::Integer) -> AnticNumberField, nf_elem\n\nReturns the field with defining polynomial x^n + sum_i=0^n-1 (-1)^n-iBx^i. These fields tend to have non-trivial class groups.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.pure_extension-Tuple{Int64,Integer}",
    "page": "Number Fields",
    "title": "Hecke.pure_extension",
    "category": "method",
    "text": "pure_extension(n::Int, gen::Integer; cached::Bool = true, check::Bool = true) -> AnticNumberField, nf_elem\npure_extension(n::Int, gen::fmpz; cached::Bool = true, check::Bool = true) -> AnticNumberField, nf_elem\n\nThe number field with defining polynomial x^n-gen.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Creation-1",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "Number fields are mostly created using NumberField, but also using number_field.Many of the constructors have arguments of type Symbol or AbstractString, if used, they define the appearance in printing, and printing only. The named parameter check can be true or false, the default beingtrue`. This parameter controlls is the polynomial defining the number field is tested for irreducibility or not. Given that this can be potentially  very time consuiming if the degree if large, one can omit this test. Note however, that the behaviour of Hecke is undefined if a reducible polynomial is used to define a field.The named boolean parameter cached is inherited from the underlying Nemo system. Two number fields defined using the same polynomial from the identical polynomial ring and the same (identical) symbol/ string will be identical if cached == true and different if cached == false.NumberField(f::fmpq_poly)\ncyclotomic_field(n::Int)\n#CyclotomicField(n::Int, s::AbstractString, t; cached)\n#CyclotomicField(n::Int, s::AbstractString, t)\n#CyclotomicField(n::Int, s::AbstractString)\n#MaximalRealSubfield(n::Int, s::AbstractString)\n#MaximalRealSubfield(n::Int, s::AbstractString, t)\nwildanger_field(n::Int, B::fmpz)\npure_extension(n::Int, gen::Integer)"
},

{
    "location": "number_fields/intro.html#Example-1",
    "page": "Number Fields",
    "title": "Example",
    "category": "section",
    "text": "using Hecke # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, a = NumberField(x^2 - 10, \"a\");"
},

{
    "location": "number_fields/intro.html#Absolute-Non-Simple-Fields-1",
    "page": "Number Fields",
    "title": "Absolute Non-Simple Fields",
    "category": "section",
    "text": ""
},

{
    "location": "number_fields/intro.html#Nemo.NumberField",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "function",
    "text": "number_field(f::Array{fmpq_poly, 1}, s::String=\"_\\$\") -> NfAbsNS\n\nLet f = (f_1 ldots f_n) be univariate rational polynomials, then we construct \n\nK = Qt_1 ldots t_nlangle f_1(t_1) ldots f_n(t_n)rangle\n\nThe ideal bust be maximal, however, this is not tested.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Creation-2",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "NumberField(f::Array{fmpq_poly, 1}, s::String=\"a\")"
},

{
    "location": "number_fields/intro.html#Example-2",
    "page": "Number Fields",
    "title": "Example",
    "category": "section",
    "text": "using Hecke # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, g = number_field([x^2-2, x^2-3, x^2-5])\ng[1]^2\nminpoly(g[1] + g[2])"
},

{
    "location": "number_fields/intro.html#Hecke.simple_extension-Tuple{NfAbsNS}",
    "page": "Number Fields",
    "title": "Hecke.simple_extension",
    "category": "method",
    "text": "simple_extension(K::NfAbsNS) -> AnticNumberField, Map\n\nFor a non-simple extension K of Q, find a primitive element and thus an isomorphic simple extension of Q. The map realises this isomorphism.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Conversion-1",
    "page": "Number Fields",
    "title": "Conversion",
    "category": "section",
    "text": "simple_extension(K::NfAbsNS)"
},

{
    "location": "number_fields/intro.html#Simple-Relative-Fields-1",
    "page": "Number Fields",
    "title": "Simple Relative Fields",
    "category": "section",
    "text": ""
},

{
    "location": "number_fields/intro.html#Nemo.NumberField-Tuple{AbstractAlgebra.Generic.Poly}",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "method",
    "text": "NumberField(f::Generic.Poly{T}, s::String; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\nNumberField(f::Generic.Poly{T}; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\nnumber_field(f::Array{Generic.Poly{T}, 1}, s::String=\"_\\$\") where T -> NfRel_ns\n\nGiven polynomials f = (f_1 ldots f_n) over some number field k, construct K = kt_1 ldots t_nlangle f_1(t_1) ldots f_n(t_n)rangle The ideal in the quotient must be maximal - although this is not tested.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Nemo.NumberField-Tuple{AbstractAlgebra.Generic.Poly,String}",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "method",
    "text": "NumberField(f::Generic.Poly{T}, s::String; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Creation-3",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "NumberField(f::Generic.Poly)\nNumberField(f::Generic.Poly, s::String)"
},

{
    "location": "number_fields/intro.html#Hecke.absolute_field-Tuple{Hecke.NfRel{nf_elem}}",
    "page": "Number Fields",
    "title": "Hecke.absolute_field",
    "category": "method",
    "text": "absolute_field(K::NfRel{nf_elem}, cached::Bool = false) -> AnticNumberField, Map, Map\n\nGiven an extension KkQ, find an isomorphic extensino of Q.\n\n\n\nabsolute_field(K::NfRel{NfRelElem}, cached::Bool = false) -> NfRel, Map, Map\n\nGiven an extension EKk, find an isomorphic extension of k. In a tower, only the top-most steps are collapsed.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.absolute_field-Tuple{Hecke.NfRel{Hecke.NfRelElem}}",
    "page": "Number Fields",
    "title": "Hecke.absolute_field",
    "category": "method",
    "text": "absolute_field(K::NfRel{NfRelElem}, cached::Bool = false) -> NfRel, Map, Map\n\nGiven an extension EKk, find an isomorphic extension of k. In a tower, only the top-most steps are collapsed.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Conversion-2",
    "page": "Number Fields",
    "title": "Conversion",
    "category": "section",
    "text": "absolute_field(K::NfRel{nf_elem})\nabsolute_field(K::NfRel{NfRelElem})"
},

{
    "location": "number_fields/intro.html#Non-Simple-Relative-Fields-1",
    "page": "Number Fields",
    "title": "Non-Simple Relative Fields",
    "category": "section",
    "text": ""
},

{
    "location": "number_fields/intro.html#Nemo.NumberField-Union{Tuple{Array{Poly{T},1}}, Tuple{T}, Tuple{Array{Poly{T},1},String}} where T",
    "page": "Number Fields",
    "title": "Nemo.NumberField",
    "category": "method",
    "text": "number_field(f::Array{Generic.Poly{T}, 1}, s::String=\"_\\$\") where T -> NfRel_ns\n\nGiven polynomials f = (f_1 ldots f_n) over some number field k, construct K = kt_1 ldots t_nlangle f_1(t_1) ldots f_n(t_n)rangle The ideal in the quotient must be maximal - although this is not tested.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Creation-4",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "NumberField(f::Array{Generic.Poly{T}, 1}, s::String=\"a\") where T"
},

{
    "location": "number_fields/intro.html#Hecke.simple_extension-Tuple{NfRel_ns}",
    "page": "Number Fields",
    "title": "Hecke.simple_extension",
    "category": "method",
    "text": "simple_extension(K::NfRel_ns{nf_elem}) -> AnticNumberField, Map, Map\n\nCompute an isomorphic field as an extension of Q together with the isomorphism  (1st map) and the embedding of the base field (2nd map).\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.simple_extension-Tuple{NfRel_ns{nf_elem},FlintRationalField}",
    "page": "Number Fields",
    "title": "Hecke.simple_extension",
    "category": "method",
    "text": "simple_extension(K::NfRel_ns{nf_elem}, FlintQQ) -> AnticNumberField, Map, Map\n\nabsolute_field(K::NfRel_ns{nf_elem}) -> AnticNumberField, Map, Map\n\nCompute an isomorphic field as an extension of Q together with the isomorphism  (1st map) and the embedding of the base field (2nd map).\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Conversion-3",
    "page": "Number Fields",
    "title": "Conversion",
    "category": "section",
    "text": "simple_extension(K::NfRel_ns)\nsimple_extension(K::NfRel_ns{nf_elem}, ::FlintRationalField)"
},

{
    "location": "number_fields/intro.html#Base.minimum-Union{Tuple{T}, Tuple{T,NfAbsOrdIdl{AnticNumberField,nf_elem}}} where T<:(Map{AnticNumberField,AnticNumberField,S,T} where T where S)",
    "page": "Number Fields",
    "title": "Base.minimum",
    "category": "method",
    "text": "minimum(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField} -> NfOrdIdl\n\nGiven an embedding mkto K of number fields and an integral ideal in K, find the  intersection I cap Z_k.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#LinearAlgebra.norm-Union{Tuple{T}, Tuple{T,NfAbsOrdIdl{AnticNumberField,nf_elem}}} where T<:(Map{AnticNumberField,AnticNumberField,S,T} where T where S)",
    "page": "Number Fields",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "norm(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField} -> NfOrdIdl\n\nGiven an embedding mkto K of number fields and an integral ideal in K, find the norm N_Kk(I).\n\n\n\n"
},

{
    "location": "number_fields/intro.html#LinearAlgebra.norm-Union{Tuple{T}, Tuple{T,nf_elem}} where T<:(Map{AnticNumberField,AnticNumberField,S,T} where T where S)",
    "page": "Number Fields",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "norm(m::T, a::nf_elem) where T <: Map{AnticNumberField, AnticNumberField} -> nf_elem\n\nGiven an embedding mkto K of number fields and an element in K, find the norm N_Kk(a).\n\n\n\n"
},

{
    "location": "number_fields/intro.html#AbstractAlgebra.Generic.discriminant-Tuple{Map,NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Number Fields",
    "title": "AbstractAlgebra.Generic.discriminant",
    "category": "method",
    "text": "discriminant(m::Map, R::NfOrd) -> NfOrdIdl\n\nThe discriminant ideal of R over the maximal order of the domain of the map m,  that is, the ideal generated by all norms of differents of elements in R.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Hecke.NfAbsOrdIdlSet",
    "page": "Number Fields",
    "title": "Hecke.NfAbsOrdIdlSet",
    "category": "type",
    "text": "(::NfAbsOrdIdlSet)(m::Map, I::NfOrdIdl) -> NfOrdIdl\n\nGiven an embedding mkto K of number fields and an ideal I in k, find the ideal above I in K.\n\n\n\n"
},

{
    "location": "number_fields/intro.html#Implicit-Relative-Extensions-1",
    "page": "Number Fields",
    "title": "Implicit Relative Extensions",
    "category": "section",
    "text": "Given two absolute fields K and k as well as an embedding phik to K we can regard K as an extension on k, hence invariante of K can be investigated relative to k rathern than over Q. Here we list functions achieving this without actually computing K as an extension of k.minimum(m::T, I::NfOrdIdl) where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)\nnorm(m::T, I::Hecke.NfAbsOrdIdl{Nemo.AnticNumberField,Nemo.nf_elem}) where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)\nnorm(m::T, a::nf_elem)  where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)\ndiscriminant(m::Map, R::NfOrd)NfAbsOrdIdlSet"
},

{
    "location": "number_fields/intro.html#Invariants-1",
    "page": "Number Fields",
    "title": "Invariants",
    "category": "section",
    "text": "degree(::AnticNumberField)\nbasis(::AnticNumberField)\ndiscriminant(::AnticNumberField)"
},

{
    "location": "number_fields/intro.html#Elements-1",
    "page": "Number Fields",
    "title": "Elements",
    "category": "section",
    "text": ""
},

{
    "location": "number_fields/intro.html#Creation-5",
    "page": "Number Fields",
    "title": "Creation",
    "category": "section",
    "text": "AnticNumberField"
},

{
    "location": "number_fields/intro.html#Invariants-2",
    "page": "Number Fields",
    "title": "Invariants",
    "category": "section",
    "text": "norm(::nf_elem)\nminpoly(::nf_elem)\ncharpoly(::nf_elem)\ndenominator(::nf_elem)\nnumerator(::nf_elem)\nisunit(::nf_elem)"
},

{
    "location": "orders/introduction.html#",
    "page": "Introduction",
    "title": "Introduction",
    "category": "page",
    "text": ""
},

{
    "location": "orders/introduction.html#Introduction-1",
    "page": "Introduction",
    "title": "Introduction",
    "category": "section",
    "text": "CurrentModule = HeckeThis chapter deals with absolute number fields and orders there of. "
},

{
    "location": "orders/introduction.html#Definitions-and-vocabulary-1",
    "page": "Introduction",
    "title": "Definitions and vocabulary",
    "category": "section",
    "text": "We begin by collecting the necessary definitions and vocabulary.  This is in particular important for everything related to embeddings of number fields into archimedean fields, since they are at least two (slighlty) different normalizations. "
},

{
    "location": "orders/introduction.html#Number-fields-1",
    "page": "Introduction",
    "title": "Number fields",
    "category": "section",
    "text": "By an absolute number field we mean finite extensions of mathbf Q, which is of type AnticNumberField and whose elements are of type nf_elem. Such an absolute number field K is always given in the form K = mathbf Q(alpha) = mathbf QX(f), where f in mathbf QX is an irreducible polynomial. See here for more information on the different types of fields supported.We call (1alphaalpha^2dotscalpha^d-1), where d is the degree K  mathbf Q the power basis of K. If beta is any element of K, then the representation matrix of beta is the matrix representing K to K gamma mapsto beta gamma with respect to the power basis, that is,\\[ \\beta \\cdot (1,\\alpha,\\dotsc,\\alpha^{d-1}) = M_\\alpha (1, \\alpha, \\dotsc, \\alpha^{d-1}). \\]Let (rs) be the signature of K, that is, K has r real embeddings sigma_i colon K to mathbfR, 1 leq i leq r, and 2s complex embeddings sigma_i colon K to mathbfC, 1 leq i leq 2s. In Hecke the complex embeddings are always ordered such that sigma_i = overlinesigma_i+s for r + 1 leq i leq r + s. The mathbfQ-linear function \\[ K \\longrightarrow \\mathbf R^{d}, \\ \\alpha \\longmapsto (\\sigma1(\\alpha),\\dotsc,\\sigmar(\\alpha),\\sqrt{2}\\operatorname{Re}(\\sigma{r+1}(\\alpha)),\\sqrt{2}\\operatorname{Im}(\\sigma{r+1}(\\alpha)),\\dotsc,\\sqrt{2}\\operatorname{Re}(\\sigma{r+s}(\\alpha)),\\sqrt{2}\\operatorname{Im}(\\sigma{r+s}(\\alpha)) \\] is called the Minkowski map (or Minkowski embedding)."
},

{
    "location": "orders/introduction.html#Orders-1",
    "page": "Introduction",
    "title": "Orders",
    "category": "section",
    "text": "If K = mathbf Q(alpha) is an absolute number field, then an order mathcal O of K is a subring of the ring of integers mathcal O_K, which is free of rank  K  mathbf Q as a mathbf Z-module. The natural order mathbf Zalpha is called the equation order of K. In Hecke orders of absolute number fields are constructed (implicitely) by specifying a mathbf Z-basis, which is refered to as the basis of mathcal O. If (omega_1dotscomega_d) is the basis of mathcal O, then the matrix B in operatornameMat_d times d(mathbf Q) with\\[ \\begin{pmatrix} \\omega1 \\\\ \\vdots \\\\ \\omegad \\end{pmatrix} = B \\begin{pmatrix} 1 \\\\ \\vdots \\\\ \\alpha^{d - 1} \\end{pmatrix} \\]is called the basis matrix of mathcal O. We call det(B) the generalized index of mathcal O.  In case mathbf Zalpha subseteq mathcal O, the determinant det(B)^-1 is in fact equal to  mathcal O  mathbf Zalpha and is called the index of mathcal O. The matrix \\[ \\begin{pmatrix}  \\sigma1(\\omega1) & \\dotsc & \\sigmar(\\omega1) & \\sqrt{2}\\operatorname{Re}(\\sigma{r+1}(\\omega1)) & \\sqrt{2}\\operatorname{Im}(\\sigma{r+1}(\\omega1)) & \\dotsc & \\sqrt{2}\\operatorname{Im}(\\sigma{r+s}(\\omega1)) \\\\\n\\sigma1(\\omega2) & \\dotsc & \\sigmar(\\omega2) & \\sqrt{2}\\operatorname{Re}(\\sigma{r+1}(\\omega2)) & \\sqrt{2}\\operatorname{Im}(\\sigma{r+1}(\\omega2)) & \\dotsc  & \\sqrt{2}\\operatorname{Im}(\\sigma{r+s}(\\omega2)) \\\\\n\\vdots & \\dotsc & \\vdots & \\vdots & \\dotsc & \\vdots & \\vdots\\\\\n\\sigma1(\\omegad) & \\dotsc & \\sigmar(\\omegad) & \\sqrt{2}\\operatorname{Re}(\\sigma{r+1}(\\omegad)) & \\sqrt{2}\\operatorname{Im}(\\sigma{r+2}(\\omegad)) & \\dotsc & \\sqrt{2}\\operatorname{Im}(\\sigma{r+s}(\\omegad)) \\end{pmatrix} \\in \\operatorname{Mat}_{d\\times d}(\\mathbf R). \\] is called the Minkowski matrix of mathcal O."
},

{
    "location": "orders/introduction.html#Examples-1",
    "page": "Introduction",
    "title": "Examples",
    "category": "section",
    "text": "Usually, to create an order, one starts with a field (or a polynomial):using Hecke; # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, a = NumberField(x^2 - 10, \"a\");\nE = EquationOrder(K)\nZ_K = MaximalOrder(K)\nconductor(E)\nE == Z_KOnce orders are created, we can play with elements and ideals:lp = prime_decomposition(Z_K, 2)\np = lp[1][1]\nisprincipal(p)\nfl, alpha = isprincipal(p^2)\nnorm(alpha)It is possible to work with residue fields as well:Fp, mFp = ResidueField(Z_K, p)\n[ mFp(x) for x = basis(Z_K)]"
},

{
    "location": "orders/orders.html#",
    "page": "Orders",
    "title": "Orders",
    "category": "page",
    "text": ""
},

{
    "location": "orders/orders.html#Orders-1",
    "page": "Orders",
    "title": "Orders",
    "category": "section",
    "text": "CurrentModule = HeckeOrders, ie. unitary subrings that are free Z-modules of rank equal to the degree of the number field, are at the core of the arithmetic of number fields. In Hecke, orders are always represented using the module structure, be it the Z-module structure for orders in absolute fields, of the structure as a module over the maximal order of the base field in the case of relative extensions. In this chapter we only deal with orders in absolute fields. There are more general definitions of orders in number fields available, but those are (currently) not implemented in Hecke.Among all orders in a fixed field, there is a unique maximal one, called the maximal order, or ring of integers of the field. It is well known that this is the only order that is a Dedekind domain, hence has a rich ideal structure as well. The maximal order is also the integral closure of Z in the number field and can also be interpreted as a normalisation of any other order."
},

{
    "location": "orders/orders.html#Hecke.Order-Tuple{AnticNumberField,Array{nf_elem,1}}",
    "page": "Orders",
    "title": "Hecke.Order",
    "category": "method",
    "text": "Order(B::Array{nf_elem, 1}, check::Bool = true) -> NfOrd\n\nReturns the order with mathbf Z-basis B. If check is set, it is checked whether B defines an order.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.Order-Tuple{AnticNumberField,FakeFmpqMat}",
    "page": "Orders",
    "title": "Hecke.Order",
    "category": "method",
    "text": "Order(K::AnticNumberField, A::FakeFmpqMat, check::Bool = true) -> NfOrd\n\nReturns the order which has basis matrix A with respect to the power basis of K. If check is set, it is checked whether A defines an order.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.Order-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Orders",
    "title": "Hecke.Order",
    "category": "method",
    "text": "Order(K::AnticNumberField, A::fmpz_mat, check::Bool = true) -> NfOrd\n\nReturns the order which has basis matrix A with respect to the power basis of K. If check is set, it is checked whether A defines an order.\n\n\n\nOrder(A::NfOrdFracIdl) -> NfOrd\n\nReturns the fractional ideal A as an order of the ambient number field.\n\n\n\n\n\n  Order(K::RelativeExtension, M::PMat) -> NfRelOrd\n\nReturns the order which has basis pseudo-matrix M with respect to the power basis of K.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.EquationOrder-Tuple{AnticNumberField}",
    "page": "Orders",
    "title": "Hecke.EquationOrder",
    "category": "method",
    "text": "EquationOrder(K::AnticNumberField) -> NfOrd\n\nReturns the equation order of the number field K.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.MaximalOrder-Tuple{AnticNumberField}",
    "page": "Orders",
    "title": "Hecke.MaximalOrder",
    "category": "method",
    "text": "maximal_order(K::AnticNumberField) -> NfOrd\nring_of_integers(K::AnticNumberField) -> NfOrd\n\nReturns the maximal order of K.\n\nExample\n\njulia> Qx, xx = FlintQQ[\"x\"];\njulia> K, a = NumberField(x^3 + 2, \"a\");\njulia> O = MaximalOrder(K);\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.MaximalOrder-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.MaximalOrder",
    "category": "method",
    "text": "\n\nmaximal_order(O::NfOrd) -> NfOrd\nMaximalOrder(O::NfOrd) -> NfOrd\n\nReturns the maximal overorder of O.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.maximal_order-Tuple{AnticNumberField}",
    "page": "Orders",
    "title": "Hecke.maximal_order",
    "category": "method",
    "text": "maximal_order(K::AnticNumberField) -> NfOrd\nring_of_integers(K::AnticNumberField) -> NfOrd\n\nReturns the maximal order of K.\n\nExample\n\njulia> Qx, xx = FlintQQ[\"x\"];\njulia> K, a = NumberField(x^3 + 2, \"a\");\njulia> O = MaximalOrder(K);\n\n\n\n"
},

{
    "location": "orders/orders.html#Nemo.lll-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Nemo.lll",
    "category": "method",
    "text": "lll(M::NfOrd) -> NfOrd\n\nThe same order, but with the basis now being LLL reduced wrt. the Minkowski metric.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.maximal_order-Tuple{AnticNumberField,Array{fmpz,1}}",
    "page": "Orders",
    "title": "Hecke.maximal_order",
    "category": "method",
    "text": "\n\nMaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd\nmaximal_order(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd\nring_of_integers(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd\n\nAssuming that primes contains all the prime numbers at which the equation order mathbfZalpha of K = mathbfQ(alpha) is not maximal, this function returns the maximal order of K.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.pradical-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Orders",
    "title": "Hecke.pradical",
    "category": "method",
    "text": "pradical(O::NfOrd, p::{fmpz|Integer}) -> NfAbsOrdIdl\n\nGiven a prime number p, this function returns the p-radical sqrtpmathcal O of mathcal O, which is just  x in mathcal O mid exists k in mathbf Z_geq 0 colon x^k in pmathcal O . It is not checked that p is prime.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.ring_of_multipliers-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.ring_of_multipliers",
    "category": "method",
    "text": "\n\nring_of_multipliers(I::NfAbsOrdIdl) -> NfOrd\n\nComputes the order (I  I), which is the set of all x in K with xI subseteq I.\n\n\n\n"
},

{
    "location": "orders/orders.html#Creation-and-basic-properties-1",
    "page": "Orders",
    "title": "Creation and basic properties",
    "category": "section",
    "text": "Order(::AnticNumberField, ::Array{nf_elem, 1})\nOrder(::AnticNumberField, ::FakeFmpqMat)\nOrder(::NfOrdFracIdl)\nEquationOrder(::AnticNumberField)\nMaximalOrder(::AnticNumberField)\nMaximalOrder(::NfOrd)\nmaximal_order(::AnticNumberField)\nlll(::NfOrd)By Chistov\'s fundamental theorem, the computation of the maximal order is basically as hard as the factorisation of the discriminant. In order to help the computer, Hecke also provides the following signatures:maximal_order(::AnticNumberField, ::Array{fmpz, 1})It is also possible the execute the steps individually:pradical(::NfOrd, ::fmpz)\nring_of_multipliers(::NfOrdIdl)"
},

{
    "location": "orders/orders.html#Base.parent-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Base.parent",
    "category": "method",
    "text": "parent(O::NfOrd) -> NfOrdSet\n\nReturns the parent of mathcal O, that is, the set of orders of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.isequation_order-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.isequation_order",
    "category": "method",
    "text": "isequation_order(O::NfOrd) -> Bool\n\nReturns whether mathcal O is the equation order of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/orders.html#Nemo.signature-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Nemo.signature",
    "category": "method",
    "text": "signature(O::NfOrd) -> Tuple{Int, Int}\n\nReturns the signature of the ambient number field of mathcal O.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.nf-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.nf",
    "category": "method",
    "text": "nf(O::NfOrd) -> AnticNumberField\n\nReturns the ambient number field of mathcal O.\n\n\n\n"
},

{
    "location": "orders/orders.html#AbstractAlgebra.Generic.degree-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "AbstractAlgebra.Generic.degree",
    "category": "method",
    "text": "degree(O::NfOrd) -> Int\n\nReturns the degree of mathcal O.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.basis-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.basis",
    "category": "method",
    "text": "basis(O::NfOrd) -> Array{NfOrdElem, 1}\n\nReturns the mathbf Z-basis of mathcal O.\n\n\n\n\n\nbasis(A::NfAbsOrdIdl) -> Array{NfOrdElem, 1}\n\nReturns the basis of A.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.basis-Tuple{NfAbsOrd{AnticNumberField,nf_elem},AnticNumberField}",
    "page": "Orders",
    "title": "Hecke.basis",
    "category": "method",
    "text": "basis(O::NfOrd, K::AnticNumberField) -> Array{nf_elem, 1}\n\nReturns the mathbf Z-basis elements of mathcal O as elements of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.basis_mat-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.basis_mat",
    "category": "method",
    "text": "basis_mat(O::NfOrd) -> FakeFmpqMat\n\nReturns the basis matrix of mathcal O with respect to the power basis of the ambient number field.\n\n\n\n\n\nbasis_mat(A::NfAbsOrdIdl) -> fmpz_mat\n\nReturns the basis matrix of A.\n\n\n\n\n\n  basis_mat(O::NfRelOrd{T, S}) -> Generic.Mat{T}\n\nReturns the basis matrix of mathcal O with respect to the power basis of the ambient number field.\n\n\n\n\n\n  basis_mat(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}\n  basis_mat(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}\n\nReturns the basis matrix of a.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.basis_mat_inv-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.basis_mat_inv",
    "category": "method",
    "text": "basis_mat_inv(O::NfOrd) -> FakeFmpqMat\n\nReturns the inverse of the basis matrix of mathcal O.\n\n\n\n\n\nbasis_mat_inv(A::NfAbsOrdIdl) -> fmpz_mat\n\nReturns the inverse basis matrix of A.\n\n\n\n\n\n  basis_mat_inv(O::NfRelOrd{T, S}) -> Generic.Mat{T}\n\nReturns the inverse of the basis matrix of mathcal O.\n\n\n\n\n\n  basis_mat_inv(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}\n  basis_mat_inv(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}\n\nReturns the inverse of the basis matrix of a.\n\n\n\n"
},

{
    "location": "orders/orders.html#AbstractAlgebra.Generic.discriminant-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "AbstractAlgebra.Generic.discriminant",
    "category": "method",
    "text": "discriminant(O::NfOrd) -> fmpz\n\nReturns the discriminant of mathcal O.\n\n\n\n\n\ndiscriminant(B::Array{NfAbsOrdElem, 1}) -> fmpz\n\nReturns the discriminant of the family B.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.gen_index-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.gen_index",
    "category": "method",
    "text": "gen_index(O::NfOrd) -> fmpq\n\nReturns the generalized index of mathcal O with respect to the equation order of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.index-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.index",
    "category": "method",
    "text": "index(O::NfOrd) -> fmpz\n\nAssuming that the order mathcal O contains the equation order mathbf Zalpha of the ambient number field, this function returns the index  mathcal O  mathbf Z.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.isindex_divisor-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Orders",
    "title": "Hecke.isindex_divisor",
    "category": "method",
    "text": "isindex_divisor(O::NfOrd, d::fmpz) -> Bool\nisindex_divisor(O::NfOrd, d::Int) -> Bool\n\nReturns whether d is a divisor of the index of mathcal O. It is assumed that mathcal O contains the equation order of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.minkowski_mat-Tuple{NfAbsOrd{AnticNumberField,nf_elem},Int64}",
    "page": "Orders",
    "title": "Hecke.minkowski_mat",
    "category": "method",
    "text": "minkowski_mat(O::NfOrd, abs_tol::Int = 64) -> arb_mat\n\nReturns the Minkowski matrix of mathcal O.  Thus if mathcal O has degree d, then the result is a matrix in operatornameMat_dtimes d(mathbf R). The entries of the matrix are real balls of type arb with radius less then 2^-abs_tol.\n\n\n\n"
},

{
    "location": "orders/orders.html#Base.in-Tuple{nf_elem,NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Base.in",
    "category": "method",
    "text": "in(a::nf_elem, O::NfOrd) -> Bool\n\nChecks whether a lies in mathcal O.\n\n\n\n"
},

{
    "location": "orders/orders.html#Base.denominator-Tuple{nf_elem,NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Base.denominator",
    "category": "method",
    "text": "denominator(a::nf_elem, O::NfOrd) -> fmpz\n\nReturns the smallest positive integer k such that k cdot a is contained in mathcal O.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.norm_change_const-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.norm_change_const",
    "category": "method",
    "text": "norm_change_const(O::NfOrd) -> (Float64, Float64)\n\nReturns (c_1 c_2) in mathbf R_0^2 such that for all x = sum_i=1^d x_i omega_i in mathcal O we have T_2(x) leq c_1 cdot sum_i^d x_i^2 and sum_i^d x_i^2 leq c_2 cdot T_2(x), where (omega_i)_i is the mathbf Z-basis of mathcal O.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.trace_matrix-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Hecke.trace_matrix",
    "category": "method",
    "text": "trace_matrix(O::NfOrd) -> fmpz_mat\n\nReturns the trace matrix of \\mathcal O, that is, the matrix (operatornametr_Kmathbf Q(b_i cdot b_j))_1 leq i j leq d.\n\n\n\n"
},

{
    "location": "orders/orders.html#Base.:+-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Orders",
    "title": "Base.:+",
    "category": "method",
    "text": "+(R::NfOrd, S::NfOrd) -> NfOrd\n\nGiven two orders R, S of K, this function returns the smallest order containing both R and S. It is assumed that R, S contain the ambient equation order and have coprime index.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.poverorder-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Orders",
    "title": "Hecke.poverorder",
    "category": "method",
    "text": "poverorder(O::NfOrd, p::fmpz) -> NfOrd\npoverorder(O::NfOrd, p::Integer) -> NfOrd\n\nThis function tries to find an order that is locally larger than mathcal O at the prime p: If p divides the index  mathcal O_K  mathcal O, this function will return an order R such that v_p( mathcal O_K  R)  v_p( mathcal O_K  mathcal O). Otherwise mathcal O is returned.\n\n\n\n"
},

{
    "location": "orders/orders.html#Hecke.pmaximal_overorder-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Orders",
    "title": "Hecke.pmaximal_overorder",
    "category": "method",
    "text": "pmaximal_overorder(O::NfOrd, p::fmpz) -> NfOrd\npmaximal_overorder(O::NfOrd, p::Integer) -> NfOrd\n\nThis function finds a p-maximal order R containing mathcal O. That is, the index  mathcal O_K  R is not dividible by p.\n\n\n\n"
},

{
    "location": "orders/orders.html#Example-1",
    "page": "Orders",
    "title": "Example",
    "category": "section",
    "text": "using Hecke; # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, a = NumberField(x^2 - 2, \"a\");\nO = EquationOrder(K)parent(::NfOrd)\nisequation_order(::NfOrd)\nsignature(::NfOrd)\nnf(::NfOrd)\ndegree(::NfOrd)\nbasis(::NfOrd)\nbasis(::NfOrd, ::AnticNumberField)\nbasis_mat(::NfOrd)\nbasis_mat_inv(::NfOrd)\ndiscriminant(::NfOrd)\ngen_index(::NfOrd)\nindex(::NfOrd)\nisindex_divisor(::NfOrd, ::fmpz)\nminkowski_mat(::NfOrd, ::Int)\nin(::nf_elem, ::NfOrd)\ndenominator(::nf_elem, ::NfOrd)\nnorm_change_const(::NfOrd)\ntrace_matrix(::NfOrd)\n+(::NfOrd, ::NfOrd)\npoverorder(::NfOrd, ::fmpz)\npmaximal_overorder(::NfOrd, ::fmpz)"
},

{
    "location": "orders/elements.html#",
    "page": "Elements",
    "title": "Elements",
    "category": "page",
    "text": ""
},

{
    "location": "orders/elements.html#Elements-1",
    "page": "Elements",
    "title": "Elements",
    "category": "section",
    "text": "CurrentModule = HeckeElements in orders have two representations: they can be viewed as  elements in the Z^n giving the coefficients wrt to the order basis where they are elements in. On the other hand, as every order is in a field, they also have a representation as number field elements. Since, asymptotically, operations are more efficient in the  field (due to fast polynomial arithmetic) than in the order, the primary representation is that as a field element."
},

{
    "location": "orders/elements.html#Hecke.NfAbsOrd",
    "page": "Elements",
    "title": "Hecke.NfAbsOrd",
    "category": "type",
    "text": "\n\n  (O::NfOrd)(a::Union{fmpz, Integer}) -> NfAbsOrdElem\n\nGiven an element a of type fmpz or Integer, this function coerces the element into mathcal O. It will be checked that a is contained in mathcal O if and only if check is true.\n\n\n\n\n\n  (O::NfOrd)(arr::Array{fmpz, 1})\n\nReturns the element of mathcal O with coefficient vector arr.\n\n\n\n\n\n  (O::NfOrd)() -> NfAbsOrdElem\n\nThis function constructs a new element of mathcal O which is set to 0.\n\n\n\n"
},

{
    "location": "orders/elements.html#Creation-1",
    "page": "Elements",
    "title": "Creation",
    "category": "section",
    "text": "Elements are constructed either as linear combinations of basis elements or via explicit coercion. Elements will be of type NfOrdElem,  the type if actually parametrized by the type of the surrounding field and the type of the field elements. E.g. the type of any element in any order of an absolute simple field will be NfAbsOrdElem{AnticNumberField,nf_elem}NfAbsOrd"
},

{
    "location": "orders/elements.html#Base.parent-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.parent",
    "category": "method",
    "text": "\n\nparent(a::NfAbsOrdElem) -> NfOrd\n\nReturns the order of which a is an element.\n\n\n\n"
},

{
    "location": "orders/elements.html#Hecke.elem_in_nf-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Hecke.elem_in_nf",
    "category": "method",
    "text": "\n\nelem_in_nf(a::NfAbsOrdElem) -> nf_elem\n\nReturns the element a considered as an element of the ambient number field.\n\n\n\n"
},

{
    "location": "orders/elements.html#Hecke.elem_in_basis-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Hecke.elem_in_basis",
    "category": "method",
    "text": "\n\nelem_in_basis(a::NfAbsOrdElem) -> Array{fmpz, 1}\n\nReturns the coefficient vector of a.\n\n\n\n\n\n  elem_in_basis(a::NfRelOrdElem{T}) -> Vector{T}\n\nReturns the coefficient vector of a.\n\n\n\n"
},

{
    "location": "orders/elements.html#AbstractAlgebra.Generic.discriminant-Tuple{Array{NfAbsOrdElem{AnticNumberField,nf_elem},1}}",
    "page": "Elements",
    "title": "AbstractAlgebra.Generic.discriminant",
    "category": "method",
    "text": "\n\ndiscriminant(B::Array{NfAbsOrdElem, 1}) -> fmpz\n\nReturns the discriminant of the family B.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.:==-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.:==",
    "category": "method",
    "text": "\n\n==(x::NfAbsOrdElem, y::NfAbsOrdElem) -> Bool\n\nReturns whether x and y are equal.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.zero-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.zero",
    "category": "method",
    "text": "\n\nzero(O::NfOrd) -> NfAbsOrdElem\n\nReturns the zero element of mathcal O.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.one-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.one",
    "category": "method",
    "text": "\n\none(O::NfOrd) -> NfAbsOrdElem\n\nReturns the one element of mathcal O.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.iszero-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.iszero",
    "category": "method",
    "text": "\n\niszero(a::NfOrd) -> Bool\n\nTests if a is zero.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.isone-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.isone",
    "category": "method",
    "text": "\n\nisone(a::NfOrd) -> Bool\n\nTests if a is one.\n\n\n\n"
},

{
    "location": "orders/elements.html#Basic-properties-1",
    "page": "Elements",
    "title": "Basic properties",
    "category": "section",
    "text": "parent(::NfOrdElem)\nelem_in_nf(::NfOrdElem)\nelem_in_basis(::NfOrdElem)\ndiscriminant(::Array{NfOrdElem, 1})\n==(::NfOrdElem, ::NfOrdElem)\nzero(::NfOrd)\none(::NfOrd)\niszero(::NfOrdElem)\nisone(::NfOrdElem)"
},

{
    "location": "orders/elements.html#Base.:--Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.:-",
    "category": "method",
    "text": "\n\n-(x::NfAbsOrdElem) -> NfAbsOrdElem\n\nReturns the additive inverse of x.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.:+-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.:+",
    "category": "method",
    "text": "\n\n+(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem\n\nReturns x + y.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.:--Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.:-",
    "category": "method",
    "text": "\n\n-(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem\n\nReturns x - y.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.:*-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Base.:*",
    "category": "method",
    "text": "\n\n*(x::NfAbsOrdElem, y::NfAbsOrdElem) -> NfAbsOrdElem\n\nReturns x cdot y.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.:^-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Elements",
    "title": "Base.:^",
    "category": "method",
    "text": "\n\n^(x::NfAbsOrdElem, y::Union{fmpz, Int})\n\nReturns x^y.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.mod-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Elements",
    "title": "Base.mod",
    "category": "method",
    "text": "\n\nmod(a::NfAbsOrdElem, m::Union{fmpz, Int}) -> NfAbsOrdElem\n\nReduces the coefficient vector of a modulo m and returns the corresponding element. The coefficient vector of the result will have entries x with 0 leq x leq m.\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.powermod-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},fmpz,Int64}",
    "page": "Elements",
    "title": "Base.powermod",
    "category": "method",
    "text": "\n\npowermod(a::NfAbsOrdElem, i::fmpz, m::Integer) -> NfAbsOrdElem\n\nReturns the element a^i modulo m.\n\n\n\n"
},

{
    "location": "orders/elements.html#Arithmetic-1",
    "page": "Elements",
    "title": "Arithmetic",
    "category": "section",
    "text": "-(::NfOrdElem)\n+(::NfOrdElem, ::NfOrdElem)\n-(::NfOrdElem, ::NfOrdElem)\n*(::NfOrdElem, ::NfOrdElem)\n^(::NfOrdElem, ::Int)\nmod(::NfOrdElem, ::Int)\npowermod(::NfOrdElem, ::fmpz, ::Int)"
},

{
    "location": "orders/elements.html#Nemo.representation_matrix-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "Nemo.representation_matrix",
    "category": "method",
    "text": "\n\nrepresentation_matrix(a::NfAbsOrdElem) -> fmpz_mat\n\nReturns the representation matrix of the element a.\n\n\n\n\n\nrepresentation_matrix(a::NfAbsOrdElem, K::AnticNumberField) -> FakeFmpqMat\n\nReturns the representation matrix of the element a considered as an element of the ambient number field K. It is assumed that K is the ambient number field of the order of a.\n\n\n\n"
},

{
    "location": "orders/elements.html#Nemo.representation_matrix-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},AnticNumberField}",
    "page": "Elements",
    "title": "Nemo.representation_matrix",
    "category": "method",
    "text": "\n\nrepresentation_matrix(a::NfAbsOrdElem, K::AnticNumberField) -> FakeFmpqMat\n\nReturns the representation matrix of the element a considered as an element of the ambient number field K. It is assumed that K is the ambient number field of the order of a.\n\n\n\n"
},

{
    "location": "orders/elements.html#LinearAlgebra.tr-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "LinearAlgebra.tr",
    "category": "method",
    "text": "\n\ntr(a::NfAbsOrdElem) -> fmpz\n\nReturns the trace of a.\n\n\n\n"
},

{
    "location": "orders/elements.html#LinearAlgebra.norm-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "\n\nnorm(a::NfAbsOrdElem) -> fmpz\n\nReturns the norm of a.\n\n\n\n\n\nnorm(A::NfAbsOrdIdl) -> fmpz\n\nReturns the norm of A, that is, the cardinality of mathcal OA, where mathcal O is the order of A.\n\n\n\n\n\nnorm(a::NfRelOrdIdl) -> NfOrdIdl\n\nReturns the norm of a.\n\n\n\n\n\nnorm(a::NfRelOrdFracIdl{T, S}) -> S\n\nReturns the norm of a\n\n\n\n"
},

{
    "location": "orders/elements.html#Base.rand-Tuple{NfAbsOrd{AnticNumberField,nf_elem},Int64}",
    "page": "Elements",
    "title": "Base.rand",
    "category": "method",
    "text": "\n\nrand(O::NfOrd, n::Union{Integer, fmpz}) -> NfAbsOrdElem\n\nComputes a coefficient vector with entries uniformly distributed in -ndotsc-101dotscn and returns the corresponding element of the order mathcal O.\n\n\n\n"
},

{
    "location": "orders/elements.html#Hecke.minkowski_map-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Elements",
    "title": "Hecke.minkowski_map",
    "category": "method",
    "text": "\n\nminkowski_map(a::NfAbsOrdElem, abs_tol::Int) -> Array{arb, 1}\n\nReturns the image of a under the Minkowski embedding. Every entry of the array returned is of type arb with radius less then 2^-abs_tol.\n\n\n\n"
},

{
    "location": "orders/elements.html#Hecke.conjugates_arb-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Elements",
    "title": "Hecke.conjugates_arb",
    "category": "method",
    "text": "\n\nconjugates_arb(x::NfAbsOrdElem, abs_tol::Int) -> Array{acb, 1}\n\nCompute the the conjugates of x as elements of type acb. Recall that we order the complex conjugates sigma_r+1(x)sigma_r+2s(x) such that sigma_i(x) = overlinesigma_i + s(x) for r + 2 leq i leq r + s.Every entry y of the array returned satisfies radius(real(y)) < 2^-abs_tol, radius(imag(y)) < 2^-abs_tol respectively.\n\n\n\n"
},

{
    "location": "orders/elements.html#Hecke.conjugates_arb_log-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Elements",
    "title": "Hecke.conjugates_arb_log",
    "category": "method",
    "text": "\n\nconjugates_arb_log(x::NfAbsOrdElem, abs_tol::Int) -> Array{arb, 1}\n\nReturns the elements (log(lvert sigma_1(x) rvert)dotsclog(lvertsigma_r(x) rvert) dotsc2log(lvert sigma_r+1(x) rvert)dotsc 2log(lvert sigma_r+s(x)rvert)) as elements of type arb radius less then 2^-abs_tol.\n\n\n\n"
},

{
    "location": "orders/elements.html#Hecke.t2-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},Int64}",
    "page": "Elements",
    "title": "Hecke.t2",
    "category": "method",
    "text": "\n\nt2(x::NfAbsOrdElem, abs_tol::Int = 32) -> arb\n\nReturn the T_2-norm of x. The radius of the result will be less than 2^-abs_tol.\n\n\n\n"
},

{
    "location": "orders/elements.html#AbstractAlgebra.Generic.minpoly-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "AbstractAlgebra.Generic.minpoly",
    "category": "method",
    "text": "minpoly(a::NfAbsOrdElem) -> fmpz_poly\n\nminpoly(a::NfAbsOrdElem, FlintZZ) -> fmpz_poly\n\nThe minimal polynomial of a.    \n\n\n\n"
},

{
    "location": "orders/elements.html#AbstractAlgebra.Generic.charpoly-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Elements",
    "title": "AbstractAlgebra.Generic.charpoly",
    "category": "method",
    "text": "charpoly(a::NfAbsOrdElem) -> fmpz_poly\n\ncharpoly(a::NfAbsOrdElem, FlintZZ) -> fmpz_poly\n\nThe characteristic polynomial of a.    \n\n\n\n"
},

{
    "location": "orders/elements.html#Miscallenous-1",
    "page": "Elements",
    "title": "Miscallenous",
    "category": "section",
    "text": "representation_matrix(::NfOrdElem)\nrepresentation_matrix(::NfOrdElem, ::AnticNumberField)\ntr(::NfOrdElem)\nnorm(::NfOrdElem)\nrand(::NfOrd, ::Int)\nminkowski_map(::NfOrdElem, ::Int)\nconjugates_arb(::NfOrdElem, ::Int)\nconjugates_arb_log(::NfOrdElem, ::Int)\nt2(::NfOrdElem, ::Int)\nminpoly(::NfOrdElem)\ncharpoly(::NfOrdElem)"
},

{
    "location": "orders/ideals.html#",
    "page": "Ideals",
    "title": "Ideals",
    "category": "page",
    "text": ""
},

{
    "location": "orders/ideals.html#Ideals-1",
    "page": "Ideals",
    "title": "Ideals",
    "category": "section",
    "text": "CurrentModule = Hecke(Integral) ideals in orders are always free Z-module of the same rank as the order, hence have a representation via a Z-basis. This can be made unique by normalising the corresponding matrix to be in reduced row echelon form  (HNF).For ideals in maximal orders Z_K, we also have a second presentation coming from the Z_K module structure and the fact that Z_K is a Dedekind ring: ideals can be generated by 2 elements, one of which can be any non-zero element in the ideal.For efficiency, we will choose the 1st generator to be an integer.Ideals here are of type NfAbsOrdIdl, which is, similar to the elements above, also indexed by the type of the field and their elements: NfAbsOrdIdl{AnticNumberField,nf_elem} for ideals in simple absolute fields.Different to elements, the parentof an ideal is teh set of all ideals in the ring, of type NfAbsOrdIdlSet."
},

{
    "location": "orders/ideals.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Ideals",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "\n\nideal(O::NfOrd, a::fmpz) -> NfAbsOrdIdl\nideal(O::NfOrd, a::Integer) -> NfAbsOrdIdl\n\nReturns the ideal of mathcal O which is generated by a.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz_mat}",
    "page": "Ideals",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "\n\nideal(O::NfOrd, x::fmpz_mat, check::Bool = false, x_in_hnf::Bool = false) -> NfAbsOrdIdl\n\nCreates the ideal of mathcal O with basis matrix x. If check is set, then it is checked whether x defines an ideal (expensive). If xinhnf is set, then it is assumed that x is already in lower left HNF.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "\n\nideal(O::NfOrd, x::NfOrdElem) -> NfAbsOrdIdl\n\nCreates the principal ideal (x) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz,NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "\n\nideal(O::NfOrd, x::fmpz, y::NfOrdElem) -> NfAbsOrdIdl\nideal(O::NfOrd, x::Integer, y::NfOrdElem) -> NfAbsOrdIdl\n\nCreates the ideal (xy) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl}",
    "page": "Ideals",
    "title": "Hecke.ideal",
    "category": "method",
    "text": "ideal(O::NfOrd, I::NfAbsOrdIdl) -> NfOrdFracIdl\n\nThe fractional ideal of O generated by a Z-basis of I.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.:*-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Base.:*",
    "category": "method",
    "text": "*(O::NfOrd, x::NfOrdElem) -> NfAbsOrdIdl\n*(x::NfOrdElem, O::NfOrd) -> NfAbsOrdIdl\n\nReturns the principal ideal (x) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.prime_decomposition-Tuple{NfAbsOrd{AnticNumberField,nf_elem},Integer}",
    "page": "Ideals",
    "title": "Hecke.prime_decomposition",
    "category": "method",
    "text": "\n\nprime_decomposition(O::NfOrd,\n                    p::Integer,\n                    degree_limit::Int = 0,\n                    lower_limit::Int = 0) -> Array{Tuple{NfOrdIdl, Int}, 1}\n\nReturns an array of tuples (mathfrak p_ie_i) such that p mathcal O is the product of the mathfrak p_i^e_i and mathfrak p_i neq mathfrak p_j for i neq j.If degree_limit is a nonzero integer k  0, then only those prime ideals mathfrak p with deg(mathfrak p) leq k will be returned. Similarly if \\lower_limit is a nonzero integer l  0, then only those prime ideals mathfrak p with l leq deg(mathfrak p) will be returned. Note that in this case it may happen that pmathcal O is not the product of the mathfrak p_i^e_i.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.prime_decomposition-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz}",
    "page": "Ideals",
    "title": "Hecke.prime_decomposition",
    "category": "method",
    "text": "\n\nprime_decomposition(O::NfOrd,\n                    p::Integer,\n                    degree_limit::Int = 0,\n                    lower_limit::Int = 0) -> Array{Tuple{NfOrdIdl, Int}, 1}\n\nReturns an array of tuples (mathfrak p_ie_i) such that p mathcal O is the product of the mathfrak p_i^e_i and mathfrak p_i neq mathfrak p_j for i neq j.If degree_limit is a nonzero integer k  0, then only those prime ideals mathfrak p with deg(mathfrak p) leq k will be returned. Similarly if \\lower_limit is a nonzero integer l  0, then only those prime ideals mathfrak p with l leq deg(mathfrak p) will be returned. Note that in this case it may happen that pmathcal O is not the product of the mathfrak p_i^e_i.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.factor-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.factor",
    "category": "method",
    "text": "\n\nfactor(A::NfOrdIdl) -> Dict{NfOrdIdl, Int}\n\nComputes the prime ideal factorization A as a dictionary, the keys being the prime ideal divisors: If lp = factor_dict(A), then keys(lp) are the prime ideal divisors of A and lp[P] is the P-adic valuation of A for all P in keys(lp).\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.factor-Tuple{nf_elem,Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.factor",
    "category": "method",
    "text": "factor(a::nf_elem, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}\n\nFactors the principal ideal generated by a.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Creation-1",
    "page": "Ideals",
    "title": "Creation",
    "category": "section",
    "text": "ideal(::NfOrd, ::fmpz)\nideal(::NfOrd, ::fmpz_mat)\nideal(::NfOrd, ::NfOrdElem)\nideal(::NfOrd, ::fmpz, ::NfOrdElem)\nideal(::NfOrd, ::NfAbsOrdIdl)\n*(::NfOrd, ::NfOrdElem)\nprime_decomposition(::NfOrd, ::Integer)\nprime_decomposition(::NfOrd, ::fmpz)\nfactor(::NfOrdIdl)\nfactor(::nf_elem, ::NfOrdIdlSet)"
},

{
    "location": "orders/ideals.html#Base.:==-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Base.:==",
    "category": "method",
    "text": "\n\n==(x::NfAbsOrdIdl, y::NfAbsOrdIdl)\n\nReturns whether x and y are equal.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.:+-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Base.:+",
    "category": "method",
    "text": "\n\n+(x::NfOrdIdl, y::NfOrdIdl)\n\nReturns x + y.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.:*-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Base.:*",
    "category": "method",
    "text": "*(x::NfOrdIdl, y::NfOrdIdl)\n\nReturns x cdot y.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.divexact-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.divexact",
    "category": "method",
    "text": "\n\ndivexact(A::NfOrdIdl, B::NfOrdIdl) -> NfOrdIdl\n\nReturns AB^-1 assuming that AB^-1 is again an integral ideal.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.divides-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.divides",
    "category": "method",
    "text": "\n\ndivides(A::NfOrdIdl, B::NfOrdIdl)\n\nChecks if B divides A\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.lcm-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Base.lcm",
    "category": "method",
    "text": "intersection(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl\nlcm(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl\n\nReturns x cap y.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.gcd-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Base.gcd",
    "category": "method",
    "text": "\n\ngcd(A::NfOrdIdl, B::NfOrdIdl) -> NfOrdIdl\n\nThe gcd or sum (A+B).\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.gcd-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},fmpz}",
    "page": "Ideals",
    "title": "Base.gcd",
    "category": "method",
    "text": "\n\ngcd(A::NfOrdIdl, p::fmpz) -> NfOrdIdl\n\nThe gcd or sum (A+ pO).\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.intersection-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.intersection",
    "category": "method",
    "text": "intersection(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl\nlcm(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl\n\nReturns x cap y.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.colon-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.colon",
    "category": "method",
    "text": "colon(a::NfAbsOrdIdl, b::NfAbsOrdIdl) -> NfOrdFracIdl\n\nThe ideal (ab) = x in K  xb subseteq a = hom(b a) where K is the number field.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.in-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdIdl}",
    "page": "Ideals",
    "title": "Base.in",
    "category": "method",
    "text": "\n\nin(x::NfOrdElem, y::NfAbsOrdIdl)\nin(x::nf_elem, y::NfAbsOrdIdl)\nin(x::fmpz, y::NfAbsOrdIdl)\n\nReturns whether x is contained in y.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.ispower-Tuple{NfAbsOrdIdl,Int64}",
    "page": "Ideals",
    "title": "Hecke.ispower",
    "category": "method",
    "text": "ispower(A::NfAbsOrdIdl, n::Int) -> Bool, NfAbsOrdIdl\nispower(A::NfOrdFracIdl, n::Int) -> Bool, NfOrdFracIdl\n\nComputes, if possible, an ideal B s.th. B^n==A holds. In this case, {{{true}}} and B are returned.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.ispower-Tuple{NfAbsOrdIdl}",
    "page": "Ideals",
    "title": "Hecke.ispower",
    "category": "method",
    "text": "ispower(I::NfAbsOrdIdl) -> Int, NfAbsOrdIdl\nispower(a::NfOrdFracIdl) -> Int, NfOrdFracIdl\n\nWrites a = r^e with e maximal. Note: 1 = 1^0.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.isinvertible-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.isinvertible",
    "category": "method",
    "text": "\n\nisinvertible(A::NfAbsOrdIdl) -> Bool, NfOrdFracIdl\n\nReturns true and an inverse of A or false and an ideal B such that A*B subsetneq order(A), if A is not invertible.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.isone-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Base.isone",
    "category": "method",
    "text": "\n\nisone(A::NfAbsOrdIdl) -> Bool\nisunit(A::NfAbsOrdIdl) -> Bool\n\nTests if A is the trivial ideal generated by 1.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Arithmetic-1",
    "page": "Ideals",
    "title": "Arithmetic",
    "category": "section",
    "text": "==(::NfOrdIdl, ::NfOrdIdl)\n+(::NfOrdIdl, ::NfOrdIdl)\n*(::NfOrdIdl, ::NfOrdIdl)\ndivexact(::NfOrdIdl, ::NfOrdIdl)\ndivides(::NfAbsOrdIdl{AnticNumberField,nf_elem}, ::NfAbsOrdIdl{AnticNumberField,nf_elem})\nlcm(::NfOrdIdl, ::NfOrdIdl)\ngcd(::NfOrdIdl, ::NfOrdIdl)\ngcd(::NfOrdIdl, ::fmpz)\nintersection(::NfOrdIdl, ::NfOrdIdl)\ncolon(::NfOrdIdl, ::NfOrdIdl)\nin(::NfOrdElem, ::NfAbsOrdIdl)\nispower(::NfAbsOrdIdl, ::Int)\nispower(::NfAbsOrdIdl)\nisinvertible(::NfOrdIdl)\nisone(::NfOrdIdl)"
},

{
    "location": "orders/ideals.html#Hecke.class_group-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.class_group",
    "category": "method",
    "text": "\n\nclass_group(O::NfOrd; bound = -1, method = 3, redo = false, large = 1000) -> GrpAbFinGen, Map\n\nReturns a group A and a map f from A to the set of ideals of O. The inverse of the map is the projection onto the group of ideals modulo the  group of principal ideals. \\texttt{redo} allows to trigger a re-computation, thus avoiding the cache. \\texttt{bound}, when given, is the bound for the factor base.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.class_group-Tuple{AnticNumberField}",
    "page": "Ideals",
    "title": "Hecke.class_group",
    "category": "method",
    "text": "class_group(K::AnticNumberField) -> GrpAbFinGen, Map\n\nShortcut for {{{classgroup(maximalorder(K))}}}: returns the class group as an abelian group and a map from this group to the set of ideals of the maximal order.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.picard_group-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.picard_group",
    "category": "method",
    "text": "  picard_group(O::NfOrd) -> GrpAbFinGen, MapClassGrp\n\nReturns the Picard group of O and a map from the group in the set of (invertible) ideals of O.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.ring_class_group-Tuple{NfAbsOrd}",
    "page": "Ideals",
    "title": "Hecke.ring_class_group",
    "category": "method",
    "text": "ring_class_group(O::NfAbsOrd)\n\nThe ring class group (Picard group) of O.    \n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.isprincipal-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.isprincipal",
    "category": "method",
    "text": "isprincipal(A::NfOrdIdl) -> Bool, NfOrdElem\n\nTests if A is principal and returns (mathtttrue alpha) if A = langle alpharangle of (mathttfalse 1) otherwise.  \n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.isprincipal_fac_elem-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.isprincipal_fac_elem",
    "category": "method",
    "text": "isprincipal_fac_elem(A::NfOrdIdl) -> Bool, FacElem{nf_elem, NumberField}\n\nTests if A is principal and returns (mathtttrue alpha) if A = langle alpharangle of (mathttfalse 1) otherwise.   The generator will be in factored form.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.power_class-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},fmpz}",
    "page": "Ideals",
    "title": "Hecke.power_class",
    "category": "method",
    "text": "power_class(A::NfOrdIdl, e::fmpz) -> NfOrdIdl\n\nComputes a (small) ideal in the same class as A^e\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.power_product_class-Tuple{Array{NfAbsOrdIdl{AnticNumberField,nf_elem},1},Array{fmpz,1}}",
    "page": "Ideals",
    "title": "Hecke.power_product_class",
    "category": "method",
    "text": "power_product_class(A::Array{NfOrdIdl, 1}, e::Array{fmpz, 1}) -> NfOrdIdl\n\nComputes a (small) ideal in the same class as prod A_i^e_i.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.power_reduce2-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},fmpz}",
    "page": "Ideals",
    "title": "Hecke.power_reduce2",
    "category": "method",
    "text": "\n\npower_reduce2(A::NfOrdIdl, e::fmpz) -> NfOrdIdl, FacElem{nf_elem}\n\nComputes B and alpha in factored form, such that alpha B = A^e\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.class_group_ideal_relation-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.ClassGrpCtx}",
    "page": "Ideals",
    "title": "Hecke.class_group_ideal_relation",
    "category": "method",
    "text": "class_group_ideal_relation(I::NfOrdIdl, c::ClassGrpCtx) -> nf_elem, SRow{fmpz}\n\nFinds a number field element alpha such that alpha I factors over the factor base in c.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.unit_group-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.unit_group",
    "category": "method",
    "text": "\n\nunit_group(O::NfOrd) -> GrpAbFinGen, Map\n\nReturns a group U and an isomorphism map f colon U to mathcal O^times. A set of fundamental units of mathcal O can be obtained via [ f(U[1+i]) for i in 1:unit_rank(O) ]. f(U[1]) will give a generator for the torsion subgroup.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.unit_group_fac_elem-Tuple{NfAbsOrd{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.unit_group_fac_elem",
    "category": "method",
    "text": "\n\nunit_group_fac_elem(O::NfOrd) -> GrpAbFinGen, Map\n\nReturns a group U and an isomorphism map f colon U to mathcal O^times. A set of fundamental units of mathcal O can be obtained via [ f(U[1+i]) for i in 1:unit_rank(O) ]. f(U[1]) will give a generator for the torsion subgroup. All elements will be returned in factored form.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.sunit_group-Tuple{Array{NfAbsOrdIdl{AnticNumberField,nf_elem},1}}",
    "page": "Ideals",
    "title": "Hecke.sunit_group",
    "category": "method",
    "text": "sunit_group(I::Array{NfOrdIdl, 1}) -> GrpAb, Map\n\nFor an array I of (coprime prime) ideals, find the S-unit group defined by I, ie. the group of non-zero field elements which are only divisible by ideals in I.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.sunit_group_fac_elem-Tuple{Array{NfAbsOrdIdl{AnticNumberField,nf_elem},1}}",
    "page": "Ideals",
    "title": "Hecke.sunit_group_fac_elem",
    "category": "method",
    "text": "sunit_group_fac_elem(I::Array{NfOrdIdl, 1}) -> GrpAb, Map\n\nFor an array I of (coprime prime) ideals, find the S-unit group defined by I, ie. the group of non-zero field elements which are only divisible by ideals in I. The map will return elements in factored form.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.sunit_mod_units_group_fac_elem-Tuple{Array{NfAbsOrdIdl{AnticNumberField,nf_elem},1}}",
    "page": "Ideals",
    "title": "Hecke.sunit_mod_units_group_fac_elem",
    "category": "method",
    "text": "sunit_mod_units_group_fac_elem(I::Array{NfOrdIdl, 1}) -> GrpAb, Map\n\nFor an array I of (coprime prime) ideals, find the S-unit group defined by I, ie. the group of non-zero field elements which are only divisible by ideals in I modulo the units of the field. The map will return elements in factored form.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Class-Group-1",
    "page": "Ideals",
    "title": "Class Group",
    "category": "section",
    "text": "The group of invertable ideals in any order forms a group and the principal ideals a subgroup.  The finite quotient is called class group for maximal orders and Picard group or ring class group in general.class_group(::NfOrd)\nclass_group(::AnticNumberField)\npicard_group(::NfOrd)\nring_class_group(::NfAbsOrd)using Hecke # hide\nk, a = wildanger_field(3, 13);\nzk = maximal_order(k);\nc, mc = class_group(zk)\nlp = prime_ideals_up_to(zk, 20);\n[ mc \\ I for I = lp]\nmc(c[1])\norder(c[1])\nmc(c[1])^Int(order(c[1]))\nmc \\ ansThe class group, or more precisely the information used to compute it also allows for principal ideal testing and related tasks.  In general, due to the size of the objetcs, the fac_elem versions are more effcient.Hecke.isprincipal(::NfOrdIdl)\nisprincipal_fac_elem(::NfAbsOrdIdl{AnticNumberField,nf_elem})\npower_class(::NfOrdIdl,::fmpz)\npower_product_class(::Array{NfOrdIdl, 1}, ::Array{fmpz, 1})\npower_reduce2(::NfAbsOrdIdl{AnticNumberField,nf_elem},::fmpz)\nclass_group_ideal_relation(::NfAbsOrdIdl{AnticNumberField,nf_elem}, ::Hecke.ClassGrpCtx)I = mc(c[1])\nHecke.isprincipal(I)\nI = I^Int(order(c[1]))\nHecke.isprincipal(I)\nHecke.isprincipal_fac_elem(I)The computation of S-units is also tied to the class group:unit_group(::NfOrd)\nunit_group_fac_elem(::NfOrd)\nHecke.sunit_group(::Array{NfOrdIdl, 1})\nHecke.sunit_group_fac_elem(::Array{NfOrdIdl, 1})\nHecke.sunit_mod_units_group_fac_elem(::Array{NfOrdIdl, 1})u, mu = unit_group(zk)\nmu(u[2])\nu, mu = unit_group_fac_elem(zk)\nmu(u[2])\nevaluate(ans)\nlp = factor(6*zk)\ns, ms = Hecke.sunit_group(collect(keys(lp)))\nms(s[4])\nnorm(ans)\nfactor(numerator(ans))"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.order-Tuple{NfAbsOrdIdl}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.order",
    "category": "method",
    "text": "\n\norder(I::NfAbsOrdIdl) -> NfOrd\n\nReturns the order of I.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.nf-Tuple{NfAbsOrdIdl}",
    "page": "Ideals",
    "title": "Hecke.nf",
    "category": "method",
    "text": "\n\nnf(x::NfAbsOrdIdl) -> AnticNumberField\n\nReturns the number field, of which x is an integral ideal.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.basis-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.basis",
    "category": "method",
    "text": "basis(O::NfOrd) -> Array{NfOrdElem, 1}\n\nReturns the mathbf Z-basis of mathcal O.\n\n\n\n\n\nbasis(A::NfAbsOrdIdl) -> Array{NfOrdElem, 1}\n\nReturns the basis of A.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.basis_mat-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.basis_mat",
    "category": "method",
    "text": "basis_mat(O::NfOrd) -> FakeFmpqMat\n\nReturns the basis matrix of mathcal O with respect to the power basis of the ambient number field.\n\n\n\n\n\nbasis_mat(A::NfAbsOrdIdl) -> fmpz_mat\n\nReturns the basis matrix of A.\n\n\n\n\n\n  basis_mat(O::NfRelOrd{T, S}) -> Generic.Mat{T}\n\nReturns the basis matrix of mathcal O with respect to the power basis of the ambient number field.\n\n\n\n\n\n  basis_mat(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}\n  basis_mat(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}\n\nReturns the basis matrix of a.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.basis_mat_inv-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.basis_mat_inv",
    "category": "method",
    "text": "basis_mat_inv(O::NfOrd) -> FakeFmpqMat\n\nReturns the inverse of the basis matrix of mathcal O.\n\n\n\n\n\nbasis_mat_inv(A::NfAbsOrdIdl) -> fmpz_mat\n\nReturns the inverse basis matrix of A.\n\n\n\n\n\n  basis_mat_inv(O::NfRelOrd{T, S}) -> Generic.Mat{T}\n\nReturns the inverse of the basis matrix of mathcal O.\n\n\n\n\n\n  basis_mat_inv(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}\n  basis_mat_inv(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}\n\nReturns the inverse of the basis matrix of a.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.assure_has_basis_mat_inv-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.assure_has_basis_mat_inv",
    "category": "method",
    "text": "\n\nbasis_mat_inv(A::NfAbsOrdIdl) -> FakeFmpqMat\n\nReturns the inverse of the basis matrix of A.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.has_basis-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.has_basis",
    "category": "method",
    "text": "\n\nhas_basis(A::NfAbsOrdIdl) -> Bool\n\nReturns whether A has a basis already computed.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.has_basis_mat-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.has_basis_mat",
    "category": "method",
    "text": "\n\nhas_basis_mat(A::NfAbsOrdIdl) -> Bool\n\nReturns whether A knows its basis matrix.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.has_2_elem-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.has_2_elem",
    "category": "method",
    "text": "\n\nhas_2_elem(A::NfAbsOrdIdl) -> Bool\n\nReturns whether A is generated by two elements.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.has_2_elem_normal-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.has_2_elem_normal",
    "category": "method",
    "text": "\n\nhas_2_elem_normal(A::NfAbsOrdIdl) -> Bool\n\nReturns whether A has normal two element generators.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.has_weakly_normal-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.has_weakly_normal",
    "category": "method",
    "text": "\n\nhas_weakly_normal(A::NfAbsOrdIdl) -> Bool\n\nReturns whether A has weakly normal two element generators.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.has_princ_gen_special-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.has_princ_gen_special",
    "category": "method",
    "text": "\n\nhas_basis_princ_gen_special(A::NfAbsOrdIdl) -> Bool\n\nReturns whether A knows if it is generated by a rational integer.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.principal_gen-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.principal_gen",
    "category": "method",
    "text": "principal_gen(A::NfOrdIdl) -> NfOrdElem\n\nFor a principal ideal A, find a generator.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.principal_gen_fac_elem-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.principal_gen_fac_elem",
    "category": "method",
    "text": "principal_gen_fac_elem(A::NfOrdIdl) -> FacElem{nf_elem, NumberField}\n\nFor a principal ideal A, find a generator in factored form.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.minimum-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Base.minimum",
    "category": "method",
    "text": "\n\nminimum(A::NfAbsOrdIdl) -> fmpz\n\nReturns the smallest nonnegative element in A cap mathbf Z.\n\n\n\n\n\n  minimum(A::NfRelOrdIdl) -> NfOrdIdl\n  minimum(A::NfRelOrdIdl) -> NfRelOrdIdl\n\nReturns the ideal A cap O where O is the maximal order of the coefficient ideals of A.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.has_minimum-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.has_minimum",
    "category": "method",
    "text": "\n\nhas_minimum(A::NfAbsOrdIdl) -> Bool\n\nReturns whether A knows its mininum.\n\n\n\n"
},

{
    "location": "orders/ideals.html#LinearAlgebra.norm-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "\n\nnorm(A::NfAbsOrdIdl) -> fmpz\n\nReturns the norm of A, that is, the cardinality of mathcal OA, where mathcal O is the order of A.\n\n\n\n\n\nnorm(a::NfRelOrdIdl) -> NfOrdIdl\n\nReturns the norm of a.\n\n\n\n\n\nnorm(a::NfRelOrdFracIdl{T, S}) -> S\n\nReturns the norm of a\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.has_norm-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.has_norm",
    "category": "method",
    "text": "\n\nhas_norm(A::NfAbsOrdIdl) -> Bool\n\nReturns whether A knows its norm.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.idempotents-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.idempotents",
    "category": "method",
    "text": "idempotents(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdElem, NfOrdElem\n\nReturns a tuple (e, f) consisting of elements e in x, f in y such that 1 = e + f.If the ideals are not coprime, an error is raised.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Nemo.isprime-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Nemo.isprime",
    "category": "method",
    "text": "\n\nisprime(A::NfOrdIdl) -> Bool\n\nReturns whether A is a prime ideal.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.isprime_known-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.isprime_known",
    "category": "method",
    "text": "\n\nisprime_known(A::NfOrdIdl) -> Bool\n\nReturns whether A knows if it is prime.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.splitting_type-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.splitting_type",
    "category": "method",
    "text": "\n\nsplitting_type(P::NfOrdIdl) -> Int, Int\n\nThe ramification index and inertia degree of the prime ideal P. First value is the ramificatio index, the second the degree of P.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.isramified-Tuple{NfAbsOrd{AnticNumberField,nf_elem},Union{Int64, fmpz}}",
    "page": "Ideals",
    "title": "Hecke.isramified",
    "category": "method",
    "text": "\n\nisramified(O::NfOrd, p::Int) -> Bool\n\nReturns whether the integer p is ramified in mathcal O. It is assumed that p is prime.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Hecke.ramification_index-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.ramification_index",
    "category": "method",
    "text": "\n\nramification_index(P::NfOrdIdl) -> Int\n\nThe ramification index of the prime-ideal P.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.degree-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.degree",
    "category": "method",
    "text": "\n\ndegree(P::NfOrdIdl) -> Int\n\nThe inertia degree of the prime-ideal P.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.valuation-Tuple{nf_elem,NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "\n\nvaluation(a::nf_elem, p::NfOrdIdl) -> fmpz\nvaluation(a::NfOrdElem, p::NfOrdIdl) -> fmpz\nvaluation(a::fmpz, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of a, that is, the largest i such that a is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.valuation-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "\n\nvaluation(a::nf_elem, p::NfOrdIdl) -> fmpz\nvaluation(a::NfOrdElem, p::NfOrdIdl) -> fmpz\nvaluation(a::fmpz, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of a, that is, the largest i such that a is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.valuation-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "\n\nvaluation(A::NfOrdIdl, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of A, that is, the largest i such that A is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.valuation-Tuple{Integer,NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "valuation(a::Integer, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of a, that is, the largest i such that a is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.valuation-Tuple{fmpz,NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "\n\nvaluation(a::nf_elem, p::NfOrdIdl) -> fmpz\nvaluation(a::NfOrdElem, p::NfOrdIdl) -> fmpz\nvaluation(a::fmpz, p::NfOrdIdl) -> fmpz\n\nComputes the mathfrak p-adic valuation of a, that is, the largest i such that a is contained in mathfrak p^i.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.Generic.valuation-Tuple{Hecke.NfOrdFracIdl,NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "valuation(A::NfOrdFracIdl, p::NfOrdIdl)\n\nThe valuation of A at p.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Miscaellenous-1",
    "page": "Ideals",
    "title": "Miscaellenous",
    "category": "section",
    "text": "order(::NfAbsOrdIdl)\nnf(::NfAbsOrdIdl)\nbasis(::NfOrdIdl)\nbasis_mat(::NfOrdIdl)\nbasis_mat_inv(::NfOrdIdl)\nHecke.assure_has_basis_mat_inv(::NfOrdIdl)\nHecke.has_basis(::NfOrdIdl)\nHecke.has_basis_mat(::NfOrdIdl)\nHecke.has_2_elem(::NfOrdIdl)\nHecke.has_2_elem_normal(::NfOrdIdl)\nHecke.has_weakly_normal(::NfOrdIdl)\nHecke.has_princ_gen_special(::NfOrdIdl)\nHecke.principal_gen(::NfOrdIdl)\nHecke.principal_gen_fac_elem(::NfOrdIdl)\nminimum(::NfOrdIdl)\n#minimum(m::T, I::NfOrdIdl) where T <: (AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)\nhas_minimum(::NfOrdIdl)\nnorm(::NfOrdIdl)\nHecke.has_norm(::NfOrdIdl)\nidempotents(::NfOrdIdl, ::NfOrdIdl)\nisprime(::NfOrdIdl)\nHecke.isprime_known(::NfOrdIdl)\nsplitting_type(::NfOrdIdl)\nisramified(::NfOrd, ::Union{Int, fmpz})\nramification_index(::NfOrdIdl)\ndegree(::NfOrdIdl)\nvaluation(::nf_elem, ::NfOrdIdl)\nvaluation(::NfOrdElem, ::NfOrdIdl)\nvaluation(::NfOrdIdl, ::NfOrdIdl)\nvaluation(::Integer, ::NfOrdIdl)\nvaluation(::fmpz, ::NfOrdIdl)\nvaluation(::NfOrdFracIdl, ::NfOrdIdl)"
},

{
    "location": "orders/ideals.html#Hecke.quo-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "Hecke.quo",
    "category": "method",
    "text": "quo(O::NfOrd, I::NfOrdIdl) -> NfOrdQuoRing, Map\n\nThe quotient ring OI as a ring together with the section M OI to O. The pointwise inverse of M is the canonical projection Oto OI.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.ResidueRing-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.ResidueRing",
    "category": "method",
    "text": "ResidueRing(O::NfOrd, I::NfOrdIdl) -> NfOrdQuoRing\n\nThe quotient ring O modulo I as a new ring.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.ResidueField-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem},Bool}",
    "page": "Ideals",
    "title": "AbstractAlgebra.ResidueField",
    "category": "method",
    "text": "ResidueField(O::NfOrd, P::NfOrdIdl, check::Bool = true) -> Field, Map\n\nReturns the residue field of the prime ideal P together with th projection map. If check is true, the ideal is checked for  being prime.\n\n\n\n"
},

{
    "location": "orders/ideals.html#Base.mod-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdIdl}",
    "page": "Ideals",
    "title": "Base.mod",
    "category": "method",
    "text": "\n\nmod(x::NfOrdElem, I::NfAbsOrdIdl)\n\nReturns the unique element y of the ambient order of x with x equiv y bmod I and the following property: If a_1dotsca_d in Z_geq 1 are the diagonal entries of the unique HNF basis matrix of I and (b_1dotscb_d) is the coefficient vector of y, then 0 leq b_i  a_i for 1 leq i leq d.\n\n\n\n"
},

{
    "location": "orders/ideals.html#AbstractAlgebra.crt-Tuple{NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Ideals",
    "title": "AbstractAlgebra.crt",
    "category": "method",
    "text": "crt(r1::NfOrdElem, i1::NfOrdIdl, r2::NfOrdElem, i2::NfOrdIdl) -> NfOrdElem\n\nFind x s.th x equiv r1 bmod i1 and x equiv r2 bmod i2\n\nusing (((idempotents)))\n\n\n\n"
},

{
    "location": "orders/ideals.html#Quotient-Rings-1",
    "page": "Ideals",
    "title": "Quotient Rings",
    "category": "section",
    "text": "quo(::NfOrd, ::NfOrdIdl)\nResidueRing(::NfOrd, ::NfOrdIdl)\nResidueField(::NfOrd, ::NfOrdIdl, ::Bool)\nmod(::NfOrdElem, ::NfAbsOrdIdl)\ncrt(::NfOrdElem, ::NfOrdIdl, ::NfOrdElem, ::NfOrdIdl)"
},

{
    "location": "orders/frac_ideals.html#",
    "page": "Fractional ideals",
    "title": "Fractional ideals",
    "category": "page",
    "text": ""
},

{
    "location": "orders/frac_ideals.html#Fractional-ideals-1",
    "page": "Fractional ideals",
    "title": "Fractional ideals",
    "category": "section",
    "text": "CurrentModule = HeckeA fractional ideal in the number field K is a Z_K-module A such that there exists an integer d0 wich dA is an (integral) ideal in Z_K. Due to the Dedekind property of Z_K, the ideals for a multiplicative group.Fractional ideals are represented as an integral ideal and an additional denominator. They are of type NfOrdFracIdl."
},

{
    "location": "orders/frac_ideals.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz_mat}",
    "page": "Fractional ideals",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, A::fmpz_mat, b::fmpz, A_in_hnf::Bool = false) -> NfOrdFracIdl\n\nCreates the fractional ideal of mathcal O with basis matrix Ab. If Ainhnf is set, then it is assumed that A is already in lower left HNF.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},fmpz_mat,fmpz}",
    "page": "Fractional ideals",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, A::fmpz_mat, b::fmpz, A_in_hnf::Bool = false) -> NfOrdFracIdl\n\nCreates the fractional ideal of mathcal O with basis matrix Ab. If Ainhnf is set, then it is assumed that A is already in lower left HNF.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},FakeFmpqMat}",
    "page": "Fractional ideals",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, A::FakeFmpqMat, A_in_hnf::Bool = false) -> NfOrdFracIdl\n\nCreates the fractional ideal of mathcal O with basis matrix A. If Ainhnf is set, then it is assumed that the numerator of A is already in lower left HNF.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Fractional ideals",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, I::NfOrdIdl) -> NfOrdFracIdl\n\nTurns the ideal I into a fractional ideal of mathcal O.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem},fmpz}",
    "page": "Fractional ideals",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, I::NfOrdIdl, b::fmpz) -> NfOrdFracIdl\n\nCreates the fractional ideal Ib of mathcal O.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},nf_elem}",
    "page": "Fractional ideals",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, a::nf_elem) -> NfOrdFracIdl\n\nCreates the principal fractional ideal (a) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.frac_ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}",
    "page": "Fractional ideals",
    "title": "Hecke.frac_ideal",
    "category": "method",
    "text": "\n\nfrac_ideal(O::NfOrd, a::NfOrdElem) -> NfOrdFracIdl\n\nCreates the principal fractional ideal (a) of mathcal O.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Base.inv-Tuple{NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Fractional ideals",
    "title": "Base.inv",
    "category": "method",
    "text": "\n\ninv(A::NfAbsOrdIdl) -> NfOrdFracIdl\n\nComputes the inverse of A, that is, the fractional ideal B such that AB = mathcal O_K.\n\n\n\n\n\n  inv(a::NfRelOrdIdl) -> NfRelOrdFracIdl\n  inv(a::NfRelOrdFracIdl) -> NfRelOrdFracIdl\n\nComputes the inverse of a, that is, the fractional ideal b such that ab = O, where O is the ambient order of a. O must be maximal.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Creation-1",
    "page": "Fractional ideals",
    "title": "Creation",
    "category": "section",
    "text": "frac_ideal(::NfOrd, ::fmpz_mat)\nfrac_ideal(::NfOrd, ::fmpz_mat, ::fmpz)\nfrac_ideal(::NfOrd, ::FakeFmpqMat)\nfrac_ideal(::NfOrd, ::NfOrdIdl)\nfrac_ideal(::NfOrd, ::NfOrdIdl, ::fmpz)\nfrac_ideal(::NfOrd, ::nf_elem)\nfrac_ideal(::NfOrd, ::NfOrdElem)\ninv(::NfOrdIdl)"
},

{
    "location": "orders/frac_ideals.html#Base.:==-Tuple{Hecke.NfOrdFracIdl,Hecke.NfOrdFracIdl}",
    "page": "Fractional ideals",
    "title": "Base.:==",
    "category": "method",
    "text": "\n\n==(x::NfOrdFracIdl, y::NfOrdFracIdl) -> Bool\n\nReturns whether x and y are equal.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Base.inv-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Fractional ideals",
    "title": "Base.inv",
    "category": "method",
    "text": "\n\ninv(A::NfOrdFracIdl) -> NfOrdFracIdl\n\nReturns the fractional ideal B such that AB = mathcal O.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.integral_split-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Fractional ideals",
    "title": "Hecke.integral_split",
    "category": "method",
    "text": "\n\nintegral_split(A::NfOrdFracIdl) -> NfOrdIdl, NfOrdIdl\n\nComputes the unique coprime integral ideals N and D s.th. A = ND^-1\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Arithmetic-1",
    "page": "Fractional ideals",
    "title": "Arithmetic",
    "category": "section",
    "text": "==(::NfOrdFracIdl, ::NfOrdFracIdl)\ninv(::NfOrdFracIdl)\nintegral_split(::NfOrdFracIdl)"
},

{
    "location": "orders/frac_ideals.html#AbstractAlgebra.Generic.order-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Fractional ideals",
    "title": "AbstractAlgebra.Generic.order",
    "category": "method",
    "text": "order(a::NfOrdFracIdl) -> NfOrd\n\nThe order that was used to define the ideal a.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.basis_mat-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Fractional ideals",
    "title": "Hecke.basis_mat",
    "category": "method",
    "text": "\n\nbasis_mat(I::NfOrdFracIdl) -> FakeFmpqMat\n\nReturns the basis matrix of I with respect to the basis of the order.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.basis_mat_inv-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Fractional ideals",
    "title": "Hecke.basis_mat_inv",
    "category": "method",
    "text": "\n\nbasis_mat_inv(I::NfOrdFracIdl) -> FakeFmpqMat\n\nReturns the inverse of the basis matrix of I.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Hecke.basis-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Fractional ideals",
    "title": "Hecke.basis",
    "category": "method",
    "text": "\n\nbasis(I::NfOrdFracIdl) -> Array{nf_elem, 1}\n\nReturns the mathbf Z-basis of I.\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#LinearAlgebra.norm-Tuple{Hecke.NfOrdFracIdl}",
    "page": "Fractional ideals",
    "title": "LinearAlgebra.norm",
    "category": "method",
    "text": "\n\nnorm(I::NfOrdFracIdl) -> fmpq\n\nReturns the norm of I\n\n\n\n"
},

{
    "location": "orders/frac_ideals.html#Miscaellenous-1",
    "page": "Fractional ideals",
    "title": "Miscaellenous",
    "category": "section",
    "text": "order(::NfOrdFracIdl)\nbasis_mat(::NfOrdFracIdl)\nbasis_mat_inv(::NfOrdFracIdl)\nbasis(::NfOrdFracIdl)\nnorm(::NfOrdFracIdl)"
},

{
    "location": "abelian/introduction.html#",
    "page": "Abelian Groups",
    "title": "Abelian Groups",
    "category": "page",
    "text": ""
},

{
    "location": "abelian/introduction.html#Abelian-Groups-1",
    "page": "Abelian Groups",
    "title": "Abelian Groups",
    "category": "section",
    "text": ""
},

{
    "location": "abelian/introduction.html#Introduction-1",
    "page": "Abelian Groups",
    "title": "Introduction",
    "category": "section",
    "text": ""
},

{
    "location": "class_fields/intro.html#",
    "page": "Class Field Theory",
    "title": "Class Field Theory",
    "category": "page",
    "text": ""
},

{
    "location": "class_fields/intro.html#Class-Field-Theory-1",
    "page": "Class Field Theory",
    "title": "Class Field Theory",
    "category": "section",
    "text": "CurrentModule = Hecke"
},

{
    "location": "class_fields/intro.html#Introduction-1",
    "page": "Class Field Theory",
    "title": "Introduction",
    "category": "section",
    "text": "This chapter deals with abelian extensions of number fields and the rational numbers.Class Field Theory, here specifically, class field theory of global number fields, deals with abelian extension, ie. fields where the group of automorphisms is abelian. For extensions of {\\Q}, the famous Kronnecker-Weber theorem classifies all such fields: a field is abelian if and only if it is contained in some cyclotomic field. For general number fields this is more involved and even for extensions of {\\Q} is is not practical.In Hecke, abelian extensions are parametrized by quotients of so called ray class groups. The language of ray class groups while dated is more applicable to algorithms than the modern language of idel class groups and quotients."
},

{
    "location": "class_fields/intro.html#Ray-Class-Groups-1",
    "page": "Class Field Theory",
    "title": "Ray Class Groups",
    "category": "section",
    "text": "Given an integral ideal m_0 le Z_K and a list of real places m_infty, the ray class group modulo (m_0 m_infty), C(m) is defined as the group of ideals coprime to m_0 modulo the elements ain K^* s.th. v_p(a-1) ge v_p(m_0) and for all vin m_infty, a^(v) 0. This is a finite abelian group. For m_0 = Z_K and m_infty =  we get C() is the class group, if m_infty contains all real places, we obtain the narrow class group, or strict class group.ray_class_group(m::Hecke.NfAbsOrdIdl{Nemo.AnticNumberField,Nemo.nf_elem}, inf_plc::Array{Hecke.InfPlc,1}; p_part, n_quo)\nclass_group(O::Hecke.NfAbsOrd{Nemo.AnticNumberField,Nemo.nf_elem}; bound, method, redo, unit_method, large)\nclass_group(K::Nemo.AnticNumberField)\nnorm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp, isabelian::Bool)\nnorm_group(K::NfRel{nf_elem}, mR::Hecke.MapRayClassGrp, isabelian::Bool)"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{Union{MapClassGrp, MapRayClassGrp}}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(m::MapClassGrp) -> ClassField\nray_class_field(m::MapRayClassGrp) -> ClassField\n\nCreates the (formal) abelian extension defined by the map m A to I where I is the set of ideals coprime to the modulus defining m and A  is a quotient of the ray class group (or class group). The map m must be the map returned from a call to {classgroup} or {rayclass_group}.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{Union{MapClassGrp, MapRayClassGrp},GrpAbFinGenMap}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(m::Union{MapClassGrp, MapRayClassGrp}, quomap::GrpAbFinGenMap) -> ClassField\n\nFor m a map computed by either {rayclassgroup} or {class_group} and q a canonical projection (quotient map) as returned by {quo} for q  quotient of the domain of m and a subgroup of m, create the (formal) abelian extension where the (relative) automorphism group is canonically isomorphic to the codomain of q.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{NfAbsOrdIdl}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(I::NfAbsOrdIdl; n_quo = 0) -> ClassField\n\nThe ray class field modulo I. If {{{n_quo}}} is given, then the largest subfield of exponent n is computed.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{NfAbsOrdIdl,Array{InfPlc,1}}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(I::NfAbsOrdIdl, inf::Array{InfPlc, 1}; n_quo = 0) -> ClassField\n\nThe ray class field modulo I and the infinite places given. If {{{n_quo}}} is given, then the largest subfield of exponent n is computed.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.hilbert_class_field-Tuple{AnticNumberField}",
    "page": "Class Field Theory",
    "title": "Hecke.hilbert_class_field",
    "category": "method",
    "text": "hilbert_class_field(k::AnticNumberField) -> ClassField\n\nThe Hilbert class field of k as a formal (ray-) class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.ring_class_field-Tuple{NfAbsOrd}",
    "page": "Class Field Theory",
    "title": "Hecke.ring_class_field",
    "category": "method",
    "text": "ring_class_field(O::NfAbsOrd) -> ClassField\n\nThe ring class field of O, ie. the maximal abelian extension ramifed  only at primes dividing the conductor with the automorphism group isomorphic to the Picard group.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Ray-Class-Fields-1",
    "page": "Class Field Theory",
    "title": "Ray Class Fields",
    "category": "section",
    "text": "In general, the construction of a class field starts with a (ray) class group. Each quotient of a ray class group then defines a ray class field, the defining property is that the (relative) automorphism group is canonically isomorphic to the quotient of the ray class group where the isomorphism is given by the Artin (or Frobenius) map. Since, in Hecke, the (ray) class groups have no link to the field, actually this has to be specified using the maps.It should be noted that this is a {\\em lazy} construction: nothing is computed at this point.ray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp})\nray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp}, quomap::Hecke.GrpAbFinGenMap)\nray_class_field(I::Hecke.NfAbsOrdIdl; n_quo, p_part)\nray_class_field(I::Hecke.NfAbsOrdIdl, ::Array{InfPlc, 1}; n_quo, p_part)\nhilbert_class_field(k::AnticNumberField)\nring_class_field(::NfAbsOrd)"
},

{
    "location": "class_fields/intro.html#Example-1",
    "page": "Class Field Theory",
    "title": "Example",
    "category": "section",
    "text": "using Hecke # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nK, a = NumberField(x^2 - 10, \"a\");\nc, mc = class_group(K)\nA = ray_class_field(mc)"
},

{
    "location": "class_fields/intro.html#Hecke.number_field-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.number_field",
    "category": "method",
    "text": "NumberField(f::Generic.Poly{T}, s::String; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\nNumberField(f::Generic.Poly{T}; cached::Bool = false, check::Bool = false) where T\n\nGiven an irreducible polynomial f over some number field K, create the field Ktf. f must be irreducible - although this is not tested.\n\n\n\nnumber_field(f::Array{Generic.Poly{T}, 1}, s::String=\"_\\$\") where T -> NfRel_ns\n\nGiven polynomials f = (f_1 ldots f_n) over some number field k, construct K = kt_1 ldots t_nlangle f_1(t_1) ldots f_n(t_n)rangle The ideal in the quotient must be maximal - although this is not tested.\n\n\n\nNumberField(CF::ClassField) -> Hecke.NfRel_ns{Nemo.nf_elem}\n\nGiven a (formal) abelian extension, compute the class field by finding defining polynomials for all prime power cyclic subfields. Note, by type this is always a non-simple extension.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.ray_class_field-Tuple{Hecke.NfRel{nf_elem}}",
    "page": "Class Field Theory",
    "title": "Hecke.ray_class_field",
    "category": "method",
    "text": "ray_class_field(K::NfRel{nf_elem}) -> ClassField\n\nFor a (relative) abelian extension, compute an abstract representation as a class field. \n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.genus_field-Tuple{Hecke.ClassField,AnticNumberField}",
    "page": "Class Field Theory",
    "title": "Hecke.genus_field",
    "category": "method",
    "text": "genus_field(A::ClassField, k::AnticNumberField) -> ClassField\n\nThe maximal extension contained in A that is the compositum of K with an abelian extension of k.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.maximal_abelian_subfield-Tuple{Hecke.ClassField,AnticNumberField}",
    "page": "Class Field Theory",
    "title": "Hecke.maximal_abelian_subfield",
    "category": "method",
    "text": "maximal_abelian_subfield(A::ClassField, k::AnticNumberField) -> ClassField\n\nThe maximal abelian extension of k contained in A. k must be a subfield of the base field of A.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.maximal_abelian_subfield-Tuple{Hecke.NfRel{nf_elem}}",
    "page": "Class Field Theory",
    "title": "Hecke.maximal_abelian_subfield",
    "category": "method",
    "text": "maximal_abelian_subfield(K::NfRel{nf_elem}; of_closure::Bool = false) -> ClassField\n\nUsing a probabilistic algorithm for the norm group computation, determine tha maximal abelian subfield in K over its base field. If {{{of_closure}}} is set to true, then the algorithm is applied to the normal closure if K (without computing it).\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Conversions-1",
    "page": "Class Field Theory",
    "title": "Conversions",
    "category": "section",
    "text": "Given a ray class field, it is possible to actually compute defining equation(s) for this field. In general, the number field constructed this way will be non-simple by type and is defined by a polynomial for each maximal cyclic quotient of prime power order in the defining group.The algorithm employed is based on Kummer-theory and requires the addition of a suitable root of unity. Progress can be monitored by setting {{{setverboselevel(:ClassField, n)}}} where 0le nle 3number_field(C::ClassField)using Hecke; # hide\nQx, x = PolynomialRing(FlintQQ, \"x\");\nk, a = NumberField(x^2 - 10, \"a\");\nc, mc = class_group(k);\nA = ray_class_field(mc)\nK = number_field(A)\nZK = maximal_order(K)\nisone(discriminant(ZK))ray_class_field(K::NfRel{nf_elem})\ngenus_field(A::ClassField, k::AnticNumberField)\nmaximal_abelian_subfield(A::ClassField, k::AnticNumberField)\nmaximal_abelian_subfield(K::NfRel{nf_elem})"
},

{
    "location": "class_fields/intro.html#AbstractAlgebra.Generic.degree-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "AbstractAlgebra.Generic.degree",
    "category": "method",
    "text": "degree(A::ClassField)\n\nThe degree of A over its base field, ie. the size of the defining ideal group.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#AbstractAlgebra.Generic.base_ring-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "AbstractAlgebra.Generic.base_ring",
    "category": "method",
    "text": "base_ring(A::ClassField)\n\nThe maximal order of the field that A is defined over.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.base_field-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.base_field",
    "category": "method",
    "text": "base_field(A::ClassField)\n\nThe number field that A is defined over.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#AbstractAlgebra.Generic.discriminant-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "AbstractAlgebra.Generic.discriminant",
    "category": "method",
    "text": "discriminant(C::ClassField) -> NfOrdIdl\n\nUsing the conductor-discriminant formula, compute the (relative) discriminant of C. This does not use the defining equations.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.conductor-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.conductor",
    "category": "method",
    "text": "\n\nconductor(C::Hecke.ClassField) -> NfOrdIdl, Array{InfPlc,1}\n\nReturn the conductor of the abelian extension corresponding to C\n\n\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.defining_modulus-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.defining_modulus",
    "category": "method",
    "text": "defining_modulus(CF::ClassField)\n\nThe modulus, ie. an ideal the the set of real places, used to create the class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.iscyclic-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.iscyclic",
    "category": "method",
    "text": "iscyclic(C::ClassField)\n\nTests if the (relative) automorphism group of C is cyclic (by checking the defining ideal group).\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.isconductor-Tuple{Hecke.ClassField,NfAbsOrdIdl{AnticNumberField,nf_elem},Array{InfPlc,1}}",
    "page": "Class Field Theory",
    "title": "Hecke.isconductor",
    "category": "method",
    "text": "\n\nisconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; check) -> NfOrdIdl, Array{InfPlc,1}\n\nChecks if m, inf_plc is the conductor of the abelian extension corresponding to C. If check is false, it assumes that the  given modulus is a multiple of the conductor. This is generically faster than computing the conductor.\n\n\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.isnormal-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.isnormal",
    "category": "method",
    "text": "isnormal(C::ClassField) -> Bool\n\nFor a class field C defined over a normal base field k, decide if C is normal over Q.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.iscentral-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.iscentral",
    "category": "method",
    "text": "iscentral(C::ClassField) -> Bool\n\nFor a class field C defined over a normal base field k, decide if C is central over Q.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Invariants-1",
    "page": "Class Field Theory",
    "title": "Invariants",
    "category": "section",
    "text": "degree(C::ClassField)\nbase_ring(A::Hecke.ClassField) \nbase_field(A::Hecke.ClassField) \ndiscriminant(C::Hecke.ClassField)\nconductor(C::Hecke.ClassField) \ndefining_modulus(C::ClassField)\niscyclic(C::ClassField)\nisconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1})\nisnormal(C::ClassField)\niscentral(C::ClassField)"
},

{
    "location": "class_fields/intro.html#Base.:*-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Base.:*",
    "category": "method",
    "text": "*(A::ClassField, B::ClassField) -> ClassField\n\nThe compositum of a and b as a (formal) class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.compositum-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.compositum",
    "category": "method",
    "text": "compositum(a::ClassField, b::ClassField) -> ClassField\n         *(a::ClassField, b::ClassField) -> ClassField\n\nThe compositum of a and b as a (formal) class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Base.:==-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Base.:==",
    "category": "method",
    "text": "==(a::ClassField, b::ClassField)\n\nTests if a and b are equal.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Base.intersect-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Base.intersect",
    "category": "method",
    "text": "intersect(a::ClassField, b::ClassField) -> ClassField\n\nThe intersection of a and b as a class field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.prime_decomposition_type-Tuple{Hecke.ClassField,NfAbsOrdIdl}",
    "page": "Class Field Theory",
    "title": "Hecke.prime_decomposition_type",
    "category": "method",
    "text": "prime_decomposition_type(C::ClassField, p::NfAbsOrdIdl) -> (Int, Int, Int)\n\nFor a prime p in the base ring of r, determine the splitting type of p  in r. ie. the tuple (e f g) giving the ramification degree, the inertia and the number of primes above p.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.issubfield-Tuple{Hecke.ClassField,Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.issubfield",
    "category": "method",
    "text": "issubfield(a::ClassField, b::ClassField) -> Bool\n\nDetermines of a is a subfield of b.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.islocal_norm-Tuple{Hecke.ClassField,NfAbsOrdElem}",
    "page": "Class Field Theory",
    "title": "Hecke.islocal_norm",
    "category": "method",
    "text": "islocal_norm(r::ClassField, a::NfAbsOrdElem) -> Bool\n\nTests if a is a local norm at all finite places in the extension implictly given by r.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.islocal_norm-Tuple{Hecke.ClassField,NfAbsOrdElem,NfAbsOrdIdl}",
    "page": "Class Field Theory",
    "title": "Hecke.islocal_norm",
    "category": "method",
    "text": "islocal_norm(r::ClassField, a::NfAbsOrdElem, p::NfAbsOrdIdl) -> Bool\n\nTests if a is a local norm at p in the extension implictly given by r. Currently the conductor cannot have infinite places.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.normal_closure-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.normal_closure",
    "category": "method",
    "text": "normal_closure(C::ClassField) -> ClassField\n\nFor a ray class field C extending a normal base field k, compute the normal closure over Q.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.subfields-Tuple{Hecke.ClassField}",
    "page": "Class Field Theory",
    "title": "Hecke.subfields",
    "category": "method",
    "text": "subfields(C::ClassField) -> Array{ClassField, 1}\n\nFind all subfields of C as class fields.     Note: this will not find all subfields over Q, but only the ones sharing the same base field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Hecke.subfields-Tuple{Hecke.ClassField,Int64}",
    "page": "Class Field Theory",
    "title": "Hecke.subfields",
    "category": "method",
    "text": "subfields(C::ClassField, d::Int) -> Array{ClassField, 1}\n\nFind all subfields of C of degree d as class fields.     Note: this will not find all subfields over Q, but only the ones sharing the same base field.\n\n\n\n"
},

{
    "location": "class_fields/intro.html#Operations-1",
    "page": "Class Field Theory",
    "title": "Operations",
    "category": "section",
    "text": "*(a::Hecke.ClassField, b::Hecke.ClassField)\ncompositum(a::Hecke.ClassField, b::Hecke.ClassField)\n==(a::Hecke.ClassField, b::Hecke.ClassField)\nintersect(a::Hecke.ClassField, b::Hecke.ClassField)\nprime_decomposition_type(C::Hecke.ClassField, p::Hecke.NfAbsOrdIdl)\nHecke.issubfield(a::ClassField, b::ClassField)\nHecke.islocal_norm(r::Hecke.ClassField, a::Hecke.NfAbsOrdElem)\nHecke.islocal_norm(r::Hecke.ClassField, a::Hecke.NfAbsOrdElem, p::Hecke.NfAbsOrdIdl)\nHecke.normal_closure(r::Hecke.ClassField) \nsubfields(r::ClassField)\nsubfields(r::ClassField, d::Int)"
},

{
    "location": "sparse/intro.html#",
    "page": "Sparse linear algebra",
    "title": "Sparse linear algebra",
    "category": "page",
    "text": ""
},

{
    "location": "sparse/intro.html#Sparse-linear-algebra-1",
    "page": "Sparse linear algebra",
    "title": "Sparse linear algebra",
    "category": "section",
    "text": "CurrentModule = Hecke"
},

{
    "location": "sparse/intro.html#Introduction-1",
    "page": "Sparse linear algebra",
    "title": "Introduction",
    "category": "section",
    "text": "This chapter deals with sparse linear algebra over commutative rings and fields.Sparse linear algebra, that is, linear algebra with sparse matrices,  plays an important role in various algorithms in algebraic number theory. For example, it is one of the key ingredients in the computation of class groups and discrete logarithms using index calculus methods."
},

{
    "location": "sparse/intro.html#Sparse-rows-1",
    "page": "Sparse linear algebra",
    "title": "Sparse rows",
    "category": "section",
    "text": "Building blocks for sparse matrices are sparse rows, which are modelled by objects of type \\texttt{SRow}. More precisely, the type is of parametrized form objects of type SRow. More precisely, the type is of parametrized form SRow{T}, where T is the element type of the base ring R. For example, SRow{fmpz} is the type for sparse rows over the integers.It is important to note that sparse rows do not have a fixed number of columns, that is, they represent elements of  (x_i)_i in R^mathbbN mid x_i = 0 text for almost all i. In particular any two sparse rows over the same base ring can be added."
},

{
    "location": "sparse/intro.html#Hecke.sparse_row-Tuple{FlintIntegerRing,Array{Tuple{Int64,fmpz},1}}",
    "page": "Sparse linear algebra",
    "title": "Hecke.sparse_row",
    "category": "method",
    "text": "sparse_row(R::Ring, J::Vector{Tuple{Int, T}}) -> SRow{T}\n\nConstructs the sparse row (a_i)_i with a_j_i = x_i, where J = (j_i x_i)_i. The elements x_i must belong to the ring R.\n\n\n\n"
},

{
    "location": "sparse/intro.html#Hecke.sparse_row-Tuple{FlintIntegerRing,Array{Tuple{Int64,Int64},1}}",
    "page": "Sparse linear algebra",
    "title": "Hecke.sparse_row",
    "category": "method",
    "text": "sparse_row(R::Ring, J::Vector{Tuple{Int, T}}) -> SRow{T}\n\nConstructs the sparse row (a_i)_i with a_j_i = x_i, where J = (j_i x_i)_i. The elements x_i must belong to the ring R.\n\n\n\nsparse_row(R::Ring, J::Vector{Tuple{Int, Int}}) -> SRow\n\nConstructs the sparse row (a_i)_i over R with a_j_i = x_i, where J = (j_i x_i)_i.\n\n\n\n"
},

{
    "location": "sparse/intro.html#Hecke.sparse_row-Tuple{FlintIntegerRing,Array{Int64,1},Array{fmpz,1}}",
    "page": "Sparse linear algebra",
    "title": "Hecke.sparse_row",
    "category": "method",
    "text": "sparse_row(R::Ring, J::Vector{Int}, V::Vector{T}) -> SRow{T}\n\nConstructs the sparse row (a_i)_i over R with a_j_i = x_i, where J = (j_i)_i and V = (x_i)_i.\n\n\n\n"
},

{
    "location": "sparse/intro.html#Creation-1",
    "page": "Sparse linear algebra",
    "title": "Creation",
    "category": "section",
    "text": "sparse_row(::FlintIntegerRing, ::Vector{Tuple{Int, fmpz}})\nsparse_row(::FlintIntegerRing, ::Vector{Tuple{Int, Int}})\nsparse_row(::FlintIntegerRing, ::Vector{Int}, ::Vector{fmpz})"
},

{
    "location": "sparse/intro.html#Basic-operations-1",
    "page": "Sparse linear algebra",
    "title": "Basic operations",
    "category": "section",
    "text": "==(::SRow{fmpz}, ::SRow{fmpz})\n+(::SRow{fmpz}, ::SRow{fmpz})\ngetindex(::SRow{fmpz}, Int)\n*(::fmpz, ::SRow{fmpz})\ndiv(::SRow{fmpz}, ::fmpz)\ndivexact(::SRow{fmpz}, ::fmpz)\nadd_scaled_row(::SRow{fmpz}, ::SRow{fmpz}, ::fmpz)"
},

{
    "location": "sparse/intro.html#Change-of-base-ring-1",
    "page": "Sparse linear algebra",
    "title": "Change of base ring",
    "category": "section",
    "text": "change_ring(::SRow{fmpz}, ::FlintIntegerRing)"
},

{
    "location": "sparse/intro.html#Base.maximum-Tuple{SRow{fmpz}}",
    "page": "Sparse linear algebra",
    "title": "Base.maximum",
    "category": "method",
    "text": "maximum(A::SRow{fmpz}) -> fmpz\n\nFinds the largest entry of A.\n\n\n\n"
},

{
    "location": "sparse/intro.html#Base.minimum-Tuple{SRow{fmpz}}",
    "page": "Sparse linear algebra",
    "title": "Base.minimum",
    "category": "method",
    "text": "minimum(A::SRow{fmpz}) -> fmpz\n\nFinds the smallest entry of A.\n\n\n\n"
},

{
    "location": "sparse/intro.html#Nemo.lift-Tuple{SRow{Nemo.nmod}}",
    "page": "Sparse linear algebra",
    "title": "Nemo.lift",
    "category": "method",
    "text": "lift(A::SRow{nmod}) -> SRow{fmpz}\n\nReturn the sparse row obtained by lifting all entries in A.\n\n\n\n"
},

{
    "location": "sparse/intro.html#Hecke.mod!-Tuple{SRow{fmpz},fmpz}",
    "page": "Sparse linear algebra",
    "title": "Hecke.mod!",
    "category": "method",
    "text": "mod!(A::SRow{fmpz}, n::fmpz) -> SRow{fmpz}\n\nInplace reduction of all entries of A modulo n to the positive residue system.\n\n\n\n"
},

{
    "location": "sparse/intro.html#Hecke.mod_sym!-Tuple{SRow{fmpz},fmpz}",
    "page": "Sparse linear algebra",
    "title": "Hecke.mod_sym!",
    "category": "method",
    "text": "mod_sym!(A::SRow{fmpz}, n::fmpz) -> SRow{fmpz}\n\nInplace reduction of all entries of A modulo n to the symmetric residue system.\n\n\n\n"
},

{
    "location": "sparse/intro.html#Functionality-for-integral-sparse-rows-1",
    "page": "Sparse linear algebra",
    "title": "Functionality for integral sparse rows",
    "category": "section",
    "text": "maximum(::SRow{fmpz})\nminimum(::SRow{fmpz})\nlift(::SRow{nmod})\nmod!(::SRow{fmpz}, ::fmpz)\nmod_sym!(::SRow{fmpz}, ::fmpz)"
},

{
    "location": "sparse/intro.html#Sparse-matrices-1",
    "page": "Sparse linear algebra",
    "title": "Sparse matrices",
    "category": "section",
    "text": "Let R be a commutative ring. Sparse matrices with base ring R are modlled by objects of type SMat. More precisely, the type is of parametrized form SRow{T}, where T is the element type of the base ring. For example, SMat{fmpz} is the type for sparse matrices over the integers.In constrast to sparse rows, sparse matrices have a fixed number of rows and columns, that is, they represent elements of the matrices space mathrmMat_ntimes m(R). Internally, sparse matrices are implemented as an array of sparse rows.  As a consequence, Unlike their dense counterparts, sparse matrices have a mutable number of rows and it is very performant to add additional rows."
},

{
    "location": "FacElem.html#",
    "page": "Factored Elements",
    "title": "Factored Elements",
    "category": "page",
    "text": ""
},

{
    "location": "FacElem.html#Factored-Elements-1",
    "page": "Factored Elements",
    "title": "Factored Elements",
    "category": "section",
    "text": "CurrentModule = HeckeIn many applications in number theory related to the multiplicative structure of number fields, interesting elements, e.g. units, are extremely large when written wrt. to a fxied basis for the field: for the fundamental unit in Qsqrt d it is known that the coefficients wrt. the canonical basis 1 sqrt d can have O(exp sqrt d) many digits. All currently known, fast methods construct those elements as power products of smaller elements, allowing the computer to handle them.Mathematically, one can think of factored elements to formally live in the ring ZK the group ring of the non-zero field elements. Thus elements are of the form $ \\prod ai^{ei}$ where a_i are elements in K, typically small and the e_iin Z are frequently  large exponents. We refer to the a_i as the base and the e_i as the  exponents of the factored element.Since K is, in general, no PID, this presentation is non-unique, elements in this form can easily be multiplied, raised to large powers, but in general not compared and not added.In Hecke, this is caputured more generally by the type FacElem,  parametrized by the type of the elements in the base and the type of their  parent.Important special cases areFacElem{fmpz, FlintIntegerRing}, factored integers\nFacElem{nf_elem, AnticNumberField}, factored algerbaic numbers\nFacElem{NfAbsOrdIdl, NfAbsOrdIdlSet}, factored idealsIt should be noted that an object of type `FacElemfmpz FlintIntegerRing  will, in general, not represent an integer as the exponents can be negative."
},

{
    "location": "FacElem.html#Hecke.FacElem",
    "page": "Factored Elements",
    "title": "Hecke.FacElem",
    "category": "type",
    "text": "FacElem{B}(base::Array{B, 1}, exp::Array{fmpz, 1}) -> FacElem{B}\n\nReturns the element prod b_i^e_i, un-expanded.\n\n\n\nFacElem{B}(d::Dict{B, fmpz}) -> FacElem{B}\nFacElem{B}(d::Dict{B, Integer}) -> FacElem{B}\n\nReturns the element prod b^dp, un-expanded.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.FacElem-Tuple{nf_elem}",
    "page": "Factored Elements",
    "title": "Hecke.FacElem",
    "category": "method",
    "text": "FacElem{B}(base::Array{B, 1}, exp::Array{fmpz, 1}) -> FacElem{B}\n\nReturns the element prod b_i^e_i, un-expanded.\n\n\n\nFacElem{B}(d::Dict{B, fmpz}) -> FacElem{B}\nFacElem{B}(d::Dict{B, Integer}) -> FacElem{B}\n\nReturns the element prod b^dp, un-expanded.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.ideal-Tuple{NfAbsOrd{AnticNumberField,nf_elem},FacElem{nf_elem,AnticNumberField}}",
    "page": "Factored Elements",
    "title": "Hecke.ideal",
    "category": "method",
    "text": " ideal(O::NfOrd, a::FacElem{nf_elem, AnticNumberField)\n\nThe factored fractional ideal a*O.\n\n\n\n"
},

{
    "location": "FacElem.html#Construction-1",
    "page": "Factored Elements",
    "title": "Construction",
    "category": "section",
    "text": "In general one can define factored elements by giving 2 arrays, the  base and the exponent, or a dictionary containing the pairs:FacElem\nFacElem(a::nf_elem)ideal(::NfOrd, ::FacElem{nf_elem, AnticNumberField})"
},

{
    "location": "FacElem.html#AbstractAlgebra.Generic.evaluate-Union{Tuple{FacElem{fmpz,S}}, Tuple{S}} where S",
    "page": "Factored Elements",
    "title": "AbstractAlgebra.Generic.evaluate",
    "category": "method",
    "text": "\n\nevaluate{T}(x::FacElem{T}) -> T\n\nExpands or evaluates the factored element, i.e. actually computes the value.  Does \"square-and-multiply\" on the exponent vectors.\n\n\n\n"
},

{
    "location": "FacElem.html#AbstractAlgebra.Generic.evaluate-Tuple{FacElem{fmpq,S} where S}",
    "page": "Factored Elements",
    "title": "AbstractAlgebra.Generic.evaluate",
    "category": "method",
    "text": "\n\nevaluate(x::FacElem{fmpq}) -> fmpq\nevaluate(x::FacElem{fmpz}) -> fmpz\n\nExpands or evaluates the factored element, i.e. actually computes the the element.  Works by first obtaining a simplified version of the power product into coprime base elements.\n\n\n\n"
},

{
    "location": "FacElem.html#AbstractAlgebra.Generic.evaluate-Union{Tuple{FacElem{T,S} where S}, Tuple{T}} where T",
    "page": "Factored Elements",
    "title": "AbstractAlgebra.Generic.evaluate",
    "category": "method",
    "text": "\n\nevaluate{T}(x::FacElem{T}) -> T\n\nExpands or evaluates the factored element, i.e. actually computes the value.  Does \"square-and-multiply\" on the exponent vectors.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.evaluate_naive-Union{Tuple{FacElem{T,S} where S}, Tuple{T}} where T",
    "page": "Factored Elements",
    "title": "Hecke.evaluate_naive",
    "category": "method",
    "text": "\n\nevaluate_naive{T}(x::FacElem{T}) -> T\n\nExpands or evaluates the factored element, i.e. actually computes the value. Uses the obvious naive algorithm. Faster for input in finite rings.\n\n\n\n"
},

{
    "location": "FacElem.html#Conversion-1",
    "page": "Factored Elements",
    "title": "Conversion",
    "category": "section",
    "text": "The process of computing the value defined by a factored element is available as evaluate. Depending on the types involved this can be very efficient.evaluate(::FacElem{fmpz, S}) where S\nevaluate(::FacElem{fmpq, S} where S)\nevaluate(::FacElem{T,S} where S) where T\nevaluate_naive(::FacElem{T,S} where S) where T"
},

{
    "location": "FacElem.html#Hecke.simplify-Tuple{FacElem{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}}}",
    "page": "Factored Elements",
    "title": "Hecke.simplify",
    "category": "method",
    "text": "simplify(x::FacElem{NfOrdIdl, NfOrdIdlSet}) -> FacElem\nsimplify(x::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> FacElem\n\nUses coprime_base to obtain a simplified version of x, ie. in the simplified version all base ideals will be pariwise coprime but not neccessarily prime!.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.simplify-Tuple{FacElem{fmpq,S} where S}",
    "page": "Factored Elements",
    "title": "Hecke.simplify",
    "category": "method",
    "text": "simplify(x::FacElem{fmpq}) -> FacElem{fmpq}\nsimplify(x::FacElem{fmpz}) -> FacElem{fmpz}\n\nSimplfies the factored element, i.e. arranges for the base to be coprime.\n\n\n\n"
},

{
    "location": "FacElem.html#Base.isone-Tuple{FacElem{fmpq,S} where S}",
    "page": "Factored Elements",
    "title": "Base.isone",
    "category": "method",
    "text": "isone(x::FacElem{fmpq}) -> Bool\nisone(x::FacElem{fmpz}) -> Bool\n\nTests if x represents 1 without an evaluation.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.factor_coprime-Tuple{FacElem{fmpz,S} where S}",
    "page": "Factored Elements",
    "title": "Hecke.factor_coprime",
    "category": "method",
    "text": "factor_coprime(x::FacElem{fmpz}) -> Fac{fmpz}\n\nComputed a partial factorisation of x, ie. writes x as a product of pariwise coprime integers.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.factor_coprime-Tuple{FacElem{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}}}",
    "page": "Factored Elements",
    "title": "Hecke.factor_coprime",
    "category": "method",
    "text": "factor_coprime(x::FacElem{NfOrdIdl, NfOrdIdlSet}) -> Dict{NfOrdIdl, Int}\n\nComputed a partial factorisation of x, ie. writes x as a product of pariwise coprime integral ideals.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.factor_coprime-Tuple{FacElem{Hecke.NfOrdFracIdl,Hecke.NfOrdFracIdlSet}}",
    "page": "Factored Elements",
    "title": "Hecke.factor_coprime",
    "category": "method",
    "text": " factor_coprime(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> Dict{NfOrdIdl, Int}\n\nA coprime factorisation of Q: each ideal in Q is split using \\code{integral_split} and then a coprime basis is computed. This does {\\bf not} use any factorisation.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.factor_coprime-Tuple{FacElem{nf_elem,AnticNumberField},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}}",
    "page": "Factored Elements",
    "title": "Hecke.factor_coprime",
    "category": "method",
    "text": "factorcoprime(a::FacElem{nfelem, AnticNumberField}, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}\n\nFactors the rincipal ideal generated by a into coprimes by computing a coprime basis from the principal ideals in the factorisation of a.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.factor-Tuple{FacElem{Hecke.NfOrdFracIdl,Hecke.NfOrdFracIdlSet}}",
    "page": "Factored Elements",
    "title": "Hecke.factor",
    "category": "method",
    "text": " factor(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> Dict{NfOrdIdl, Int}\n\nThe factorisation of Q, by refining a coprime factorisation.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.factor-Tuple{FacElem{nf_elem,AnticNumberField},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}}",
    "page": "Factored Elements",
    "title": "Hecke.factor",
    "category": "method",
    "text": "factor(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}\n\nFactors the principal ideal generated by a by refinind a coprime factorisation.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.compact_presentation",
    "page": "Factored Elements",
    "title": "Hecke.compact_presentation",
    "category": "function",
    "text": "compact_presentation(a::FacElem{nf_elem, AnticNumberField}, n::Int = 2; decom, arb_prec = 100, short_prec = 1000) -> FacElem\n\nComputes a presentation a = prod a_i^n_i where all the exponents n_i are powers of n and, the elements a are \"small\", generically, they have a norm bounded by d^n2 where d is the discriminant of the maximal order. As the algorithm needs the factorisation of the principal ideal generated by a, it can be passed in in \\code{decom}.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.signs-Tuple{Union{FacElem{nf_elem,AnticNumberField}, nf_elem}}",
    "page": "Factored Elements",
    "title": "Hecke.signs",
    "category": "method",
    "text": "\n\nsigns(a::nf_elem)          -> Dict{InfPlc, Int}\nsigns(a::FacElem{nf_elem}) -> Dict{InfPlc, Int}\n\nThis function returns a dictionary of the signs of a at all infinite places of the ambient number field. The keys are infinite places of the ambient number field. The value is 1 if the sign is positive and -1 if the sign is negative.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.signs-Tuple{Union{FacElem{nf_elem,AnticNumberField}, nf_elem},Array{InfPlc,1}}",
    "page": "Factored Elements",
    "title": "Hecke.signs",
    "category": "method",
    "text": "\n\nsigns(a::nf_elem, l::Vector{InfPlc})          -> Dict{InfPlc, Int}\nsigns(a::FacElem{nf_elem}, l::Vector{InfPlc}) -> Dict{InfPlc, Int}\n\nThis function returns a dictionary of the signs of a at places in l. The keys are the elements of l. The value is 1 if the sign is positive and -1 if the sign is negative. The result will contain as many signs as there are real places contained in l.\n\n\n\n"
},

{
    "location": "FacElem.html#Base.sign-Tuple{Union{FacElem{nf_elem,AnticNumberField}, nf_elem},InfPlc}",
    "page": "Factored Elements",
    "title": "Base.sign",
    "category": "method",
    "text": "\n\nsign(a::nf_elem, P::InfPlc)          -> Int\nsign(a::FacElem{nf_elem}, P::InfPlc) -> Int\n\nThis function returns the sign of a at the place P. The value is 1 if the sign is positive and -1 if the sign is negative.\n\n\n\n"
},

{
    "location": "FacElem.html#Nemo.ispositive-Tuple{Union{FacElem{nf_elem,AnticNumberField}, nf_elem},InfPlc}",
    "page": "Factored Elements",
    "title": "Nemo.ispositive",
    "category": "method",
    "text": "\n\nispositive(a::nf_elem, P::InfPlc)          -> Bool\nispositive(a::FacElem{nf_elem}, P::InfPlc) -> Bool\n\nReturns whether the element a is positive at the embedding corresponding to P. The place P must be real.\n\n\n\n"
},

{
    "location": "FacElem.html#Nemo.ispositive-Tuple{Union{FacElem{nf_elem,AnticNumberField}, nf_elem},Array{InfPlc,1}}",
    "page": "Factored Elements",
    "title": "Nemo.ispositive",
    "category": "method",
    "text": "\n\nispositive(a::nf_elem, l::Vector{InfPlc})          -> Bool\nispositive(a::FacElem{nf_elem}, l::Vector{InfPlc}) -> Bool\n\nReturns whether the element a is positive at the embeddings corresponding to the real places of l.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.istotally_positive-Tuple{Union{FacElem{nf_elem,AnticNumberField}, nf_elem}}",
    "page": "Factored Elements",
    "title": "Hecke.istotally_positive",
    "category": "method",
    "text": "\n\nistotally_positive(a::nf_elem)          -> Bool\nistotally_positive(a::FacElem{nf_elem}) -> Bool\n\nReturns whether the element a is totally positive, that is, whether it is positive at all places of the ambient number field.\n\n\n\n"
},

{
    "location": "FacElem.html#AbstractAlgebra.Generic.valuation-Tuple{FacElem{nf_elem,AnticNumberField},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Factored Elements",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "valuation(a::FacElem{nf_elem, AnticNumberField}, P::NfOrdIdl) -> fmpz\n\nThe valuation of a at P.\n\n\n\n"
},

{
    "location": "FacElem.html#AbstractAlgebra.Generic.valuation-Tuple{FacElem{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}},NfAbsOrdIdl{AnticNumberField,nf_elem}}",
    "page": "Factored Elements",
    "title": "AbstractAlgebra.Generic.valuation",
    "category": "method",
    "text": "valuation(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}, p::NfOrdIdl)\nvaluation(A::FacElem{NfOrdIdl, NfOrdIdlSet}, p::NfOrdIdl)\n\nThe valuation of A at P.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.evaluate_mod-Tuple{FacElem{nf_elem,AnticNumberField},Hecke.NfOrdFracIdl}",
    "page": "Factored Elements",
    "title": "Hecke.evaluate_mod",
    "category": "method",
    "text": "evaluate_mod(a::FacElem{nf_elem, AnticNumberField}, B::NfOrdFracIdl) -> nf_elem\n\nEvaluates a using CRT and small primes. Assumes that the ideal generated by a is in fact B. Useful in cases where a has huge exponents, but the evaluated element is actually \"small\".\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.pure_extension-Tuple{Int64,FacElem{nf_elem,AnticNumberField}}",
    "page": "Factored Elements",
    "title": "Hecke.pure_extension",
    "category": "method",
    "text": "pure_extension(n::Int, gen::FacElem{nf_elem, AnticNumberField}) -> NfRel{nf_elem}, NfRelElem\npure_extension(n::Int, gen::nf_elem) -> NfRel{nf_elem}, NfRelElem\n\nCreate the field extension with the defining polynomial x^n-gen.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.reduce_ideal2-Tuple{FacElem{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}}}",
    "page": "Factored Elements",
    "title": "Hecke.reduce_ideal2",
    "category": "method",
    "text": "\n\nreduce_ideal2(A::FacElem{NfOrdIdl}) -> NfOrdIdl, FacElem{nf_elem}\n\nComputes B and alpha in factored form, such that alpha B = A.\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.modular_proj-Tuple{FacElem{nf_elem,AnticNumberField},Hecke.modular_env}",
    "page": "Factored Elements",
    "title": "Hecke.modular_proj",
    "category": "method",
    "text": "\n\nmodularproj(a::FacElem{nfelem, AnticNumberField}, me::modularenv) -> Array{fqnmod, 1}\n\nGiven an algebraic number a in factored form and data \\code{me} as computed by \\code{modular_init}, project a onto the residue class fields.\n\n\n\n"
},

{
    "location": "FacElem.html#Special-functions-1",
    "page": "Factored Elements",
    "title": "Special functions",
    "category": "section",
    "text": "In the case where the parent of the base allows for efficient gcd computation, power products can be made unique:simplify(x::FacElem{NfOrdIdl, NfOrdIdlSet})\nsimplify(x::FacElem{fmpq,S} where S)The simplified version can then be used further:isone(x::FacElem{fmpq, S} where S)\nfactor_coprime(::FacElem{fmpz, S} where S)\nfactor_coprime(::FacElem{NfOrdIdl, NfOrdIdlSet})\nfactor_coprime(::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})\nfactor_coprime(::FacElem{nf_elem, AnticNumberField}, ::NfOrdIdlSet)\nfactor(::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})\nfactor(::FacElem{nf_elem, AnticNumberField}, ::NfOrdIdlSet)For factorised algebraic numbers a unique simplification is not possible, however, this allows still do obtain partial results:compact_presentation(a::FacElem{nf_elem, AnticNumberField}, n::Int = 2)signs(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem})\nsigns(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem}, ::Array{InfPlc,1})\nsign(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem}, ::InfPlc)\nispositive(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem}, ::InfPlc)\nispositive(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem}, ::Array{InfPlc,1})\nistotally_positive(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem})valuation(::FacElem{nf_elem,AnticNumberField}, ::NfAbsOrdIdl{AnticNumberField,nf_elem})\nvaluation(::FacElem{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}}, ::NfAbsOrdIdl{AnticNumberField,nf_elem})\nevaluate_mod(::FacElem{nf_elem,AnticNumberField}, ::NfOrdFracIdl)\npure_extension(::Int64, ::FacElem{nf_elem,AnticNumberField})\nreduce_ideal2(::FacElem{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}})\nmodular_proj(::FacElem{nf_elem,AnticNumberField}, ::Hecke.modular_env)"
},

{
    "location": "FacElem.html#Hecke.max_exp-Tuple{FacElem}",
    "page": "Factored Elements",
    "title": "Hecke.max_exp",
    "category": "method",
    "text": "max_exp(a::FacElem)\n\nFinds the largest exponent in the factored element a\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.min_exp-Tuple{FacElem}",
    "page": "Factored Elements",
    "title": "Hecke.min_exp",
    "category": "method",
    "text": "min_exp(a::FacElem)\n\nFinds the smallest exponent in the factored element a\n\n\n\n"
},

{
    "location": "FacElem.html#Hecke.maxabs_exp-Tuple{FacElem}",
    "page": "Factored Elements",
    "title": "Hecke.maxabs_exp",
    "category": "method",
    "text": "maxabs_exp(a::FacElem)\n\nFinds the largest exponent by absolute value the factored element a\n\n\n\n"
},

{
    "location": "FacElem.html#Miscellaneous-1",
    "page": "Factored Elements",
    "title": "Miscellaneous",
    "category": "section",
    "text": "max_exp(a::FacElem)\nmin_exp(a::FacElem)\nmaxabs_exp(a::FacElem)"
},

]}
