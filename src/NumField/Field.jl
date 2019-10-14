################################################################################
#
#  Base field
#
################################################################################

@doc Markdown.doc"""
    base_field(L::NumField) -> NumField

Given a number field $L/K$ this function returns the base field $K$.
For absolute extensions this returns $\mathbf{Q}$.
"""
base_field(::NumField)

_base_ring(K::NumField) = base_field(K)

_base_ring(::FlintRationalField) = FlintQQ

################################################################################
#
#  Predicates
#
################################################################################

export isabsolute

@doc Markdown.doc"""
    isabsolute(L::NumField) -> Bool

Returns whether $L$ is an absolute extension, that is, whether the base field
of $L$ is $\mathbf{Q}$.
"""
isabsolute(::NumField)

isabsolute(::NumField) = false

isabsolute(::NumField{fmpq}) = true

@doc Markdown.doc"""
    elem_type(L::NumField) -> Type

Returns the type of the elements of $L$.
"""
elem_type(::NumField)

################################################################################
#
#  Degree
#
################################################################################

@doc Markdown.doc"""
    degree(L::NumField) -> Int 

Given a number field $L/K$, this function returns the degree of $L$ over $K$.
"""
degree(A::NumField)

dim(K::NumField) = degree(K)

################################################################################
#
#  Absolute degree
#
################################################################################

@doc Markdown.doc"""
    absolute_degree(L::NumField) -> Int 

Given a number field $L/K$, this function returns the degree of $L$ over
$\mathbf Q$.
"""
function absolute_degree(A::NumField)
  return absolute_degree(base_field(A)) * degree(A)
end

################################################################################
#
#  Is simple extension
#
################################################################################

@doc Markdown.doc"""
    issimple(L::NumField) -> Bool

Given a number field $L/K$ this function returns whether $L$ is simple, that is,
whether $L/K$ is defined by a univariate polynomial$.
"""
issimple(a::NumField)

################################################################################
#
#  Number field creation
#
################################################################################

@doc Markdown.doc"""
    NumberField(f::Poly{NumFieldElem}, s::String;
                cached::Bool = false, check::Bool = false) -> NumField, NumFieldElem

Given an irreducible polynomial $f \in K[x]$ over some number field $K$, this
function creates the simple number field $L = K[x]/(x)$ and returns $(L, b)$,
where $b$ is the class of $x$ in $L$. The string `s` is used only for printing
the primitive element $b$.

Testing that $f$ is irreducible can be disabled by setting the keyword argument
`check` to `false`.
"""
NumberField(f::PolyElem{<:NumFieldElem}, s::String;
            cached::Bool = false, check::Bool = false) 

################################################################################
#
#  Is commutative
#
################################################################################

iscommutative(K::NumField) = true

################################################################################
#
#  Absolute field
#
################################################################################

@doc Markdown.doc"""
    absolute_field(L::NumField) -> NumField, Map

Given a number field $L$, this function returns an absolute simple number field
$M/\mathbf{Q}$ together with a $\mathbf{Q}$-linear isomorphism $M \to K$.
"""
absolute_field(::NumField)

################################################################################
# 
#  Normal basis
#
################################################################################

@doc Markdown.doc"""
    normal_basis(L::NumField) -> NumFieldElem

Given a normal number field $L/K$, this function returns an element $a$ of $L$,
such that the orbit of $a$ under the Galois group of $L/K$ is an $K$-basis
of $L$.
"""
function normal_basis(L::NumField)
  n = degree(L)
  K = base_field(L)
  Aut = automorphisms(L)

  length(Aut) != degree(L) && error("The field is not normal over the rationals!")

  A = zero_matrix(K, n, n)
  r = one(L)
  while true
    r = rand(basis(L), -n:n)
    for i = 1:n
      y = Aut[i](r)
      for j = 1:n
        A[i,j] = coeff(y, j - 1)
      end
    end
    if rank(A) == n
      break
    end
  end
  return r
end
