# Introduction

In Hecke, maximal orders (aka ring of integers), due to their special properties normal orders don't share, come with their own type `NfMaximalOrder`. 
While the elements have type `NfOrderElem`, the ideals and fractional ideals have types `NfMaximalOrderIdeal` and `NfMaximalOrderFracIdeal` respectively.

While theoretically a number field contains a unique maximal order (the set of all integral elements), for technical reasons in Hecke a number field admits multiple maximal orders, which are uniquely determined by the number field and a chosen integral basis.

Let $K$ be a number field of degree $d$ with primitive element $\alpha$ and $\mathcal O$ a maximal order $K$ with $\mathbf{Z}$-basis $(\omega_1,\dotsc,\omega_d)$.
The *basis matrix* of $\mathcal O$ is the unique matrix $M_{\mathcal O} \in \operatorname{Mat}_{d \times d}(\mathbf{Q})$ such that
\begin{align} \begin{pmatrix} \omega_1 \\\\ \omega_2 \\\\ \vdots \\\\ \omega_d \end{pmatrix} = M_{\mathcal O} \begin{pmatrix} 1 \\\\ \alpha \\\\ \vdots \\\\ \alpha^{d - 1} \end{pmatrix} \end{align}.
If $\beta$ is an element of $\mathcal O$, we call the unique integers $(x_1,\dotsc,x_d) \in \mathbf Z^d$ with
\begin{align} \beta = \sum_{i=1}^d x_i \omega_i \end{align}
the *coefficients* of $\beta$ with respect to $\mathcal O$ or just the *coefficient vector*.

For an ideal $I$ of $\mathcal O$, a *basis matrix* of $I$ is a matrix $M \in \operatorname{Mat}_{d \times d}(\mathbf{Z})$, such that the elements $(\alpha_1,\dotsc,\alpha_d)$ definied by
\begin{align} \begin{pmatrix} \alpha_1 \\\\ \alpha_2 \\\\ \vdots \\\\ \alpha_d \end{pmatrix} = M_{\mathcal O} \begin{pmatrix} \omega_1 \\\\ \omega_2 \\\\ \vdots \\\\ \omega_d \end{pmatrix} \end{align}
form a $\mathbf{Z}$-basis of $I$.

@module{Hecke}

## Creation

@{MaximalOrder(::AnticNumberField)}
@{MaximalOrder(::AnticNumberField, ::Array{fmpz, 1})}

## Basic invariants

@{nf(::NfMaximalOrder)}
@{degree(::NfMaximalOrder)}
@{basis(::NfMaximalOrder)}
@{basis(::NfMaximalOrder, ::AnticNumberField)}
@{basis_mat(::NfMaximalOrder)}
@{basis_mat_inv(::NfMaximalOrder)}
@{index(::NfMaximalOrder)}
@{signature(::NfMaximalOrder)}
@{is_index_divisor(::NfMaximalOrder, ::fmpz)}

## Elements
@{call(::NfMaximalOrder, ::nf_elem, ::Bool)}

## Ideals

@{nf(::NfMaximalOrderIdeal)}
