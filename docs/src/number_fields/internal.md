```@meta
CurrentModule = Hecke
```
Number fields, in Hecke, come in several
different types:
 - `AnticNumberField`: a finite simple extension of the rational numbers $Q$
 - `NfAbsNS`: a finite extension of $Q$ given by several polynomials.
 We will refer to this as a non-simple field - even though mathematically
 we can find a primitive elements.
 - `NfRel`: a finite simple extension of a number field. This is 
    actually parametried by the (element) type of the coefficient field.
    The complete type of an extension of an absolute field (`AnticNumberField`)
    is `NfRel{nf_elem}`. The next extension thus will be
    `NfRel{NfRelElem{nf_elem}}`.
 - `NfRel_ns`: extensions of number fields given by several polynomials.
    This too will be refered to as a non-simple field.

The simple types `AnticNumberField` and `NfRel` are also calle simple
fields in the rest of this document, `NfRel` and `NfRel_ns` are referred
to as relative extensions while `AnticNumberField` and `NfAbsNS` are
called absolute.

Internally, simple fields are essentially just (univariate) polynomial
quotients in a dense representation, while non-simple fields are
multivariate quotient rings, thus have a sparse presentation.
In general, simple fields allow much faster arithmetic, while 
the non-simple fields give easy access to large degree fields.

## Absolute Simple Fields

The most basic number field type is that of `AnticNumberField`. Internally
this is essentially represented as a unvariate quotient with the
arithmetic provided by the antic-c-library and implemented in Nemo.

