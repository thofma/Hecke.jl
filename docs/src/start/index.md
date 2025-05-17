```@meta
CurrentModule = Hecke
DocTestSetup = Hecke.doctestsetup()
```
# Getting started

To use Hecke, a julia version of 1.0 is necessary (the latest stable julia version will do).
Please see <https://julialang.org/downloads/> for instructions on how to obtain julia for your system.
Once a suitable julia version is installed, use the following steps at the julia prompt to install Hecke:

```julia
julia> using Pkg

julia> Pkg.add("Hecke")
```

Here is a quick example of using Hecke to define a number field and compute its class group::

```jldoctest
julia> using Hecke

julia> Qx, x = QQ[:x];

julia> f = x^2 - 2*3*5*7;

julia> K, a = number_field(f, :a);

julia> OK = maximal_order(K);

julia> C, mC = class_group(OK);

julia> C
(Z/2)^2
```
