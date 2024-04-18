# alternative names for some functions from Base
#= none =#

# TODO: next breaking release: remove the if guard around the block
if @__MODULE__() == Hecke

  # alternative names for some functions from LinearAlgebra
  # we don't use the `@alias` macro here because we provide custom
  # docstrings for these aliases
  #= none =#
end

# predeclare some functions to allow defining aliases for some of our own functions
function number_of_lattices end
function number_of_relations end
@alias nlattices number_of_lattices
@alias nrels number_of_relations

# TODO: next breaking release: remove this block
# Oscar includes this file for historical reasons, but expects it to contain the Base.@deprecate_binding calls.
# Until this is changed and released there, we thus need to include the deprecations here.
@static if Symbol(@__MODULE__()) in [:Oscar]
  Hecke.@include_deprecated_bindings()
end
