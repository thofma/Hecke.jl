# alternative names for some functions from Base
@alias trace tr

# alternative names for some functions from LinearAlgebra
# we don't use the `@alias` macro here because we provide custom
# docstrings for these aliases
#= none =#


# predeclare some functions to allow defining aliases for some of our own functions
function number_of_lattices end
function number_of_relations end
@alias nlattices number_of_lattices
@alias nrels number_of_relations
