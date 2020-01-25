######################################################################
#
# File for quick testing of the LocalFields interface.
# Note that the "Crayons" dependency is not actually required
# for any code to run.
#
######################################################################

using Test
using Hecke
#using Crayons

######################################################################
#
# Display modification.
#
######################################################################

#=
### Yarrrr! I be a type pirate! ####
import Base.show
function show(io::IO, x::Hecke.AbstractAlgebra.Generic.PolynomialElem)
   len = length(x)
   S = var(parent(x))
   if len == 0
      print(IOContext(io, :compact => true), base_ring(x)(0))
   else
      for i = 1:len - 1
         c = coeff(x, len - i)
         bracket = needs_parentheses(c)
         if !iszero(c)
            if i != 1 && !displayed_with_minus_in_front(c)
               print(io, "+")
            end
            if !isone(c) && (c != -1 || show_minus_one(typeof(c)))
               if bracket
                  print(io, "(")
               end
               print(IOContext(io, :compact => true), c)
               if bracket
                  print(io, ")")
               end
               print(io, "*")
            end
            if c == -1 && !show_minus_one(typeof(c))
               print(io, "-")
            end
            # Probably better to define a "print variable" function to hook into here.
            print(io, Crayon(foreground=:cyan,bold=true), string(S))
            if len - i != 1
               print(io, "^")
               print(io, len - i)
            end
            print(io,  Crayon(reset=true))
         end
      end
      c = coeff(x, 0)
      bracket = needs_parentheses(c)
      if !iszero(c)
         if len != 1 && !displayed_with_minus_in_front(c)
            print(io, "+")
         end
         if bracket
            print(io, "(")
         end
         print(IOContext(io, :compact => true), c)
         if bracket
            print(io, ")")
         end
      end
   end
end
=#

######################################################################
#
# Tests!
#
######################################################################

include("../../test/LocalField/Eisenstein.jl")



nothing


