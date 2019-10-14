
using Hecke
using Crayons

######################################################################
#
# Display modification.
#
######################################################################


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
            print(io, Crayon(foreground=:cyan,bold=true), string(S), Crayon(reset=true))
            if len - i != 1
               print(io, "^")
               print(io, len - i)
            end
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


######################################################################
#
# Tests!
#
######################################################################

Qp = PadicField(7,10)
R, x = PolynomialRing(Qp,"x")

K,θ = Hecke.EisensteinField(x^6-7, "θ")

f = x^5 - 7*x + 4
fK = change_base_ring(K,f)


Ql = QadicField(17,3,10)
S, y = PolynomialRing(Ql, "y")
L,a = Hecke.EisensteinField(y^3-17*y^2+17*y-17, "a")

g = change_base_ring(L, L.pol)
Y = change_base_ring(L, y)

@assert fK - 4 == change_base_ring(K, x^5 - 7*x)
@assert 2*θ == θ + θ

####
# Root finding

rts1 = roots(fK)
correct = fmpz(5) + 138118274 + O(Qp,7^10)
# + O(7^10)

@assert length(rts1) == 1 && K(correct) == rts1[1]

rts2 = roots(x^6 - 7, K)

correct = [
(2 + 4*7^1 + 6*7^2 + 3*7^3 + 2*7^5 + 6*7^6 + 2*7^7 + 4*7^8 + O(Qp,7^9))*θ
(3 + 4*7^1 + 6*7^2 + 3*7^3 + 2*7^5 + 6*7^6 + 2*7^7 + 4*7^8 + O(Qp,7^9))*θ        
(5 + 2*7^1 + 3*7^3 + 6*7^4 + 4*7^5 + 4*7^7 + 2*7^8 + O(Qp,7^9))*θ                
θ                                                                             
(4 + 2*7^1 + 3*7^3 + 6*7^4 + 4*7^5 + 4*7^7 + 2*7^8 + O(Qp,7^9))*θ                
(6 + 6*7^1 + 6*7^2 + 6*7^3 + 6*7^4 + 6*7^5 + 6*7^6 + 6*7^7 + 6*7^8 + O(Qp,7^9))*θ
]

@assert rts2 == correct

nothing


