using Hecke

if VERSION < v"0.5.0-dev+7720"
  """
  Allows the `@testset` syntax from Julia 0.5 in Julia 0.4,
  but without the additional features.
  """
  macro testset(args...)
    isempty(args) && error("No arguments to @testset")
    return esc(args[end])
  end
end

using Base.Test

include("NfMaxOrd-test.jl")
include("NfMaxOrd.jl")
include("NfOrd.jl")
include("EllCrv.jl")
include("Misc/AbelianGrp.jl")

test_pseudohnf()

set_verbose_level(:UnitGroup, 0)
set_verbose_level(:ClassGroup, 0)

test_NfOrd()
test_NfOrd_Elem()
test_NfOrd_Idl()
test_NfOrd_FracIdl()
test_EllCrv()
test_EllCrv_QQ()
test_EllCrv_Finite()

Qx, x = PolynomialRing(QQ, "x")

K, a = NumberField(x^2 - 2)
print("Testing $(x^2 - 2)\n")
O = maximal_order(K)
#
# x^5 + 514944*x^2 + 123904 test prime decomposition with this (2 is index divisor and only one prime ideal over 2)
#
print("Tentative class and unit group computation ... \n")
c, U, b = Hecke._class_unit_group(O);
print("Saturating the tentative unit group ... \n")
Hecke._refine_with_saturation(c, U)

K, a = NumberField(x^3 - 2)
print("Testing $(x^3 - 2)\n")
O = maximal_order(K)
#
# x^5 + 514944*x^2 + 123904 test prime decomposition with this (2 is index divisor and only one prime ideal over 2)
#
print("Tentative class and unit group computation ... \n")
c, U, b = Hecke._class_unit_group(O);
print("Saturating the tentative unit group ... \n")
Hecke._refine_with_saturation(c, U)

K, a = NumberField(x^5 - 11^2 * 7)
print("Testing $(x^5 - 11^2 * 7)\n")
O = maximal_order(K)
#
# x^5 + 514944*x^2 + 123904 test prime decomposition with this (2 is index divisor and only one prime ideal over 2)
@test discriminant(O) == 109853253125
#
print("Tentative class and unit group computation ... \n")
c, U, b = Hecke._class_unit_group(O);
print("Saturating the tentative unit group ... \n")
Hecke._refine_with_saturation(c, U)
@test c.h == 5 
#
f = x^18 + 18*x^16 + 135*x^14 + 192*x^12 - 2961*x^10 - 17334*x^8+ 20361*x^6 +  315108*x^4 + 514944*x^2 + 123904
#
print("Testing $f\n")
println(signature(f))
K, a = NumberField(f)
O = maximal_order(K)
#
print("Tentative class and unit group computation ... \n")
c, U, b = Hecke._class_unit_group(O);
print("Saturating the tentative unit group ... \n")
Hecke._refine_with_saturation(c, U)
#
@test c.h == 36
#@test Hecke._validate_class_unit_group(c, U) == 1
##
#f = x^5 + 514944*x^2 + 123904 
##
#print("Testing $f\n")
#println(signature(f))
#K, a = NumberField(f)
#O = maximal_order(K)
##
#print("Tentative class and unit group computation ... \n")
#c, U, b = Hecke._class_unit_group(O);
#print("Saturating the tentative unit group ... \n")
#Hecke._refine_with_saturation(c, U)
#
#@test c.h == 2
