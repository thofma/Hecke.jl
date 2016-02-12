using Hecke
using Base.Test

# write your own tests here
@test 1 == 1

Qx, x = PolynomialRing(QQ, "x")
K, a = NumberField(x^5 - 11^2 * 7)
O = MaximalOrder(K)

@test discriminant(O) == 109853253125

print("Tentative class and unit group computation ... ")
c, U, b = Hecke._class_unit_group(O);
println("DONE")
print("Saturating the tentative unit group ... ")
Hecke._refine_with_saturation(c, U)
println("DONE")
#@test c.h == 5
#@test Hecke._validate_class_unit_group(c, U) == 1

