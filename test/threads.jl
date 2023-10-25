K, = cyclotomic_field(19)
OK = maximal_order(K)
@test order(class_group(OK, GRH = false)[1]) == 1
