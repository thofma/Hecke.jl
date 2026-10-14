if !isdefined(@__MODULE__, :AlgebraOrders)
  const AlgebraOrders = Hecke.AssociativeAlgebraOrders
end

if !isdefined(@__MODULE__, :algebra_order_test_rings)
  # Triples (R, Frac(R), p), with p a nonzero nonunit of R, for Z,
  # F_7[t], and the valuation ring of F_7(t) at infinity.
  function algebra_order_test_rings()
    F, t = rational_function_field(GF(7), "t")
    return ((ZZ, QQ, QQ(2)),
            (parent(numerator(t)), F, t),
            (localization(F, degree), F, inv(t)))
  end
end
