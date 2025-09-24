# Requires Oscar >= 1.5

using Oscar, Distributed

wp = oscar_worker_pool(3) # number of processes

grps = pmap(wp, [x^2 + d for d in PrimesSet(100000, 110110)]) do f
  println(f)
  class_group(maximal_order(number_field(f; cached = false)[1]))[1]
end
