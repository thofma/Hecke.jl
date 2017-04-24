################################################################################
#
#  The main class group part
#
################################################################################

function show(io::IO, c::ClassGrpCtx)
  println(io, "Ctx for class group of ", order(c.FB.ideals[1]))
  println(io, "Factorbase with ", length(c.FB.ideals), " ideals of norm up to ", norm(c.FB.ideals[1]))
  println(io, "Relations module: ", c.M)
end

function class_group_init(FB::NfFactorBase, T::DataType = SMat{fmpz})
  O = order(FB.ideals[1])

  clg = ClassGrpCtx{T}()

  clg.FB = FB

  clg.bad_rel = 0
  clg.rel_cnt = 0
  clg.last = 0

  clg.M = ModuleCtx_fmpz(length(FB.ideals))
  clg.R_gen = Array{nf_elem, 1}()
  clg.R_rel = Array{nf_elem, 1}()

  clg.c = conjugates_init(nf(O).pol)
  for I in clg.FB.ideals
    a = I.gen_one
    class_group_add_relation(clg, nf(O)(a), fmpq(abs(a)^degree(O)), fmpz(1), orbit = false)
    b = nf(O)(I.gen_two)
    bn = norm_div(b, fmpz(1), 600)
    if nbits(num(bn)) < 550
      class_group_add_relation(clg, b, abs(bn), fmpz(1), orbit = false)
    end
  end
  n = degree(O)
  l = MatrixSpace(FlintZZ, n, 1+clg.c.r2)()
  for i = 1:n
    l[i,1] = 1
  end
  for i = 1:clg.c.r2
    l[clg.c.r1+2*i, i+1] = 1
    l[clg.c.r1+2*i-1, i+1] = -1
  end
  # what I want is a lll-reduced basis for the kernel
  # it probably should be a sep. function
  # however, there is nullspace - which is strange...
  l,t = hnf_with_transform(l)
  t = sub(t, (1+clg.c.r2+1):rows(l), 1:rows(l))
  l = lll(t)
  clg.val_base = l
  return clg
end

function class_group_init(O::NfMaxOrd, B::Int;
                          complete::Bool = true, degree_limit::Int = 0, T::DataType = SMat{fmpz})
  @vprint :ClassGroup 2 "Computing factor base ...\n"

  FB = NfFactorBase()
  while true
    FB = NfFactorBase(O, B, complete = complete, degree_limit = degree_limit)
    if length(FB.ideals) > 10
      break
    end
    B *= 2
    @vprint :ClassGroup 2 "Increasing bound to $B ...\n"
  end
  @vprint :ClassGroup 2 " done\n"
  return class_group_init(FB, T)
end

function class_group_add_auto(clg::ClassGrpCtx, f::Map)
  p = induce(clg.FB, f)
  if isdefined(clg, :op)
    push!(clg.op, (f, p))
  else
    clg.op = [(f, p)]
  end
  clg.aut_grp = generated_subgroup(clg.op)
end  

################################################################################
#
#  Conversion to Magma
#
################################################################################
function toMagma(f::IOStream, clg::ClassGrpCtx)
  print(f, "K<a> := NumberField(", nf(order(clg.FB.ideals[1])).pol, ");\n");
  print(f, "M := MaximalOrder(K);\n");
  print(f, "fb := [ ")
  for i=1:clg.FB.size
    toMagma(f, clg.FB.ideals[i], "M")
    if i < clg.FB.size
      print(f, ",\n")
    end
  end
  print(f, "];\n")

  print(f, "R := [ ")
  for i = 1:length(clg.R)
    print(f, clg.R[i])
    if i < length(clg.R)
      print(f, ",\n")
    end
  end
  print(f, "];\n")

  toMagma(f, clg.M, name = "MM")
end

function toMagma(s::String, c::ClassGrpCtx)
  f = open(s, "w")
  toMagma(f, c)
  close(f)
end

