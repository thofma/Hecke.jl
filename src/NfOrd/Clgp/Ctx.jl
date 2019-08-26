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

function order(c::ClassGrpCtx)
  return ring(c.FB)
end

function nf(c::ClassGrpCtx)
  return nf(order(c))
end

function class_group_init(FB::NfFactorBase, T::DataType = SMat{fmpz}; add_rels::Bool = true, use_aut::Bool = false)
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
  add_rels && for I in clg.FB.ideals
    a = I.gen_one
    class_group_add_relation(clg, nf(O)(a), fmpq(abs(a)^degree(O)), fmpz(1), orbit = false)
    b = nf(O)(I.gen_two)
    bn = norm_div(b, fmpz(1), 600)
    if nbits(numerator(bn)) < 550
      class_group_add_relation(clg, b, abs(bn), fmpz(1), orbit = false)
    end
  end
  n = degree(O)
  l = zero_matrix(FlintZZ, n, 1+clg.c.r2)
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
  if 1 + clg.c.r2 + 1 > nrows(l)
    t = zero_matrix(FlintZZ, 0, 0)
  else
    t = sub(t, (1+clg.c.r2+1):nrows(l), 1:nrows(l))
  end
    l = lll(t)
  clg.val_base = l

  if use_aut
    au = automorphisms(nf(O))
    class_group_add_auto(clg, au[1])
    i = 2
    while length(clg.aut_grp) < length(au)
      class_group_add_auto(clg, au[i])
      i += 1
    end
    clg.normCtx = NormCtx(O, div(nbits(discriminant(O)), 2) + 20, 
                                                     length(au) == degree(O))
  else
    clg.normCtx = NormCtx(O, div(nbits(discriminant(O)), 2) + 20, false)
  end

  return clg
end

function class_group_init(O::NfOrd, B::Int; min_size::Int = 20, add_rels::Bool = true, 
                          use_aut::Bool = false,
                          complete::Bool = true, degree_limit::Int = 0, T::DataType = SMat{fmpz})
  @vprint :ClassGroup 2 "Computing factor base ...\n"

  FB = NfFactorBase()
  while true
    FB = NfFactorBase(O, B, complete = complete, degree_limit = degree_limit)
    if length(FB.ideals) > min_size
      break
    end
    B *= 2
    @vprint :ClassGroup 2 "Increasing bound to $B ...\n"
  end
  @vprint :ClassGroup 2 " done\n"
  return class_group_init(FB, T, add_rels = add_rels, use_aut = use_aut)
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

  R = vcat(clg.R_gen, clg.R_rel)
  print(f, "R := [ ")
  for i = 1:length(R)
    print(f, R[i])
    if i < length(R)
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

################################################################################

function toNemo(f::IOStream, clg::ClassGrpCtx; field_name = "K")
  O = order(clg.FB.ideals[1])
  L = nf(O)
  varr = string(L.S)
  print(f, "$field_name, $vvar = number_field(", nf(order(clg.FB.ideals[1])).pol, ", \"$varr\");\n");
  O = order(clg.FB.ideals[1])
  toNemo(f, basis(O))
  print(f, "O = Order($field_name, map($field_name, R))\n")
  print(f, "O.ismaximal = 1\n")

  print(f, "c = Hecke.class_group_init(O, ", norm(clg.FB.ideals[1]), ")\n")

  #_print_nf_elem_array_serialize(a)

  R = vcat(clg.R_gen, clg.R_rel)
  for i = 1:length(R)
    print(f, "Hecke.class_group_add_relation(c, $field_name(", R[i], "))\n")
  end

end

function toNemo(s::String, c::ClassGrpCtx; T...)
  f = open(s, "w")
  toNemo(f, c; T...)
  close(f)
end

