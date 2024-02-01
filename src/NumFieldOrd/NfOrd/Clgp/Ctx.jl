################################################################################
#
#  The main class group part
#
################################################################################

function Base.deepcopy_internal(FB::NfFactorBase, dict::IdDict)
  c = NfFactorBase()
  c.fb = Dict(x => deepcopy(y) for (x, y) in FB.fb) # should be shallow
  c.size = FB.size
  c.fb_int = Base.deepcopy_internal(FB.fb_int, dict)
  c.ideals = [deepcopy(p) for p in FB.ideals]  # Not shallow,
                                               # otherwise the ideals reference each other
  c.rw = copy(FB.rw)
  c.mx = FB.mx
  return c
end

function Base.deepcopy_internal(FB::FactorBase{T}, dict::IdDict) where {T}
  return FactorBase(FB.base)
end

function Base.deepcopy_internal(FBS::FactorBaseSingleP{T}, dict::IdDict) where {T}
  lp = [(e, deepcopy(P)) for (e, P) in FBS.lp]
  if T === zzModPolyRingElem
    return FactorBaseSingleP(Int(FBS.P), lp)
  else
    @assert T === ZZModPolyRingElem
    return FactorBaseSingleP(FBS.P, lp)
  end
end
#mutable struct FactorBaseSingleP{T}
#  P::ZZRingElem
#  pt::FactorBase{T}
#  lp::Vector{Tuple{Int,AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}
#  lf::Vector{T}

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

function class_group_init(FB::NfFactorBase, T::DataType = SMat{ZZRingElem, ZZRingElem_Array_Mod.ZZRingElem_Array}; add_rels::Bool = true, use_aut::Bool = false)
  O = order(FB.ideals[1])
  n = degree(O)
  clg = ClassGrpCtx{T}()

  clg.FB = FB

  clg.bad_rel = 0
  clg.rel_cnt = 0
  clg.last = 0

  clg.M = ModuleCtx_fmpz(length(FB.ideals))
  clg.R_gen = Vector{AbsSimpleNumFieldElem}()
  clg.R_rel = Vector{AbsSimpleNumFieldElem}()

  clg.c = conjugates_init(nf(O).pol)
  add_rels && for I in clg.FB.ideals
    a = I.gen_one
    class_group_add_relation(clg, nf(O)(a), QQFieldElem(abs(a)^n), ZZRingElem(1), orbit = false)
    b = nf(O)(I.gen_two)
    bn = norm_div(b, ZZRingElem(1), 600)
    if nbits(numerator(bn)) < 550
      class_group_add_relation(clg, b, abs(bn), ZZRingElem(1), orbit = false)
    end
  end

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
  l, t = hnf_with_transform(l)
  if 1 + clg.c.r2 + 1 > nrows(l)
    t = zero_matrix(FlintZZ, 0, 0)
  else
    t = view(t, (1+clg.c.r2+1):nrows(l), 1:nrows(l))
  end
  l = lll(t)
  clg.val_base = l

  #if the galois group is small enough and the field large
  #then the split-norm-ctx is (much) better
  #the galois group size should, asymptotically, be
  #number of primes divided by totally split ones
  #lets accept this.
  ordG = length(collect(PrimesSet(ZZ(1), maximum(FB.fb_int.base)))) / length([x[1] for x = FB.fb if length(x[2].lp) == degree(O)])

  if use_aut
    au = automorphism_list(nf(O), copy = false)
    clg.aut_grp = class_group_add_auto(clg, au)
    clg.normCtx = NormCtx(O, div(nbits(discriminant(O)), 2) + 20,
        length(au) == degree(O) || ordG < 4*degree(O))
  else
    clg.normCtx = NormCtx(O, div(nbits(discriminant(O)), 2) + 20, ordG < 4*degree(O))
  end

  return clg
end

function class_group_init(O::AbsSimpleNumFieldOrder, B::Int; min_size::Int = 20, add_rels::Bool = true,
                          use_aut::Bool = false,
                          complete::Bool = true, degree_limit::Int = 0, T::DataType = SMat{ZZRingElem, ZZRingElem_Array_Mod.ZZRingElem_Array})
  @vprintln :ClassGroup 2 "Computing factor base ..."

  @assert B > 0

  FB = NfFactorBase()
  while true
    FB = NfFactorBase(O, B, complete = complete, degree_limit = degree_limit)
    if length(FB.ideals) > min_size
      break
    end
    B *= 2
    @vprintln :ClassGroup 2 "Increasing bound to $B ..."
  end
  @vprintln :ClassGroup 2 " done"
  return class_group_init(FB, T, add_rels = add_rels, use_aut = use_aut)
end

function _get_autos_from_ctx(ctx::ClassGrpCtx)
  return ctx.aut_grp::Vector{Tuple{morphism_type(AbsSimpleNumField, AbsSimpleNumField), Perm{Int}}}
end

################################################################################
#
#  Conversion to Magma
#
################################################################################
function to_magma(f::IOStream, clg::ClassGrpCtx)
  print(f, "K<a> := number_field(", nf(order(clg.FB.ideals[1])).pol, ");\n");
  print(f, "M := MaximalOrder(K);\n");
  print(f, "fb := [ ")
  for i=1:clg.FB.size
    to_magma(f, clg.FB.ideals[i], "M")
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

  to_magma(f, clg.M, name = "MM")
end

function to_magma(s::String, c::ClassGrpCtx)
  f = open(s, "w")
  to_magma(f, c)
  close(f)
end

################################################################################

function to_hecke(f::IOStream, clg::ClassGrpCtx; field_name = "K")
  O = order(clg.FB.ideals[1])
  L = nf(O)
  varr = string(L.S)
  print(f, "$field_name, $vvar = number_field(", nf(order(clg.FB.ideals[1])).pol, ", \"$varr\");\n");
  O = order(clg.FB.ideals[1])
  to_hecke(f, basis(O))
  print(f, "O = Order($field_name, map($field_name, R))\n")
  print(f, "O.is_maximal = 1\n")

  print(f, "c = Hecke.class_group_init(O, ", norm(clg.FB.ideals[1]), ")\n")

  #_print_nf_elem_array_serialize(a)

  R = vcat(clg.R_gen, clg.R_rel)
  for i = 1:length(R)
    print(f, "Hecke.class_group_add_relation(c, $field_name(", R[i], "))\n")
  end

end

function to_hecke(s::String, c::ClassGrpCtx; T...)
  f = open(s, "w")
  to_hecke(f, c; T...)
  close(f)
end

