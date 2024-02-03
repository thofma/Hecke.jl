using Hecke

Base.:*(x::Hecke.RelNonSimpleNumFieldElem{Nemo.AbsSimpleNumFieldElem}) = x

function _get_simple_extension_and_maximal_order(K)
  @assert degree(base_ring(K)) == 1
  pol = K.pol
  k = length(pol)
  gensK = gens(K)
  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  basesofmaximalorders = Vector{elem_type(K)}[]
  discs = ZZRingElem[]
  for i in 1:k
    f = pol[i]
    g = zero(Qx)
    for j in 1:f.length
      g += coeff(f.coeffs[j], 1)* x^Int(f.exps[i, j])
    end
    L, _ = number_field(g)
    OL = maximal_order(L)
    push!(discs, discriminant(OL))
    BOL = map(z -> z.elem_in_nf, basis(OL))
    push!(basesofmaximalorders, [ sum(coeff(b, j) * gensK[i]^j for j in 0:degree(L)) for b in BOL ])
  end
  bbb = vec([ prod(c) for c in Iterators.product(basesofmaximalorders...) ])
  Ksimpleabs, g = Hecke.absolute_simple_field(Ksimple)
  prime_divisors = Set{ZZRingElem}()
  for i in 1:length(discs)
    for j in 1:(i - 1)
      ff = factor(gcd(discs[i], discs[j]))
      prime_divisors = union(prime_divisors, Set{ZZRingElem}([ p for (p, e) in ff ]))
    end
  end
  OO = Order(Ksimpleabs, [ g\b for b in bbb ])
  for p in prime_divisors
    OO = pmaximal_overorder(OO, p)
  end
  OO.is_maximal = 1
  set_attribute!(Ksimpleabs, :maximal_order => OO)
  return Ksimpleabs
end

bounddisc = ARGS[1]
real = ARGS[2]
gtype = ARGS[3]
startcond = ARGS[4]
endcond = ARGS[5]

bounddisc = ZZRingElem(eval(parse(bounddisc)))
gtype = convert(Vector{Int}, eval(parse(gtype)))
startcond = parse(Int, startcond)
endcond = parse(Int, endcond)
real = parse(Bool, real)

sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

Qx, x = polynomial_ring(QQ, "x")
K, a = number_field(x - 1, "a")
O = maximal_order(K)

n=prod(gtype)
expo=lcm(gtype)


if length(ARGS) == 6
   total_cond = countlines(ARGS[6])
else
   conductors = sort!(Hecke.conductorsQQ(O, gtype, bounddisc))
   total_cond = length(conductors)
end

upper_index = min(total_cond, endcond)

l_conductors = Vector{Int}(upper_index - startcond + 1)

if length(ARGS) == 6
   print("Loading conductors ... ")
   open(ARGS[6]) do f
     k = 1
     for (i, lline) in enumerate(eachline(f))
       if i < startcond
         continue
       end
       if i > upper_index
         break
       end
       l_conductors[k] = parse(Int, lline)
       k = k + 1
     end
   end
   #conductors = readdlm(ARGS[6], Int)
   #conductors = conductors[:, 1]
   println("DONE")
end

width = length(string(total_cond))

#@show l_conductors

fields=Tuple{AbsSimpleNumField, ZZRingElem}[]
#  autos=Vector{NfRelNSToNfRelNSMor}[]

#Now, the big loop
for (i, k) in enumerate(l_conductors)
  print("Left: $(length(l_conductors) - i)\n")
  r,mr=Hecke.ray_class_groupQQ(O,k,!real,expo)
  if !Hecke._are_there_subs(r,gtype)
    continue
  end
  ls=subgroups(r,quotype=gtype, fun= (x, y) -> quo(x, y, false)[2])
  for s in ls
    C=Hecke.ray_class_field(mr, s)
    if Hecke._is_conductor_minQQ(C,n) && Hecke.discriminant_conductorQQ(O,C,k,bounddisc,n)
      L=number_field(C)
      LL = _get_simple_extension_and_maximal_order(L)
      LLdisc = discriminant(maximal_order(LL))

      if LLdisc != prod( p^e for (p, e) in C.absolute_discriminant)
        println("Ups")
        @show LLdisc
        @show prod( p^e for (p, e) in C.absolute_discriminant)
        println("==========================")
      end

      push!(fields, (Hecke.simplify(LL)[1], LLdisc))
    end
  end
end

if length(ARGS) == 6
file = ARGS[6] * "_" * sprint_formatted("%0$(width)d", startcond) * "-" * sprint_formatted("%0$(width)d", upper_index)
else
file = sprint_formatted("%0$(width)d", startcond) * "-" * sprint_formatted("%0$(width)d", upper_index)
end

@show length(fields)

Hecke._write_fields(fields, file)

