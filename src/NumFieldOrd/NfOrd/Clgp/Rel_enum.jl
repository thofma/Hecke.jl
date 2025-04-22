################################################################################
#
# More interesting search: Enumeration and other things on the Minkowski side
#
################################################################################

################################################################################
#
################################################################################

function enum_ctx_from_ideal(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},
                v::ZZMatrix; prec::Int = 100, limit::Int = 0, Tx::DataType = Int, TU::DataType = Float64, TC::DataType = Float64)

  l, t = lll(A, v, prec = prec)
  OK = order(A)
  K = nf(OK)
  temp = FakeFmpqMat(basis_matrix(A, copy = false))*basis_matrix(FakeFmpqMat, OK, copy = false)
  b = temp.num
  b_den = temp.den

  if limit == 0
    limit = nrows(l)
  end

  E = enum_ctx_from_gram(l, Tx = Tx, TC = TC, TU = TU,
                  limit = limit)::enum_ctx{Tx, TC, TU}
  E.t = t*b
  E.t_den = b_den
  ## we want to find x sth. norm(x) <= sqrt(|disc|)*norm(A)
  ## |N(x)^2|^(1/n) <= T_2(x)/n
  ## so if T_2(x) <= n * D^(1/n)
  ## then |N(x)| <= D^(1/2)
  #d = abs(discriminant(order(A))) * norm(A)^2
  #due to limit, the lattice is smaller and the disc as well.
  d = ZZRingElem(ceil(abs(prod(TC[TC(E.C[i,i]) for i=1:E.limit]))))
  ## but we don't want to overshoot too much the length of the last
  ## basis element.
  den = basis_matrix(FakeFmpqMat, OK, copy = false).den ## we ignore the den above, but this
                                ## changes the discriminant!!!
  b = min(den^2 * (iroot(d, E.limit) + 1)*E.limit * E.d, E.G[E.limit, E.limit]*E.limit)
  @v_do :ClassGroup 3 println("T_2 from disc ", (iroot(d, E.limit)+1)*E.limit * E.d)
  @v_do :ClassGroup 3 println("    from Gram ", E.G[E.limit, E.limit]*E.limit)
  @v_do :ClassGroup 3 println(" using ", b)
  enum_ctx_start(E, b)
  return E
end

_start = 0.0
function class_group_small_real_elements_relation_start(clg::ClassGrpCtx,
                A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; prec::Int = 200, val::Int = 0,
                limit::Int = 0)
  global _start
  @v_do :ClassGroup_time 2 rt = time_ns()
  while true
    try
      I = IdealRelationsCtx{Int, Float64, Float64}(clg, A, prec = prec, val = val, limit = limit)
      @v_do :ClassGroup_time 2 _start += time_ns()-rt
      return I
    catch e
      if isa(e, LowPrecisionCholesky)
        print_with_color(:red, "prec too low in cholesky,")
        prec = Int(ceil(1.2*prec))
        println(" increasing to ", prec)
        if prec > 1000
          _start = A
          error("1:too much prec")
        end
      elseif isa(e, LowPrecisionLLL)
        print_with_color(:red, "prec too low in LLL,")
        prec = Int(ceil(1.2*prec))
        println(" increasing to ", prec)
        if prec > 1000
          error("2:too much prec")
        end
      else
        rethrow(e)
      end
    end
  end
end

global _elt = UInt(0)

function class_group_small_real_elements_relation_next(I::IdealRelationsCtx)
  global _elt, _next
  K = nf(order(I.A))
  while true
    if enum_ctx_next(I.E)
#       println("elt is", I.E.x)
      # should we (again) add content_is_one()?
      if !isone(content(I.E.x))
        continue
      end
      @v_do :ClassGroup_time 2 rt = time_ns()
#      I.M = I.E.x * I.E.t
      I.M = mul!(I.M, I.E.x, I.E.t)
      q = elem_from_mat_row(K, I.M, 1, I.E.t_den)
#      println("found ", q, " norm ", norm(q)//norm(I.A))
      @v_do :ClassGroup_time 2 _elt += time_ns()- rt
      return q
    end
    @v_do :ClassGroup 2 print_with_color(:red, "restart after ")
    @v_do :ClassGroup 2 print(I.E.cnt)
    @v_do :ClassGroup 3 println(" for ", I.A, I.E.c)
    @v_do :ClassGroup 2 println(" length now ", I.E.c*2)
#    throw(NoElements())
    I.restart += 1
    if I.restart > 100
      _elt = I
      error("too much restarting");
    end
    enum_ctx_start(I.E, I.E.c*2)
  end
end


function show(io::IO, I::IdealRelationsCtx)
  println(io, "IdealRelationCtx for ", I.A)
  println(io, "  current length bound ", I.c, " stats: ", I.cnt, " and ", I.bad)
end

