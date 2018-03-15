
#TODO: do binary...although this is exactly what BigInt does
function Base.serialize(s::AbstractSerializer, t::fmpz)
  Base.serialize_type(s, fmpz)
  return serialize(s, base(t, 62))
end

function Base.deserialize(s::AbstractSerializer, ::Type{fmpz})
  return parse(fmpz, deserialize(s), 62)
end

function Base.serialize(s::AbstractSerializer, t::fmpq)
  Base.serialize_type(s, fmpq)
  serialize(s, base(numerator(t), 62))
  return serialize(s, base(denominator(t), 62))
end

function Base.deserialize(s::AbstractSerializer, ::Type{fmpq})
  n = parse(fmpz, deserialize(s), 62)
  d = parse(fmpz, deserialize(s), 62)
  return fmpq(n, d)
end

function Base.serialize(s::AbstractSerializer, t::PolyElem{T}) where T
  Base.serialize_type(s, PolyElem{T})
  Base.serialize(s, length(t))
  for i=0:length(t)
    serialize(s, coeff(t, i))
  end
end

function Base.deserialize(s::AbstractSerializer, ::Type{PolyElem{T}}) where T
  L = T[]
  l = deserialize(s)
  for i=0:l
    push!(L, deserialize(s))
  end
  R = parent(L[1])
  Rx, x = PolynomialRing(R, :S, cached=false)
  return Rx(L)
end

function Base.serialize(s::AbstractSerializer, t::AnticNumberField)
  Base.serialize_type(s, AnticNumberField)
  return serialize(s, t.pol)
end

function Base.deserialize(s::AbstractSerializer, ::Type{AnticNumberField})
  return number_field(deserialize(s), cached=false)[1]
end

function parallel_class_group(a::Int, r::UnitRange)
  l = length(workers())
  cache = []
  st = start(r)
  res = []
  while !done(r, st)
    while length(cache) < 2*l
      if done(r, st)
        break
      end
      v, st = next(r, st)
      c = Channel(1)
      @async put!(c, remotecall_fetch(() -> length(Hecke.class_group(Hecke.wildanger_field(a, v)[1])[1]), Distributed.nextproc()))
      push!(cache, c)
    end
    i = 1
    while i <= length(cache)
      c = cache[i]
      println("test $c")
      if isready(c)
        @time f = take!(c)
        push!(res, f)
        deleteat!(cache, i)
      else
        i += 1
      end
    end
    sleep(0.1)
  end
  i = 1
  while length(cache) > 0
    c = cache[i]
    println("test $c")
    if isready(c)
      @time f = take!(c)
      push!(res, f)
      deleteat!(cache, i)
      if length(cache) == 0
        break
      end
    else
      i += 1
    end
    if i > length(cache)
      i = 1
      sleep(0.1)
    end
  end
  return res
end

add_verbose_scope(:Par)

function _bizarre(a::Int, b::Int)
  return length(Hecke.class_group(Hecke.wildanger_field(a, b)[1])[1])
end

function parallel_work(f::Function, r::UnitRange)
  l = length(workers())
  @vprint :Par 1 "using $l workers\n"
  cache = []
  st = start(r)
  res = []
  c = Channel(2*l+1)
  no_job = 0
  tw = 0.0
  job_stat = Dict(w => 0 for w = workers())
  while !done(r, st)
    while no_job < l
      if done(r, st)
        break
      end
      v, st = next(r, st)
      no_job += 1
      d = Distributed.nextproc()
      job_stat[d] += 1
      @vtime :Par 2 @async put!(c, remotecall_fetch(f, d, v))
    end
    tw -= time()
    @vtime :Par 2 wait(c)
    tw += time()
    while isready(c)
      @vtime :Par 2 push!(res, take!(c))
      no_job -= 1
    end
  end
  while no_job > 0
    tw -= time()
    @vtime :Par 2 push!(res, take!(c))
    tw += time()
    no_job -= 1
  end
  println("total waiting time was $tw")
  for (w,v) = job_stat
    println("$w -> $v")
  end
  return res
end
