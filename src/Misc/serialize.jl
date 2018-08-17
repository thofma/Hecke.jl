
#TODO: do binary...although this is exactly what BigInt does
function serialize(s::AbstractSerializer, t::fmpz)
  serialize_type(s, fmpz)
  return serialize(s, base(t, 62))
end

function deserialize(s::AbstractSerializer, ::Type{fmpz})
  return parse(fmpz, deserialize(s), 62)
end

function serialize(s::AbstractSerializer, t::fmpq)
  serialize_type(s, fmpq)
  serialize(s, base(numerator(t), 62))
  return serialize(s, base(denominator(t), 62))
end

function deserialize(s::AbstractSerializer, ::Type{fmpq})
  n = parse(fmpz, deserialize(s), 62)
  d = parse(fmpz, deserialize(s), 62)
  return fmpq(n, d)
end

function serialize(s::AbstractSerializer, t::PolyElem{T}) where T
  serialize_type(s, PolyElem{T})
  serialize(s, length(t))
  for i=0:length(t)
    serialize(s, coeff(t, i))
  end
end

function deserialize(s::AbstractSerializer, ::Type{PolyElem{T}}) where T
  L = T[]
  l = deserialize(s)
  for i=0:l
    push!(L, deserialize(s))
  end
  R = parent(L[1])
  Rx, x = PolynomialRing(R, :S, cached=false)
  return Rx(L)
end

function serialize(s::AbstractSerializer, t::AnticNumberField)
  serialize_type(s, AnticNumberField)
  return serialize(s, t.pol)
end

function deserialize(s::AbstractSerializer, ::Type{AnticNumberField})
  return number_field(deserialize(s), cached=false)[1]
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
  jobs = Dict{Int, Any}()
  while !done(r, st)
    while no_job < l
      if done(r, st)
        break
      end
      v, st = next(r, st)
      no_job += 1
      d = Distributed.nextproc()
      job_stat[d] += 1
      jobs[d] = time()
      @vtime :Par 2 @async put!(c, remotecall_fetch(f, d, v, d))
    end
    tw -= time()
    @vtime :Par 2 wait(c)
    tw += time()
    while isready(c)
      @vtime :Par 2 t = take!(c)
      push!(res, (t, time() - jobs[t[4]]))
      no_job -= 1
    end
  end
  @vprint :Par 2 "Finishing off..\n"
  push!(res, ((1,2,3.0,4), 5.0))
  while no_job > 0
    tw -= time()
    @vtime :Par 2 wait(c)
    tw += time()
    t = take!(c)
    push!(res, (t, time() - jobs[t[4]]))
    no_job -= 1
  end
  println("total waiting time was $tw")
  for (w,v) = job_stat
    println("$w -> $v")
  end
  return res
end

function addprocs(machines::AbstractVector; tunnel=false, sshflags=``, max_parallel=10, kwargs...)
  new = Base.Distributed.addprocs(Base.Distributed.SSHManager(machines); tunnel=tunnel, sshflags=sshflags, max_parallel=max_parallel, kwargs...)
  for d = new
    eval(Main, :(@spawnat $d eval(Main, :(include("/home/fieker/.julia/v0.6/Nemo/src/Nemo.jl");include("/home/fieker/.julia/v0.6/Hecke/src/Hecke.jl")))))
  end
  return new
end

