
#TODO: do binary...although this is exactly what BigInt does

#function serialize(s::AbstractSerializer, t::ZZRingElem)
#  Serialization.serialize_type(s, ZZRingElem)
#  return serialize(s, base(t, 62))
#end
#
#function deserialize(s::AbstractSerializer, ::Type{ZZRingElem})
#  return parse(ZZRingElem, deserialize(s), 62)
#end
#
#function serialize(s::AbstractSerializer, t::QQFieldElem)
#  Serialization.serialize_type(s, QQFieldElem)
#  serialize(s, base(numerator(t), 62))
#  return serialize(s, base(denominator(t), 62))
#end
#
#function deserialize(s::AbstractSerializer, ::Type{QQFieldElem})
#  n = parse(ZZRingElem, deserialize(s), 62)
#  d = parse(ZZRingElem, deserialize(s), 62)
#  return QQFieldElem(n, d)
#end
#
#function serialize(s::AbstractSerializer, t::PolyRingElem{T}) where T
#  Serialization.serialize_type(s, PolyRingElem{T})
#  serialize(s, length(t))
#  for i=0:length(t)
#    serialize(s, coeff(t, i))
#  end
#end
#
#function deserialize(s::AbstractSerializer, ::Type{PolyRingElem{T}}) where T
#  L = T[]
#  l = deserialize(s)
#  for i=0:l
#    push!(L, deserialize(s))
#  end
#  R = parent(L[1])
#  Rx, x = polynomial_ring(R, :S, cached=false)
#  return Rx(L)
#end
#
#function serialize(s::AbstractSerializer, t::AbsSimpleNumField)
#  Serialization.serialize_type(s, AbsSimpleNumField)
#  return serialize(s, t.pol)
#end
#
#function deserialize(s::AbstractSerializer, ::Type{AbsSimpleNumField})
#  return number_field(deserialize(s), cached=false)[1]
#end
#
#function serialize(s::AbstractSerializer, t::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
#  Serialization.serialize_type(s, NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
#  return serialize(s, (domain(t), codomain(t), t.prim_img))
#end
#
#function deserialize(s::AbstractSerializer, ::Type{NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
#  K, L, a = deserialize(s)
#  return NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}(K, L, a)
#end
#

function _bizarre(a::Int, b::Int)
  return length(Hecke.class_group(Hecke.wildanger_field(a, b)[1])[1])
end

function parallel_work(f::Function, r::AbstractUnitRange)
  l = length(workers())
  @vprintln :Par 1 "using $l workers"
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
  @vprintln :Par 2 "Finishing off.."
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
