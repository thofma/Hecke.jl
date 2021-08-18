module HeckeProfile
using Hecke, Profile
using Base.StackTraces


function Profile.callers(fn::Symbol)
  return Profile.callers(String(fn))
end
#=
function Profile.callersf(matchfunc::Function, bt::Vector, lidict::Profile.LineInfoFlatDict)
  counts = Dict{StackFrame, Int}()
  lastmatched = false
  for id in bt
      if id == 0
	  lastmatched = false
	  continue
      end
      li = lidict[id]
      if lastmatched
	  if haskey(counts, li)
	      counts[li] += 1
	  else
	      counts[li] = 1
	  end
      end
      lastmatched = matchfunc(li)
  end
  k = collect(keys(counts))
  v = collect(values(counts))
  p = sortperm(v, rev=true)
  return [(v[i], k[i]) for i in p]
end

function Profile.callers(funcname::Symbol, bt::Vector, lidict::Profile.LineInfoDict; filename = nothing, linerange = nothing)
   bt, lid = Profile.flatten(bt, lidict)

    if filename === nothing && linerange === nothing
        return Profile.callersf(li -> li.func == funcname, bt, lid)
    end
    filename === nothing && throw(ArgumentError("if supplying linerange, you must also supply the filename"))
    if linerange === nothing
        return Profile.callersf(li -> li.func == funcname && li.file == filename, bt, lid)
    else
        return Profile.callersf(li -> li.func == funcname && li.file == filename &&
            in(li.line, linerange), bt, lid)
    end
end


Profile.callers(funcname::Symbol; kwargs...) = Profile.callers(funcname, Profile.retrieve()...; kwargs...)
Profile.callers(func::Function, bt::Vector, lidict::Profile.LineInfoDict; kwargs...) =
    Profile.callers(Symbol(func), bt, lidict; kwargs...)
Profile.callers(func::Function; kwargs...) = Profile.callers(Symbol(func), Profile.retrieve()...; kwargs...)

=#

#=
function Base.process_backtr(process_func::Function, t::Vector, limit::Int=typemax(Int); skipC = !true)
    n = 0
    last_frame = StackTraces.UNKNOWN
    count = 0
    for i = eachindex(t)
        lkups = StackTraces.lookup(t[i])
        for lkup in lkups
            if lkup === StackTraces.UNKNOWN
                continue
            end

            if lkup.from_c && skipC; continue; end
            if i == 1 && lkup.func == :error; continue; end
            count += 1
            if count > limit; break; end

            if lkup.file != last_frame.file || lkup.line != last_frame.line || lkup.func != last_frame.func
                if n > 0
                    process_func(last_frame, n)
                end
                n = 1
                last_frame = lkup
            else
                n += 1
            end
        end
    end
    if n > 0
        process_func(last_frame, n)
    end
end
=#
#=
  from base/profile.jl
  bt is a vector if UInt
    each complete backtrace corresponds to a block in bt between to 0
    iz = find(bt .== 0)
    then bt[1:iz[1]-1] is a complete trace
         bt[iz[1]+1:iz[2]-1] the next, ...
=#

function callers_frame(fname::Symbol, bt::Vector, lidict::Profile.LineInfoDict)
  counts = []
  st = typeof(bt)()
  skip = false
  found = false
  for id in bt
    skip = skip && id != 0
    skip && continue

    if id == 0
      st = typeof(bt)()
      continue
    end
    li = lidict[id]
    push!(st, id)
    for x in li
#      if contains(String(x.func), "eval_user_input")
      if x.func == :eval_user_input
        if found
          push!(st, 0)
          push!(counts, st)
          found = false
        end
        skip = true
        break
      end
      if x.func == fname
        found = true
        break
      end
    end
  end
  return counts
end

function leafs(bt::Vector, lidict::Profile.LineInfoDict, skipC::Bool = false)
  M = Hecke.MSet{Symbol}()
  skip = false
  for f = bt
    if !skip
      if f == 0
        continue
      end
      for fr = lidict[f]
        if skipC && fr.from_c
          continue
        end
        push!(M, fr.func)
        skip = true
        break
      end
    else
      skip = f!=0
    end
  end
  return M
end

function counts(bt::Vector, lidict::Profile.LineInfoDict, skipC::Bool = false)
  M = Hecke.MSet{Symbol}()
  for f = bt
    if f == 0
      continue
    end
    for fr = lidict[f]
      if skipC
        if !fr.from_c
          push!(M, fr.func)
        end
      else
        push!(M, fr.func)
      end
    end
  end
  return M
end

#all frames starting with fname
function prune(fname::Symbol, bt::Vector, lidict::Profile.LineInfoDict)
  rt = typeof(bt)()
  last = typeof(bt)()
  bingo = false
  for i=length(bt):-1:1
    g = bt[i]
    if g==0
      if bingo
        append!(rt, reverse(last))
        push!(rt, g)
        last = typeof(bt)()
      end
      @assert length(last) == 0
      bingo = false
      continue
    end
    for f = g
      if lidict[f][1].func == fname
        bingo = true
      end
      if bingo
        push!(last, g)
        break
      end
    end
  end
  if bingo
    append!(rt, reverse(last))
    push!(rt, UInt(0))
  end
  return rt
end

mutable struct Graph{T <: Any}
  v::Dict{T, Int}
  e::Dict{Tuple{T, T}, Int}
  function Graph{T}() where T
    r = new()
    r.v = Dict{T, Int}()
    r.e = Dict{Tuple{T, T}, Int}()
    return r
  end
end

function symb(a::StackFrame)
  if a.func==:Type
    if isdefined(a, :linfo) && isdefined(a.linfo, :value) && isdefined(a.linfo.value, :specTypes)
      return Symbol(a.linfo.value.specTypes)
    else
      return a.func
    end
  else
    return a.func
  end
end

function graph(bt::Vector, lidict::Profile.LineInfoDict, skipC::Bool = true, skipMacro::Bool=true; prune_by::Symbol = :nothing)
  if prune_by != :nothing
    bt = prune(prune_by, bt, lidict)
  end
  g = Graph{Symbol}()
  v = g.v
  e = g.e

  last = :rt
  Mac = Symbol("macro expansion")
  for f = bt
    if f==0
      last = :rt
      continue
    end
    for y = lidict[f]
      if skipC && y.from_c
        continue
      end
      fn = symb(y)
      if skipMacro && fn == Mac
        continue
      end
      if haskey(v, fn)
        v[fn] += 1
      else
        v[fn] = 1
      end
      t = (fn, last)
      if haskey(e, t)
        e[t] += 1
      else
        e[t] = 1
      end
      last = fn
    end
  end
  return g
end

graph(skipC::Bool = true, skipMacro::Bool=true; prune_by::Symbol = :nothing) = graph(Profile.retrieve()..., skipC, skipMacro, prune_by = prune_by)

function parents(g::Graph{T}, c::T)  where {T}
  return [a for (a,b) = keys(g.e) if b==c]
end

function parents_with_count(g::Graph{T}, c::T)  where {T}
  return [(a, d) for ((a,b), d) = g.e if b==c]
end

function children(g::Graph{T}, c::T) where {T}
  return [b for (a,b) = keys(g.e) if a==c]
end

function children_with_count(g::Graph{T}, c::T) where {T}
  return [(b, d) for ((a,b), d) = g.e if a==c]
end

#= usage:
  @profile s.th.

  Profile.callers(:jl_apply_generic)
  G = HeckeProfile.grpah();
  HeckeProfile.children(G, :+)
  ...

=#

end
