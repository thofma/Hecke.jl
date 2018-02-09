module HeckeProfile

function Profile.callersf(matchfunc::Function, bt::Vector, lidict::Profile.LineInfoFlatDict)
  counts = Dict{Profile.StackFrame, Int}()
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


end
