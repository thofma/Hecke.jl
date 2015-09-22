function check_return_type(f::Function, M::Module, print_only_bad::Bool = false)
  color(x) = contains_any(x) ? :red : :green

  met = methods(f)

  for m in met
    if (m.func.code.module != M)
      continue
    end

    return_type_bad = true

    a = Base.return_types(f, m.sig)
    for ret in a
      return_type_bad = contains_any(ret) && return_type_bad
    end

    if (print_only_bad && return_type_bad) || !print_only_bad
      print("name:\n$(m.func.code.name)\n")
      print("signature:\n")
      print_with_color(color(m.sig), "$(m.sig)\n")
      a = Base.return_types(f, m.sig)
      print("return values:\n")
      for ret in a
        print_with_color(color(ret), "$ret ")
      end
      print("\n")
      print("location:\n")
      print("$(m.func.code.file):$(m.func.code.line)\n")
      print("--------------------------------------------------------------------------------\n")
    end
  end
end

function check_return_type(f::DataType, M::Module, print_only_bad::Bool = false)
  color(x) = contains_any(x) ? :red : :green

  met = methods(f)

  for m in met
    if (m.func.code.module != M)
      continue
    end

    return_type_bad = true

    a = Any[]
    try
      a = Base.return_types(call, m.sig)
    catch
      continue
    end

    for ret in a
      return_type_bad = contains_any(ret) && return_type_bad
    end

    if (print_only_bad && return_type_bad) || !print_only_bad
      print("name:\n$(m.func.code.name)\n")
      print("signature:\n")
      print_with_color(color(m.sig), "$(m.sig)\n")
      a = Base.return_types(f, m.sig)
      print("return values:\n")
      for ret in a
        print_with_color(color(ret), "$ret ")
      end
      print("\n")
      print("location:\n")
      print("$(m.func.code.file):$(m.func.code.line)\n")
      print("--------------------------------------------------------------------------------\n")
    end
  end
end 

function check_bad_return_type(M::Module)
  for x in names(M)
    try y = eval(x)
      if isa(y, Function) || isa(y, DataType)
        check_return_type(y, M, true)
      end
    catch
      nothing
    end
  end
end

function contains_any(T)
  if typeof(T) == TypeVar
    #return contains_any(T.ub)
    return false
  elseif typeof(T) == Union
    return false
  elseif isleaftype(T)
    return false
  elseif length(T.parameters) == 0
    return T == Any
  else
    for P in T.parameters
      if contains_any(P)
        return true
      end
    end
  end
  return false
end
