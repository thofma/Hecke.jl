function check_return_type(f)

  color(x) = isleaftype(x) ? :green : :red

  if isa(f, Function)
    print("--------------------------------------------------------------------------------")
    print("Analyzing return values of function $f\n")
    print("--------------------------------------------------------------------------------")
    met = methods(f)
    for m in met
      if (m.func.code.module != hecke) && (m.func.code.module != Nemo)
        continue
      end
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
  elseif isa(f, DataType)
    print("--------------------------------------------------------------------------------")
    print("Analyzing return values of constructors for $f\n")
    print("--------------------------------------------------------------------------------")
    met = methods(f)
    for m in met
      a = Any[]
      try
        a = Base.return_types(call, m.sig)
      catch
        continue
      end
      print("signature:\n")
      print_with_color(color(m.sig), "$(m.sig)\n")
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
  nothing
end

