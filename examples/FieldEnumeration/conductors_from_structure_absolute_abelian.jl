using Hecke, DelimitedFiles

boundcond = ARGS[1]
gtype = ARGS[2]

_gtype = replace(replace(replace(replace(replace(gtype, '[' => '_'), ']' => '_'), ' ' => '_'), ',' => '_'), "__" => "_")

file = "conductors_" * boundcond * "_" * _gtype;

bound = fmpz(Meta.eval(Meta.parse(boundcond)))
gtype = convert(Vector{Int}, Meta.eval(Meta.parse(gtype)))

sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

gtype_right = snf(abelian_group(gtype))[1].snf
g_exp = gtype_right[end]
wild_primes = factor(g_exp).fac
for (p, v) in wild_primes
  if p == 2
    wild_primes[p] = v+2
  else
    wild_primes[p] = v+1
  end
end
conductors = Vector{Int}()
for i = 3:bound
  lf = factor(i)
  admissible = true
  for (p, v) in lf
    if p in keys(wild_primes)
      if v > 1 && v <= wild_primes[p]
        continue
      elseif v > wild_primes[p]
        admissible = false
        break
      else
        #we need to check that p-1 is not coprime to the other factors
        if length(wild_primes) == 1
          admissible = false
          break
        else
          t = p-1
          found = false
          for q in keys(wild_primes)
            if !is_coprime(t, q)
              found = true
              break
            end
          end
          if !found
            admissible = false
            break
          end
        end
      end
    else
      if v > 1
        admissible = false
        break
      end
      #p is tamely ramified...
      t = p-1
      found = false
      for q in keys(wild_primes)
        if !is_coprime(t, q)
          found = true
          break
        end
      end
      if !found
        admissible = false
        break
      end
    end
  end
  if admissible
    push!(conductors, i)
  end
end


println("DONE")

if length(ARGS) == 3
  file = ARGS[3]
else
  file = file * "_" * string(length(conductors))
end

if isfile(file)
  error("File $file already exists")
end

open(file, "w") do f
  print("Writing conductors to $file ... ")
  writedlm(f, conductors)
  println("DONE")
end

@assert countlines(file) == length(conductors)
