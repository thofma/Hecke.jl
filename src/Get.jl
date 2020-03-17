# A draft for a "get some data" interface
const _lattice_data_src = "https://github.com/thofma/Hecke.jl/releases/download/DBtest/lattice_test"

function download_lattice_data(url::String = _lattice_data_src)
  println("This will download xx MB of data. Proceed? [Y/n]")
  n = readline()
  if n == "" || n == "Y" || n == "yes" || n == "Yes"
    Base.download(_lattice_data_src, joinpath(pkgdir, "data/lattices"))
  end
  nothing
end
