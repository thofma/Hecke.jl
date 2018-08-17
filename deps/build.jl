using Pkg, Nemo, Libdl

oldwdir = pwd()

nemo_pkgdir = joinpath(dirname(pathof(Nemo)), "..")
#nemo_pkgdir = Pkg.dir("Nemo") 
nemo_wdir = joinpath(nemo_pkgdir, "deps")
nemo_vdir = joinpath(nemo_pkgdir, "local")

hecke_pkgdir = joinpath(@__DIR__, "..")
wdir = joinpath(hecke_pkgdir, "deps")
vdir = joinpath(hecke_pkgdir, "local")


if !ispath(joinpath(hecke_pkgdir, "local"))
    mkdir(joinpath(hecke_pkgdir, "local"))
end
if !ispath(joinpath(hecke_pkgdir, "local", "lib"))
    mkdir(joinpath(hecke_pkgdir, "local", "lib"))
end

function download_dll(url_string, location_string)
   try
      run(`curl -o $(location_string) -L $(url_string)`)
   catch
      download(url_string, location_string)
   end
end

LDFLAGS = "-Wl,-rpath,$nemo_vdir/lib -Wl,-rpath,\$\$ORIGIN/../share/julia/site/v$(VERSION.major).$(VERSION.minor)/Nemo/local/lib -Wl,-rpath,$vdir/lib -Wl,-rpath,\$\$ORIGIN/../share/julia/site/v$(VERSION.major).$(VERSION.minor)/Hecke/local/lib"
DLCFLAGS = "-fPIC -fno-common"

cd(wdir)

if Sys.iswindows()
   if Int == Int64
      download_dll("http://www.mathematik.uni-kl.de/~thofmann/hecke/bin/libhecke.dll", joinpath(vdir, "lib", "libhecke.dll"))
   else
      println("There is no libhecke for 32 bit Windows")
   end
else
   cd("$wdir/hecke")
   withenv("LD_LIBRARY_PATH"=>"$vdir/lib:$nemo_vdir/lib", "LDFLAGS"=>LDFLAGS) do
      run(`./configure --prefix=$vdir --disable-static --enable-shared --with-mpir=$nemo_vdir --with-mpfr=$nemo_vdir --with-flint=$nemo_vdir`)
      run(`make -j4`)
      run(`make install`)
   end
end

push!(Libdl.DL_LOAD_PATH, joinpath(hecke_pkgdir, "local", "lib"))

cd(oldwdir)

