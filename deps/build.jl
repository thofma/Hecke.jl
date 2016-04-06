on_windows = @windows ? true : false
on_osx = @osx ? true : false

oldwdir = pwd()

nemo_pkgdir = Pkg.dir("Nemo") 
nemo_wdir = Pkg.dir("Nemo", "deps")
nemo_vdir = Pkg.dir("Nemo", "local")

pkgdir = Pkg.dir("Hecke") 
wdir = Pkg.dir("Hecke", "deps")
vdir = Pkg.dir("Hecke", "local")


if !ispath(Pkg.dir("Hecke", "local"))
    mkdir(Pkg.dir("Hecke", "local"))
end
if !ispath(Pkg.dir("Hecke", "local", "lib"))
    mkdir(Pkg.dir("Hecke", "local", "lib"))
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

if on_windows
  error("not supported yet")
   if Int == Int64
      download_dll("http://www.mathematik.un-kl.de/~thofmann/hecke/bin/libhecke.dll", joinpath(vdir, "lib", "libhecke.dll"))
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

push!(Libdl.DL_LOAD_PATH, Pkg.dir("Hecke", "local", "lib"))

cd(oldwdir)

