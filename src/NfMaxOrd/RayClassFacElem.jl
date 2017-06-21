

export ray_class_group_fac_elem

type MapRayClassGrpFacElem{T} <: Map{T, FacElemMon{NfMaxOrdIdlSet}}
  header::Hecke.MapHeader
  modulus_fin::NfMaxOrdIdl
  modulus_inf::Array{InfPlc,1}
  
  function MapRayClassGrpFacElem()
    return new()
  end
end


type MapMultGrp <: Map{GrpAbFinGen, NfMaxOrdQuoRing}
  header::Hecke.MapHeader

  function MapMultGrp()
    return new()
  end
end




function principal_gen_fac_elem(I::FacElem)
  
  
  J,a= Hecke.reduce_ideal2(I)
  x = Hecke.principal_gen_fac_elem(J)
  x=x*inv(a)
  return x
  
  
end


function _coprime_ideal_fac_elem(C::GrpAbFinGen, mC::Map, m::NfMaxOrdIdl)
 
  O=parent(m).order
  K=nf(O)
  L=NfMaxOrdIdl[]
  
  for i=1:ngens(C)
    a=mC(C[i])
    if iscoprime(a,m)
      push!(L,a)
    else  
      J=inv(a)
      s=K(rand(J.num,5))//J.den  # Is the bound acceptable?
      I=s*a
      simplify(I)
      I = num(I)
      while !iscoprime(I,m)
        s=K(rand(J.num,5))//J.den  
        I=s*a
        simplify(I)
        I = num(I)
      end
      push!(L,I)
    end
  end
  
  function exp(a::GrpAbFinGenElem)
  
    e=FacElem(Dict(ideal(O,1) => fmpz(1)))
    for i=1:ngens(C)
      if Int(a.coeff[1,i])!= 0
        e*=FacElem(Dict(L[i] => a.coeff[1,i]))
      end
    end
    return e
  
  end
  
  return exp

end 









function _multgrp_ray_class(Q::NfMaxOrdQuoRing)
  gens = Vector{NfMaxOrdQuoRingElem}()
  structt = Vector{fmpz}()
  disc_logs = Vector{Function}()
  i = ideal(Q)
  O=parent(i).order
  K=nf(O)
  fac = factor(i)
  # TODO calculate each primepower only once
  for (p,vp) in fac
    gens_p , struct_p , dlog_p = Hecke._multgrp_mod_pv(p,vp)

    # Make generators coprime to other primes
    if length(fac) > 1
      i_without_p = 1
      for (p2,vp2) in fac
        (p != p2) && (i_without_p *= p2^vp2)
      end

      pvp = p^vp
      alpha, beta = Hecke.extended_euclid(pvp,i_without_p)
      for i in 1:length(gens_p)
        g_pi_new = beta*gens_p[i] + alpha
        @hassert :NfMaxOrdQuoRing 2 (g_pi_new - gens_p[i] in pvp)
        @hassert :NfMaxOrdQuoRing 2 (g_pi_new - 1 in i_without_p)
        gens_p[i] = g_pi_new
      end
    end
    
    uni_p=Hecke.anti_uniformizer(p)
    
    function dlog_p_norm(x::NfOrdElem{Hecke.NfMaxOrd})
      
      val=valuation(x,p)
      if val==0
        return dlog_p(x)
      else 
        return dlog_p(O(K(x)*uni_p^val))
      end

    end

    gens_p = map(Q,gens_p)
    append!(gens,gens_p)
    append!(structt,struct_p)
    push!(disc_logs,dlog_p_norm)
  end
  
  G=DiagonalGroup(structt)
  
  function expo(a::GrpAbFinGenElem)   
    x=Q(1)
    for i=1:ngens(G)
      if Int(a.coeff[1,i])!= 0
        x=x*(gens[i]^(Int(a.coeff[1,i])))
      end
    end
    return x
  end
  
  function dlog(x::NfOrdElem{Hecke.NfMaxOrd})
    result = Vector{fmpz}()
    for disclog in disc_logs
      append!(result,disclog(x))
    end
    return G(result)
  end
  
  mG=MapMultGrp()
  mG.header=Hecke.MapHeader(G,Q,expo,dlog)
  
  return G, mG
end




function ray_class_group_fac_elem(m::NfMaxOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])

#
# We compute the group using the sequence U -> (O/m)^* _> Cl^m -> Cl -> 1
# First of all, we compute all these groups with their own maps
#  

  O=parent(m).order
  K=nf(O)
  

  C, mC = class_group(O)
  exp_class=_coprime_ideal_fac_elem(C,mC,m)
  U, mU = unit_group_fac_elem(O)
  M, pi= quo(O,m)
  G, mG=_multgrp_ray_class(M)
  
  p = [ x for x in inf_plc if isreal(x) ]
  if !isempty(p)
    H,lH,eH=Hecke._infinite_primes(O,p,m)
    T=G
    G=direct_product(G,H)
  end

#
# We start to construct the relation matrix
#
  RG=rels(G)
  RC=rels(C)

  A=vcat(RC, MatrixSpace(FlintZZ, ngens(G)+ngens(U), cols(RC))())
  B=vcat(MatrixSpace(FlintZZ, ngens(C), cols(RG))(), RG)
  B=vcat(B, MatrixSpace(FlintZZ, ngens(U) , cols(RG))())
 
#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#
  for i=1:ngens(U)
    u=mU(U[i])
    a=G([0 for i=1:ngens(G)])
    for (f,k) in u.fac
      if f in O
        a=a+k*(mG\(O(f)))
      else 
        d=den(f,O)
        n=f*d
        a=a+k*(mG\(O(n))) -k*(mG\(O(d)))
      end
    end
    a=a.coeff
    if !isempty(p)
      a=hcat(a, (lH(K(u))).coeff)
    end 
    for j=1:ngens(G)
      B[i+rows(RC)+rows(RG),j]=a[1,j]
    end
  end 

#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  for i=1: ngens(C)
    if order(C[i])!=1
      y=principal_gen_fac_elem((exp_class(C[i]))^(Int(order(C[i]))))
      b=G([0 for i=1:ngens(G)])
      for (f,k) in y.fac
        if f in O
          b=b+k*(mG\(O(f)))
        else 
          d=den(f,O)
          n=f*d
          b=b+k*(mG\(O(n))) -k*(mG\(O(d)))
        end
      end
      b=b.coeff
      if !isempty(p)
        b=hcat(b, (lH(K(y))).coeff)
      end 
      for j=1: ngens(G)
        B[i,j]=-b[1,j]
      end 
    end
  end

  R=hcat(A,B)
  X=AbelianGroup(R)

#
# Discrete logarithm
#

  function disclog(J::NfMaxOrdIdl)

    if isone(J)
      return X([0 for i=1:ngens(X)])
    else
      L=mC\J
      s=exp_class(L)
      I=FacElem(Dict(J => fmpz(-1)))* s
      A, c = Hecke.reduce_ideal2(I)
      p=Hecke.principal_gen_fac_elem(A)
      y=G([0 for i=1:ngens(G)])
      for (f,k) in p.fac
        if f in O
          y=y+k*(mG\(O(f)))
        else 
          d=den(f,O)
          n=f*d
          y=y+k*(mG\O(n) - mG\(O(d)))
        end
      end
      for (f,k) in c.fac
        if f in O
          y=y-k*(mG\(O(f)))
        else 
          d=den(f,O)
          n=f*d
          y=y-k*(mG\O(n) - mG\(O(d)))
        end
      end
      y=y.coeff
      if !isempty(inf_plc)
        z=lH(K(gamma))
        y=hcat(y, z.coeff)
      end 
      return X(hcat(L.coeff,y))
    end
  end 


#
# Exp map
#


  function expo(a::GrpAbFinGenElem)
    b=C([a.coeff[1,i] for i=1:ngens(C)])
    if isempty(inf_plc)
      c=G([a.coeff[1,i] for i=ngens(C)+1:ngens(X)])
      return exp_class(b)*ideal(O,pi\(mG(c)))
    else 
      c=T([a.coeff[1,i] for i=ngens(C)+1:ngens(T)+ngens(C)])
      d=H([a.coeff[1,i] for i=ngens(T)+ngens(C)+1: ngens(X)])
      el=pi\(mG(c))
      # I need to modify $el$ so that it has the correct sign at the embeddings contained in primes
      vect=(lH(K(el))).coeff
      if vect==d.coeff
        return ideal(O,el)*exp_class(b)
      else 
        correction=O(1)
        for i=1:ngens(H)
          if d.coeff[1,i]==1
            correction=correction*eH(H[i])
          end
        end
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return ideal(O,el)*exp_class(b)
      end 
    end
  end 

  mp=MapRayClassGrpFacElem{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElem{NfMaxOrdIdl} , expo, disclog)
  mp.modulus_fin=m
  mp.modulus_inf=p
 
  return X, mp
  
end



