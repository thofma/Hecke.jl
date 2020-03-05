#import "../Functions/Groups.m": matbas,matbas2,matbas3;
 
function voronoi_algorithm(V::VoronoiCtx; quite = false, SL = false)
  #{ImQuad: Voronoi algorithm. If SL is set everything will be done with respect to the special linear group instead of GL}
  #//Find a first perfect form
  n = V.n
  d = V.d
  steinitz = V.steinitz
  K = V.K
  w = V.w
  tau = V.tau
  p1 = V.p1
  p2 = V.p2
  ZB = V.ZB
  B = V.B
  BasHermNorm = V.BasHermNorm
  mmax = V.mmax
  F = V.F
  sqrtd = V.sqrtd
  Injec = V.Injec

  Pini = hermitian_space(K, n)
  Pinie, PiniToPinie, PinieToPini = restrict_scalars(Pini, FlintQQ, K(1//2))
  Pinie2, PiniToPinie2, Pinie2ToPini = restrict_scalars(Pini, FlintQQ, w * K(1//2))

  Lini = Zlattice(gram = gram_matrix(Pinie))

  Sini = _minimal_vectors(Pini, V)
  Rini = _perfection_rank(Pini, V)

  count = 1

  local Pc

  while Rini < n^2 && count <= 100
    count = count + 1
    dir = _find_perp(V, [hermitian_conjugate(x) * x for x in Sini])
    tsup = BigInt(1000)
    tinf = BigInt(0)
    t = (tsup + tinf)//2
    bool = false
    count2 = 1
    @show count

    while !bool && count2 < 100
      @show count2
      count2 += 1
      M = 1
      Pt = hermitian_space(K, gram_matrix(Pini) + t * dir)
      while M == 1
        @show M, t
        _tr = restrict_scalars(Pt, FlintQQ, K(1//2))[1]
        #@show Pt
        #@show ispositive_definite(_tr)
        if ispositive_definite(_tr)
          Lt = Zlattice(gram = gram_matrix(_tr))
          M = _hermitian_minimum(Pt, V)
          if M == 1
            tinf = t
            t = (tinf + tsup)//2
            Pt = hermitian_space(K, gram_matrix(Pini) + t * dir)
          end
        else
          tsup = t
          t = (tinf + tsup)//2
          Pt = hermitian_space(K, gram_matrix(Pini) + t * dir)
        end
      end

      St = _minimal_vectors(Pt, V)

      ttt = [ (K(_ideal_norm(V, v)) - (v * gram_matrix(Pini) * hermitian_conjugate(v))[1, 1])//(v * dir * hermitian_conjugate(v))[1, 1] for v in St]
      @assert all(x -> iszero(coeff(x, 1)), ttt)
      ttt = fmpq[ coeff(x, 0) for x in ttt]
      tt = minimum(ttt)
      bool = false
      if tt < t && tt > 0
        Pc = hermitian_space(K, gram_matrix(Pini) + K(tt) * dir)
        @show Pc
        Pce, _, _ = restrict_scalars(Pc, FlintQQ, K(1//2))
        Lc = Zlattice(gram = gram_matrix(Pce))
        M = _hermitian_minimum(Pc, V)
        if M == 1
          bool = true
        else
          tsup = tt
          t = (tinf + tsup)//2
          Pt = hermitian_space(K, gram_matrix(Pini) + K(t) * dir)
        end
      else
        tsup = t
        t = (tsup + tinf)//2
        Pt = hermitian_space(K, gram_matrix(Pini) + K(t) * dir)
      end
    end

    Pini = Pc
    Pinie, _, _ = restrict_scalars(Pini, FlintQQ, K(1//2))
    Lini = Zlattice(gram = gram_matrix(Pinie))
    Sini = _minimal_vectors(Pini, V)
    @show Pini
    Rini = _perfection_rank(Pini, V)
    @show Rini
  end

  if Rini != n^2
    error("The form Rini is not perfect?")
  end

  # //Enumerate perfect neighbours in order to obtain a set of representatives
  # //of perfect Hermitian forms

  perfectlist=[Pini]         #List of representatives of perfect forms
  vectlist =[]             #List of shortest vectors of perfect forms
  facelist =[]             # List of facets of V-domains of p. forms; given by shortest vectors
  faceneu=[];               #// 1 at [i][j] if neighbor(facelist[i][j]) >= i
  #// 0 else
  facevectlist =[]          #//Perpendicular form to shortest vectors defining the respective facet
  Dim2facevectList=[]      #
  FaceFormList=[]          #List of forms defined by those shortest vectors, which define the respective facet
  AutList=[];               #List of Aut-Groups of the inverse FaceForms
  Dim2FormList=[];          #
  Dim2FaceList=[];          #
  Dim2AutList=[];           #

  numberoffaces=[];           #List of number of faces of V-domains of p. forms
  E=Set([]);                     #multiset encoding the Voronoi graph of perfect forms
  Todo=[Pini];                #List of perfect forms to be treated with Voronoi
  minvecss=[_minimal_vectors(Pini, V)];
  PerfectNeighbourList=[];  #List of perfect neighbours of all (mod GL) perfect forms

  CriticalValueList=[];     #List of critical rho values (from Voronoi's algorithm)
  FacetVectorList=[];       #List of facet vectors (from Voronoi's algorithm)

  FaceTrafoList=[];

  NeighbourList=[];         #List of numbers of standard representatives of neighbours
  #
  #while length(Todo) > 0
  if length(Todo) > 0
    ###!!!!! uncomment
    P = popfirst!(Todo)
    Pe = restrict_scalars(P, FlintQQ, K(1//2))[1]
    L = Zlattice(gram = gram_matrix(Pe))
    m = _hermitian_minimum(P, V)
    Sk = _minimal_vectors(P, V)
    Sproj = [ _symmetric_coordinates(V, hermitian_conjugate(v) * v) for v in Sk]
    push!(vectlist, Sk)
    println("Still ", Todo+1, " forms to treat. I have found ", length(perfectlist), "perfect forms.")

    if _perfection_rank_list(V, Sk) != n^2
      error("In enumerating perfect neighbours: perfection rank of potential neighbour is too small.")
    end

    _G = _hermitian_automorphism_group(V, P, SL = SL)

    # We are doing it for now exactly as they do it
    
    G = [ change_base_ring(FlintQQ, g) for g in _G]
    # TEST

    append!(GeneratorsOfPolytope, [ _symmetric_coordinates(V, X) for X in Sprojtest])

    println("Generators of Polytope constructed")
    poly = polytope(GeneratorsOfPolytope)
    println("Polytope constructed")

    Faces = face_indices(poly, n^2 - 1)
  end


#  GeneratorsOfPolytope cat:= [Eltseq(SymmetricCoordinates(X)): X in Sprojtest];
#  //Ende der Aenderung. Scheint's zu tun... Kein Plan was hier gebacken ist.
#  print "Generators of Polytope constructed.";
#  Poly:=Polytope(GeneratorsOfPolytope);
#  print "Polytope constructed.";
#  Faces:=FaceIndices(Poly,n^2-1);
#  print "Faces calculated.";
#  Faces:=[Exclude(x,1) : x in Faces | 1 in x];
#  Faces:=[{a-1 : a in x} : x in Faces];
#  //return Faces;
#  P`Vertices:=[ CoordinatesToMatrix(Vector(x)) : x in Vertices(Poly) | x ne Vertices(Poly)[1]]; //Dies hier wurde kopiert. HIER MUESSEN WIR NOCHMAL RAN
#  Append(~numberoffaces,#Faces);
#  Append(~facelist,Faces);
#  FaceForms:=[];
#  AutFF:=[];
#  facevect:=[];
#  for F in Faces do
#   FF:=Parent(Pini`Matrix) ! 0;
#   for k in F do
#    Fk:= HermitianTranspose(Sk[k])*Sk[k];
#    FF := FF+ Fk;
#   end for;
#   gL:=FindPerp([HermitianTranspose(Sk[k])*Sk[k] : k in F]);
#   //if #gL eq 1 then
#    Append(~facevect,gL);
#   //end if;
#  end for;
#  Append(~facevectlist,[**]);
#
#  count:=0;
#  FFFaces:=Faces;
#
#  
# 
#  PerfectNeighbours:=[**];    //List of perfect neighbours of P being treated
#  Neighbours:=[**];           //List of indices of standard representatives of perf. neighbours of P
#  CriticalValues:=[**];       //List of critical rho-values of P
#  fneu:=[];
#  if not quiet then print "I am now treating a Voronoi domain which has " cat IntegerToString(#Faces) cat " faces."; end if;
#  TrafoList:=[**];
#  while(#Faces gt 0) do
#   count:=count+1;
#   
#   F1:=FindPerp([HermitianTranspose(Sk[n])*Sk[n] : n in Faces[1]]);
#   FF1:=NewHermForm(F1);
#   Exclude(~Faces,Faces[1]);
#   sgn:=Sign(&+ [Rationals()!EvaluateVector(FF1,x) : x in Sk]);
#   F1:=sgn*F1;
#   FF1:=NewHermForm(F1);
#   Append(~FacetVectorList,FF1);  //[??]
#
#//   F1:=FindPerp([(P`Vertices)[n] : n in Faces[1]]);
#   facevectlist[#facevectlist]:=facevectlist[#facevectlist] cat [*F1*];
#
#   //Append(~FacetVectorList,F1);  
#   //Exclude(~Faces,Faces[1]);
#   //sgn:=Sign(&+ [Rationals()!EvaluateVector(FF1,x) : x in Sk]);
#   //F1:=sgn*F1;
#   //FF1:=NewHermForm(F1);
#
#   tsup:=10000;
#   tinf:=0;
#   t:=(tinf+tsup)/2;
#   minimcont:=0;
#   while minimcont ne 1 do
#    coherent:=false;
#    while not coherent do
#     Pt:=NewHermForm(P`Matrix+t*F1);
#     M:=1;
#     while M eq 1 do
#      if IsPositiveDefinite(TraceForm(Pt)) then
#       M:=HermitianMinimum(Pt);
#       if M eq 1 then
#        tinf:=t;
#        t:=(tinf+tsup)/2;
#        Pt:=NewHermForm(P`Matrix+t*F1);
#       end if;
#      else
#       tsup:=t;
#       t:=(tinf+tsup)/2;
#       Pt:=NewHermForm(P`Matrix+t*F1);
#      end if;
#     end while;
#     St:=MinimalVectors(Pt);
#     SFace:=[ s : s in Sk | EvaluateVector(FF1,s) eq 0];
# 
#     Condlist:=[HermitianTranspose(s)*s : s in SFace] cat [HermitianTranspose(s)*s : s in St];
#     Cond:=KMatrixSpace(Rationals(),n^2,#Condlist)!0;
#     for i in [1..n^2] do
#      for j in [1..#Condlist] do
#       Cond[i][j]:=Trace(BasHermNorm[i]*Condlist[j]);
#      end for;
#     end for;
#     Uns:=Vector( #Condlist , [ Rationals()!(IdealNorm(v)) : v in SFace ] cat [Rationals()!(IdealNorm(v)) : v in St] );
#
# 
#     coherent:=IsConsistent(Cond,Uns);
#     if not coherent then
#      tsup:=t;
#      t:=(tinf+tsup)/2;
#      Pt:=NewHermForm(P`Matrix+t*F1);
#     end if;
#    end while;
#    Pcont:=NewHermForm(CoordinatesToMatrix(Solution(Cond,Uns)));
#    Pconte:=TraceForm(Pcont);
#    Lcont:=LatticeWithGram(Pconte);
#   
#    Scontk:=MinimalVectors(Pcont);
# 
#    minimcont:=HermitianMinimum(Pcont);
# 
#    tsup:=t;
#    t:=(tinf+tsup)/2;
#    Pt:=NewHermForm(P`Matrix+t*F1);
#   end while;
#      if Pcont eq NewHermForm(MatrixRing(K,n)!1) then error "BLA"; end if;
# 
#   Append(~PerfectNeighbours,Pcont);
# 
#   //Determine critical value rho:
#   C:=Pcont`Matrix-P`Matrix;
#   I:=0; J:=0;
#   for i in [1..n] do
#    for j in [1..n] do
#     if C[i][j] ne 0 then
#      I:=i; J:=j;
#      break i;
#     end if;
#    end for;
#   end for;
#   //Append(~CriticalValues , sgn*(C[I][J])/(F1[I][J]) );
#   Append(~CriticalValues , (C[I][J])/(F1[I][J]) );
# 
# 
#   iso:=false;
#   jjj := Position(perfectlist,P);
#   for i in [1..#perfectlist] do
#    bool,trans:=TestIsometry(Pcont,perfectlist[i]:SL:=SL);
#    if bool then
#     iso:=true;
#     Include(~E,<jjj,i>);
#     if jjj  le i then Append(~fneu,1); else Append(~fneu,0); end if;
#     Append(~Neighbours,i);
#     break;
#    end if;
#   end for;
#   if not iso then
#    Append(~perfectlist,Pcont);
#    Append(~minvecss,MinimalVectors(Pcont));
#    Append(~fneu,1);
#    Append(~Todo,Pcont);
#    Append(~TrafoList,MatrixRing(Integers(),2*n)!1);
#    Include(~E,<Position(perfectlist,P),Position(perfectlist,Pcont)>);
#    Append(~Neighbours,#perfectlist);
#   else
#    Append(~TrafoList,trans);
#   end if;
#  end while;
#  Append(~faceneu,fneu);
#  Append(~PerfectNeighbourList,PerfectNeighbours);
#  Append(~CriticalValueList,CriticalValues);
#  Append(~FaceTrafoList,matbas(TrafoList));
#  Append(~NeighbourList,Neighbours);
# end while;
#
# //Create a generating set of GL(L) as Z-matrices
# X:=[];
# for p in perfectlist do
#  X:=X cat [MatrixRing(Integers(),2*n)!x : x in Generators(HermitianAutomorphismGroup(p:SL:=SL))];
# end for;
# 
# MFL:=[];
# for a in FaceTrafoList do
#  X cat:= matbas2(a);
#  MFL cat:=matbas2(a);
# end for;
# ZGENS:=X; 
# OKGENS:=matbas(X);            //Z-generating system
# MFL:=matbas(MFL);    //OK-generating system
# MFL:=SetToSequence(SequenceToSet(MFL));
# MFL:=[x: x in MFL| x ne Parent(x)!1];
# 
# W:=KSpace(FieldOfFractions(Integers(K)),n);
# LatticeGens:=[W.i: i in [1..n-1]] cat [x*W.n: x in Generators(p2)];
# 
# 
# V:=New(VData);
# V`Lattice:=Module(LatticeGens);
# V`n:=n;
# V`d:=d;
# V`PerfectList:=perfectlist;
# V`FacesList:=facelist;
# V`ZGens:=ZGENS;
# V`OKGens:=OKGENS;
# V`MultFreeList:=MFL;
# V`CriticalValueList:=CriticalValueList;
# V`FaceTrafoList:=FaceTrafoList;
# V`NeighbourList:=NeighbourList;
# V`PerfectNeighbourList:=PerfectNeighbourList;
# V`PerpendicularList:=facevectlist;
# //V`PerpendicularList:=FacetVectorList;
# V`faceneu:=faceneu;
# 
# return V;
#end intrinsic;
end

function _minimal_vectors(A, V)
  K = base_ring(A)
  tr_form, _, _ = restrict_scalars(A, FlintQQ, K(1//2))
  L = Zlattice(gram = gram_matrix(tr_form))
  m = _hermitian_minimum(A, V)
  mmax = V.mmax
  S = short_vectors(L, m//mmax, m*mmax)
  @assert all(x -> !iszero(x[1]), S)
  Sk = _shorten_vectors(A, V, m, [s[1] for s in S])
  unique!(Sk)
  return Sk
end

function _hermitian_minimum(A, V)
  mmax = V.mmax
  K = base_ring(A)
  tr_form, _, _ = restrict_scalars(A, FlintQQ, K(1//2))
  L = Zlattice(gram = gram_matrix(tr_form))
  minL = minimum(L)
  S = short_vectors(L, minL//mmax, minL * mmax)
  m = minimum([_evaluate_vector(A, V, _shorten_vector(A, V, s[1])) for s in S])
end

function _shorten_vector(A, V, x)
  B = V.B
  n = V.n
  K = V.K
  res = zero_matrix(K, 1, n)
  for j in 1:2*n
    res = res + x[1, j] * B[j]
  end
  return res
end

function _shorten_vectors(A, V, m, S)
  res = []
  for i in 1:length(S)
    xk = _shorten_vector(A, V, S[i])
    @assert !iszero(xk)
    if _evaluate_vector(A, V, xk) == m
      push!(res, xk)
    end
  end
  return res
end

function _perfection_rank(A, V)
  mmax = V.mmax
  K = base_ring(A)
  tr_form, _, _ = restrict_scalars(A, FlintQQ, K(1//2))
  m = _hermitian_minimum(A, V)
  L = Zlattice(gram = gram_matrix(tr_form))
  S = short_vectors(L, m//mmax, m * mmax)
  Sk = _shorten_vectors(A, V, m, [ s[1] for s in S])
  @show length(S)
  r = _perfection_rank_list(Sk)
  return r
end

function _perfection_rank_list(Sk)
  n = ncols(Sk[1])
  M = zero_matrix(base_ring(Sk[1]), length(Sk), n^2)
  for i in 1:length(Sk)
    z = hermitian_conjugate(Sk[i]) * Sk[i]
    for j in 1:n^2
      M[i, j] = z[j]
    end
  end
  return rank(M)
end

function _evaluate_vector(A, V, x)
  K = V.K
  N = zero(K)
  n = V.n
  I = 0 * maximal_order(K)
  z = (x * gram_matrix(A) * hermitian_conjugate(x))[1, 1]
  for i in 1:(n - 1)
    I = I + x[1, i] * V.p1
  end
  I = I + x[1, n] * V.p1 * inv(V.p2)
  N = norm(I)
  @assert coeff(z, 1) == 0
  return coeff(z, 0)//N
end

function hermitian_conjugate(M::MatElem{nf_elem})
  K = base_ring(M)
  @assert degree(K) == 2
  A, mA = automorphism_group(K)
  sigma = mA(A[2])
  @assert sigma(gen(K)) != gen(K)
  return transpose(map_entries(sigma, M))
end

function _find_perp(V, L::Vector)
  K = V.K
  # I think this is nonsense
  bashermnorm = V.BasHermNorm
  M = zero_matrix(FlintQQ, length(bashermnorm), length(L))
  for i in 1:length(bashermnorm)
    for j in 1:length(L)
      t = trace((bashermnorm[i] * L[j])[1, 1])
      M[i, j] = t
    end
  end
  r, N = left_kernel(M)
  return sum(K(N[1, i]) * bashermnorm[i] for i in 1:length(bashermnorm))
end

function _ideal_norm(V, x)
  n = V.n
  K = V.K
  I = 0 * maximal_order(K)
  for i in 1:(n - 1)
    I = I + x[1, i] * V.p1
  end
  I = I + x[1, n] * V.p1 * inv(V.p2)
  N = norm(I)
  return N
end

function _symmetric_coordinates(V, A)
  n = V.n
  K = V.K
  z = zero_matrix(K, length(V.BasHermNorm), n^2)
  for i in 1:length(V.BasHermNorm)
    for k in 1:n^2
      z[i, k] = V.BasHermNorm[i][k]
    end
  end

  v = zero_matrix(K, 1, n^2)
  for k in 1:n^2
    v[1, k] = A[k]
  end

  fl, w = can_solve(z, v, side = :left)
  @assert A == sum(w[i] * V.BasHermNorm[i] for i in 1:length(V.BasHermNorm))
  return w
end 

function _order(a::nf_elem, ::typeof(*))
  n, = _torsion_units_gen(parent(a))
  n = 1
  b = a
  while !isone(b)
    b = b * a
    n += 1
  end
  return n
end

function _hermitian_automorphism_group(V, A; SL::Bool = false)
  K = V.K
  n = V.n
  if !SL
    return _hermitian_automorphism_group_absolute(V, A, check = true)
  else
    #G = _hermitian_automorphism_group_absolute(V, A, check = true)
    GG = automorphism_group_generators(lattice(A, identity_matrix(K, n)))
    detGG = [ det(t) for t in GG ]
    index = lcm([_order(t, *) for t in GG])
    if index == 1
      return _hermitian_automorphism_group_absolute(V, A, check = true)
    else
      H = [ x for x in GG if det(x) == 1]
      throw(NotImplemented())
    end
  end
end
  

function _hermitian_automorphism_group_absolute(V, A, check = true)
  tau = V.tau
  K = V.K
  n = V.n
  #Ae, _, _ = restrict_scalars(A, FlintQQ, K(1//2))[1]
  ZgramL, scalars, Babsmat, _ = _Zforms(lattice(A, identity_matrix(K, n)), [K(1//2), tau * K(1//2)])
  #L1 = gram_matrix(Ae)
  #Ae2, _, _ = restrict_scalars(A, FlintQQ, tau * K(1//2))[1]
  #L2 = gram_matrix(Ae2)

  Glll, T = lll_gram_with_transform(ZgramL[1])
  Ttr = transpose(T)
  ZgramLorig = ZgramL
  ZgramL = copy(ZgramL)
  for i in 1:length(ZgramL)
    ZgramL[i] = T * ZgramL[i] * Ttr
  end
  CC = ZLatAutoCtx(ZgramLorig)
  init(CC)
  auto(CC)
  gens, order = _get_generators(CC)
  if check
    for g in gens
      for i in 1:length(ZgramLorig)
        @assert g * ZgramLorig[i] * g' == ZgramLorig[i]
      end
    end
  end

  # Create the automorphism context and compute generators as well as orders
  C = ZLatAutoCtx(ZgramL)
  init(C)
  auto(C)
  return _get_generators(C)
end
