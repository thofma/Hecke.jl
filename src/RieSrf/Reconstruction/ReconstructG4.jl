
function reconstruct_g4_curve_from_bi_tri_tangents(bitangents, tritangents)
  r = length(tritangents)
  CC = parent(tritangents[1][1][1])
  prec = precision(CC)
  RR = ArbField(prec)
  CC4, (x, y, z, w) = polynomial_ring(CC, [:x, :y, :z, :w])
  X4 = matrix(CC4, 4, 1, [x, y, z, w])
  mats1new =[matrix(tritangents[i][1] * transpose(tritangents[i][2])) for i in (1:r)]
  mats1new =[(m + transpose(m))/2 for m in mats1new]
  mats1newx = matrix(CC4, 1, r,[(transpose(X4) * mats1new[i] *X4)[1,1] for i in (1:r)])

  Xnew = matrix([reduce(vcat,[[m[i,j] for j in (i:4)] for i in (1:4)]) for m in mats1new])
  Xnewsym = matrix([vec(collect((m))) for m in mats1new]  )

  setprecision(BigFloat, prec)
  Xnew_float = Complex{BigFloat}.(collect(Xnew))

  vi = permutedims(nullspace(transpose(Xnew_float)))

  CC3, X = polynomial_ring(CC, 3)
  
  fs = [sum([el[i]*X[i] for i in (1:3)]) for el in bitangents[1:r]]
  mons = monomials_of_degree(CC3, 2)

  fsq_mat = Vector{AcbFieldElem}[]
  for f in fs
    cs = []
    for m in mons
      push!(cs, coeff(f^2,m))
    end
    push!(fsq_mat, cs)
  end
  fsq_mat = matrix(fsq_mat)
  fsq_mat_float = Complex{BigFloat}.(collect(fsq_mat))
  si = permutedims(nullspace(transpose(fsq_mat_float)))
  sirows = nrows(si)
  
  N = hcat([diagm(vi[i,:])*fsq_mat_float for i in (1:nrows(vi))]...)
  #//TODO: Check singular values to see if rank is too small. If so then compute more tritangents.
  #DN = svd(N).S
  tolerance = 10^(-precision(BigFloat) * 0.9 *log(2)/log(10))
  gammaiinv = permutedims(nullspace(transpose(N), rtol = tolerance))
  @req nrows(gammaiinv) == 1 "Error in the numerical computation."
  gammaiinv = gammaiinv[1,:]
  
  F = svd(Xnew_float)
  DXnew, U, V = F.S, F.U, F.V
  Upart_float = U[1:7,:]
  Upart = matrix(CC.(Upart_float))
  phi = Upart_float*diagm(gammaiinv)*fsq_mat_float

  #Kernel is not deterministic
  
  Qpre = permutedims(nullspace(transpose(phi)))
  Qpre1_float = Qpre*Upart_float

  Qpre1 = CC.(Qpre1_float)

  Qnew = sum([Qpre1[1,i]*mats1new[i] for i in (1:r) ])
  dualelt = mats1newx*transpose(matrix(Upart))
  
  VCeta = transpose(matrix([vec(collect(mat)) for mat in mats1new]))
  VCeta_float = Complex{BigFloat}.(collect(VCeta))
  VCetaperp = CC.(permutedims(nullspace(transpose(VCeta_float))))


  VCetaperpmats = [matrix(CC, 4,4, VCetaperp[i,:]) for i in (1:nrows(VCetaperp))]
  VCetaperpmats =[(m + transpose(m))/2 for m in VCetaperpmats]
  Qsharp = (VCetaperpmats[1]^-1+VCetaperpmats[2]^-1)^-1
  
  cond = Upart*Xnewsym* matrix(CC, 16, 1, vec(collect(Qsharp)))
  phiext = [matrix(CC,phi) cond]
  phiTinv = transpose(phiext)^(-1)
  phiL = dualelt*phiTinv
  qdual = zero_matrix(CC4, 3,3)
  count = 1
  for i in (1:3)
    for j in (i:3)
      qdual[i,j] = phiL[1,count]
      qdual[j,i] = phiL[1, count]
      count += 1
    end
  end
  detqdual = det(qdual)
  cubic = compute_sqrt_homogeneous(detqdual)
   
  quadric = collect(transpose(X4)*(Qnew*X4))[1,1]
  return [quadric, cubic]
end

function compute_sqrt_homogeneous(F)
	R = parent(F)
	CC = base_ring(R)
  X = gens(R)
  n = length(X)
	Rmi, _ = polynomial_ring(CC, n-1)
	d = div(total_degree(F),2)
	_, i0 = findmax([abs(coeff(F, X[i]^(2*d))) for i in (1:n)])
	varsmi = [X[i] for i in [1:i0-1 ; i0+1:n]]
	co = coeff(F, R[i0]^(2*d))
	Fnorm = F/co
	ret = R[i0]^d
	for i in (1:d)
		rem = Fnorm - ret^2
	  mons = [evaluate(mon, varsmi) for mon in monomials_of_degree(Rmi, i)]
		ret += 1/2 * sum([coeff(rem, m*X[i0]^(2*d-i))*m*X[i0]^(d-i) for m in mons])
	end
	return sqrt(co)*ret
end



function compute_tritangents(thetas::Dict{NTuple{8, Int64}, AcbFieldElem})
  tritangentsys =
   [(0, 1, 1, 0, 0, 1, 0, 0 ), (0, 1, 1, 0, 1, 1, 0, 0 )],
    [(0, 1, 0, 0, 0, 1, 0, 0 ), (0, 1, 0, 0, 1, 1, 0, 0 )],
    [(0, 1, 0, 1, 0, 1, 0, 0 ), (0, 1, 0, 1, 1, 1, 0, 0 )],
    [(0, 1, 1, 1, 0, 1, 0, 0 ), (0, 1, 1, 1, 1, 1, 0, 0 )],
    [(0, 1, 0, 1, 0, 1, 1, 0 ), (0, 1, 0, 1, 1, 1, 1, 0 )],
    [( 0, 1, 0, 0, 0, 1, 1, 0 ), (0, 1, 0, 0, 1, 1, 1, 0 )],
    [( 0, 1, 0, 0, 0, 1, 1, 1 ), (0, 1, 0, 0, 1, 1, 1, 1 )],
    [( 0, 1, 1, 1, 0, 1, 1, 1 ), (0, 1, 1, 1, 1, 1, 1, 1 )],
    [( 0, 1, 0, 0, 0, 1, 0, 1 ), (0, 1, 0, 0, 1, 1, 0, 1 )],
    [(0, 1, 1, 0, 0, 1, 0, 1 ), (0, 1, 1, 0, 1, 1, 0, 1 )]

  tritangentbasis = [
    (1, 1, 1, 0, 1, 1, 1, 0),
    (1, 0, 1, 0, 0, 0, 1, 0),
    (1, 1, 1, 0, 0, 0, 1, 0),
    (1, 0, 1, 0, 0, 1, 1, 0),
    (0, 1, 1, 0, 0, 1, 0, 0)]
  
  CC = parent(thetas[0,0,0,0,0,0,0,0])
  S1 = [[
    (1, 1, 0, 1, 0, 1, 1, 1),
    (0, 1, 1, 1, 1, 1, 0, 1,),
    (1, 1, 0, 1, 0, 1, 0, 1),
    (0, 1, 1, 1, 1, 1, 1, 0,),
    (1, 1, 1, 0, 1, 1, 0, 0,),
    (0, 1, 1, 0, 1, 1, 1, 1)],
[
    (0, 1, 0, 1, 0, 1, 1, 1),
    (1, 0, 1, 1, 0, 0, 1, 1),
    (0, 1, 0, 1, 0, 1, 0, 1),
    (1, 0, 1, 1, 0, 0, 0, 0,),
    (0, 1, 1, 0, 1, 1, 1, 0,),
    (1, 0, 1, 0, 0, 0, 0, 1)],
[
    (0, 1, 0, 1, 0, 1, 1, 1),
    (1, 1, 1, 1, 0, 0, 1, 1),
    (0, 1, 0, 1, 0, 1, 0, 1),
    (1, 1, 1, 1, 0, 0, 0, 0,),
    (0, 1, 1, 0, 1, 1, 1, 0,),
    (1, 1, 1, 0, 0, 0, 0, 1)],
[
    (0, 1, 0, 1, 0, 1, 0, 1),
    (1, 0, 1, 1, 0, 1, 1, 1),
    (0, 1, 0, 1, 0, 1, 1, 1),
    (1, 0, 1, 1, 0, 1, 0, 0),
    (0, 1, 1, 0, 1, 1, 1, 0),
    (1, 0, 1, 0, 0, 1, 0, 1)]]

  S2 = [[
    (0, 1, 0, 1, 0, 1, 0, 1),
    (1, 1, 1, 1, 1, 1, 1, 1),
    (0, 1, 0, 1, 0, 1, 1, 1),
    (1, 1, 1, 1, 1, 1, 0, 0),
    (0, 1, 1, 0, 1, 1, 1, 0),
    (1, 1, 1, 0, 1, 1, 0, 1)],
    [
    (1, 0, 0, 1, 1, 0, 0, 1),
    (0, 1, 1, 1, 1, 1, 0, 1),
    (1, 0, 0, 1, 1, 0, 1, 1),
    (0, 1, 1, 1, 1, 1, 1, 0),
    (1, 0, 1, 0, 0, 0, 0, 0),
    (0, 1, 1, 0, 1, 1, 1, 1)],
    [
    (1, 1, 0, 1, 1, 0, 0, 1),
    (0, 1, 1, 1, 1, 1, 0, 1),
    (1, 1, 0, 1, 1, 0, 1, 1),
    (0, 1, 1, 1, 1, 1, 1, 0),
    (1, 1, 1, 0, 0, 0, 0, 0),
    (0, 1, 1, 0, 1, 1, 1, 1)],
    [
    (1, 0, 0, 1, 1, 1, 1, 1),
    (0, 1, 1, 1, 1, 1, 0, 1),
    (1, 0, 0, 1, 1, 1, 0, 1),
    (0, 1, 1, 1, 1, 1, 1, 0),
    (1, 0, 1, 0, 0, 1, 0, 0),
    (0, 1, 1, 0, 1, 1, 1, 1)
]]

  Signs = [[-1,1],[1,-1],[-1,1],[-1,1]]

  S1S2signs = hard_coded_s1_s2()
  constant = zeros(CC, 4)
  for k in (1:4)
    temp_list = [tritangentbasis[1:k - 1]..., tritangentbasis[5],tritangentbasis[k+1:4]...]
    s1 = S1[k]
    s2 = S2[k]
    signs = Signs[k]
    T1 = CC(1)
    T2 = CC(1)
    for s in s1
      T1 *= thetas[s]
    end
    for s in s2
      T2 *= thetas[s]
    end
    constant[k] = signs[1]*T1 + signs[2]*T2
  end

  tritangents = [[zeros(CC, 4), zeros(CC, 4)] for t in (1:10)]
  for i in (1:10)
    for j in (1:2)
      for k in (1:4)
        S1, S2, signs = S1S2signs[i][j][k]
        T1 = CC(1)
        T2 = CC(1)
        for s in S1
          T1 *= thetas[s]
        end

        for s in S2
          T2 *= thetas[s]
        end
        tritangents[i][j][k] = (signs[1]*T1 + signs[2]*T2)/constant[k]
      end
    end
  end
  
  return tritangents
end

function Complex{BigFloat}(x::AcbFieldElem)
  return Complex{BigFloat}(real(x), imag(x))
end

function monomials_of_degree(R::MPolyRing, n::Int)
  X = gens(R)
  W = Iterators.product(repeat([X], n)...)
  result = Set{MPolyRingElem}()
  for a in W
    push!(result, prod(a))
  end
  return [r for r in result]
end


function preloop()
  id = identity_matrix(GF(2), 3)
  zero_block = zero_matrix(GF(2), 3, 3)
  J = [zero_block id
      id zero_block]
  J1 = [zero_block id
  zero_block zero_block]
  chars = sort(even_theta_characteristics(3))
  char_vecs = collect.(chars)

  V = vector_space(GF(2), 21)
  cs = [[GF(2)(1) for i in (1:36)]]

  for v in basis(V)
    T = upper_triangular_matrix(v.v[1,:])
    new = [(transpose(ve*T)*ve) for ve in char_vecs]
    push!(cs, new)
  end

  A = matrix(cs)
  A_ech = echelon_form(A)
  pivots = [minimum(filter( i -> A_ech[j,i] == one(GF(2)), (1:36))) for j in (1:21)]
  pivots_compl= filter(x -> !(x in pivots), (1:36))

  W = Iterators.product(repeat([[0,1]], 6)...)
  T = [ char_vecs[i] for i in pivots]
  Tcompl = [ char_vecs[i] for i in pivots_compl]

  function check_condition_bs(v1, v2)
    i = something(findfirst(isone, v1),0)
    j = something(findfirst(isone, v2),0)
    return transpose(v1*J)*v2 == 0 &&
    i < j && 
    iszero(v1[j]) && !iszero(v1) && !iszero(v2) &&  
    transpose(v1*J1)*v1 == transpose(v2*J1)*v2
  end

  bs = []

  for b1 in W
    for b2 in W 
      v1, v2 = collect.([b1,b2])
      if check_condition_bs(v1, v2)
        push!(bs, [v1,v2])
      end
    end
  end

 N = length(bs)

  function check_condition_cs(v1, v2, c)
    return transpose(v1*J)*c == transpose(v1*J1)*v1  &&
    transpose(v2*J)*c == transpose(v2*J1)*v2
  end

  cs = Vector{Vector{Int}}[]
  for b in bs
    temp = Vector{Int}[]
    for c in char_vecs
      if check_condition_cs(b[1],b[2], c)
        push!(temp, c)
      end
    end
    push!(cs, temp)
  end

  rep = [filter(x-> iszero(x[findfirst(isone, bs[i][1])]) &&  iszero(x[findfirst(isone, bs[i][2])]), cs[i]) for i in (1:length(bs))]
  cosets = [ [map(x-> mod.(x,2), [rep[i][j], rep[i][j]+bs[i][1],  rep[i][j]+bs[i][2], rep[i][j]+bs[i][1]+bs[i][2]]) for j in (1:3)]  for i in (1:N)]

  S = []
  A = []
  for k in (1:3)
    push!(S, filter(c-> all(x->x in T, cosets[c][k]), (1:161)))
    A = vcat(A, [[ [Int(any([cosets[i][2][j] == c for j in (1:4)]))  for c in Tcompl], [Int(any([cosets[i][3][j] == c for j in (1:4)])) for c in Tcompl]] for  i in S[k]])
  end

  Si = reduce(vcat, S)

  As = matrix(A[1])
  i = 2
  list = [Si[1]]
  listcoind = [1]
  while rank(As) < 15
    VJ = matrix([As ; matrix(A[i])])
    if rank(VJ) > rank(As)
      As = VJ
      push!(list, Si[i])
      if i < length(S[1])
        push!(listcoind, 1)
      elseif i < length(S[1]) + length(S[2])
        push!(listcoind, 2)
      else
        push!(listcoind, 3)
      end
    end
    i = i+1
  end
  usedbs = [bs[i] for i in list]
  usedrep = [rep[i] for i in list]
  return As, usedbs, usedrep, listcoind, Tcompl
end


function correct_signs(thetas)
  X, bs, rep, coind, Tcompl = preloop()

  id = identity_matrix(ZZ, 3)
  zero_block = zero_matrix(ZZ, 3, 3)
  J = [zero_block id
      id zero_block]
  J1 = [zero_block id
  zero_block zero_block]
  N = length(bs)

  F = GF(2)

  cosets = [ [[rep[i][j], rep[i][j]+bs[i][1],  rep[i][j]+bs[i][2], rep[i][j]-bs[i][1]-bs[i][2]] for j in (1:3)]  for i in (1:N)]
  cosets4 = [[[ [cosets[i][j][nu], cosets[i][j][nu] - bs[i][1], cosets[i][j][nu]- bs[i][2], cosets[i][j][nu]- bs[i][1]- bs[i][2] ] for nu in (1:4)] for j in (1:3)] for i in (1:N)]
  carry=[[[[[fld(cosets4[i][j][xi][mu][nu], 2) for nu in (1:6)] for mu in (1:4)] for xi in (1:4)] for j in (1:3)] for i in (1:N)]
  vec=FqFieldElem[]
  pairs = [F.([0,0]),F.([1,0]),F.([0,1]), F.([1,1])]
  for i in (1:N)
    #Term of the theta relation where the sign is fixed.
    coindi = coind[i]
    #Other two terms
      compl = filter(x-> x != coindi, (1:3)) 
      coeff = [sum([  ZZ(-1)^ sum([transpose(cosets4[i][j][xi][mu]*J1)*carry[i][j][xi][mu] for xi in (1:4)]) for mu in (1:4)  ]) for j in (1:3)]
      if rep[i][1] == [0,0,0,0,0,0]
		    coeff[1] -= 8
	    end
    sigsposs = [[coeff[j] for nu in (1:4)] for j in (1:3) ]
    #= nu=1 means no sign switch
      nu=2 means 1st sign switches
      nu=3 means 2nd sign switches
      nu=4 means both signs switch
    =#
    sigsposs[compl[1]][2] *= (-1)
    sigsposs[compl[2]][3] *= (-1)
    sigsposs[compl[1]][4] *= (-1)
    sigsposs[compl[2]][4] *= (-1)

    thetarel = [abs(sum([sigsposs[j][nu]*  prod([thetas[map(x -> mod(x,2), cosets[i][j][xi])... ] for xi in (1:4)]) for j in (1:3)]))   for nu in (1:4)]
    min, ind = findmin(thetarel)
    vec = [vec ; pairs[ind]] 
  end

  sol = solve(transpose(matrix(F, X)), vec)
  for j in (1:length(Tcompl))
    thetas[Tcompl[j]...] *= ZZ(-1)^(lift(ZZ,sol[j]))
  end
  return thetas
end


function moduli_from_theta(theta_dict)
  inds = Hecke.theta_characteristics_indices(3)
  thetas = [theta_dict[inds[i]] for i in (1:64)]
  I = onei(parent(thetas[1]))
  a1 = I*thetas[34]*thetas[6]/(thetas[41]*thetas[13])
  a2 = I*thetas[22]*thetas[50]/(thetas[29]*thetas[57])
  a3 = I*thetas[8]*thetas[36]/(thetas[15]*thetas[43])
  ap1 = I*thetas[6]*thetas[55]/(thetas[28]*thetas[41])
  ap2 = I*thetas[50]*thetas[3]/(thetas[48]*thetas[29])
  ap3 = I*thetas[36]*thetas[17]/(thetas[62]*thetas[15])
  as1 = -thetas[55]*thetas[34]/(thetas[13]*thetas[28])
  as2 = thetas[3]*thetas[22]/(thetas[57]*thetas[48])
  as3 = thetas[17]*thetas[8]/(thetas[43]*thetas[62])
  return [a1, a2, a3, ap1, ap2, ap3, as1, as2, as3]
end

function riemann_model_from_moduli(mods)
  a1 = mods[1]; a2=mods[2];   a3 = mods[3]
  ap1 = mods[4];ap2 = mods[5];ap3 = mods[6]
  as1 = mods[7];as2 = mods[8];as3 = mods[9]
  CC = parent(a1)
  P, (x1,x2,x3) = polynomial_ring(CC,[:x1, :x2, :x3])
  k=1;kp=1;ks=1
  M = matrix([CC.([1,1,1]),[k*a1,k*a2,k*a3],[kp*ap1,kp*ap2,kp*ap3]])
  Mb = matrix([CC.([1,1,1]),[1/a1,1/a2,1/a3],[1/ap1,1/ap2,1/ap3]])
  U = -Mb^(-1)*M
  u1 = U[1,:];u2 = U[2,:];u3 = U[3,:]
  u1 = u1[1]*x1 + u1[2]*x2 + u1[3]*x3
  u2 = u2[1]*x1 + u2[2]*x2 + u2[3]*x3
  u3 = u3[1]*x1 + u3[2]*x2 + u3[3]*x3
  return (x1*u1+x2*u2-x3*u3)^2-4*x1*u1*x2*u2, u1, u2, u3
end

function compute_bitangents(thetas)
  CC = parent(thetas[0,0,0,0,0,0,0,0])
  chars_even = even_theta_characteristics(3)
  g3thetas = Dict{NTuple{6, Int64}, AcbFieldElem}()
  for char in chars_even
    delta_new1 = (0, char[1:3]..., 0, char[4:6]...)
    delta_new2 = (0, char[1:3]..., 1, char[4:6]...)
    #Formula from Lemma 1 (p. 148) of Farkas
    g3thetas[char] = sqrt(thetas[delta_new1]*thetas[delta_new2])
  end

  for char in odd_theta_characteristics(3)
    g3thetas[char] = zero(CC)
  end
  
  g3thetas = correct_signs(g3thetas)
  mods = moduli_from_theta(g3thetas)
  mods_mat = [[mods[i], mods[i+1], mods[i+2]] for i in [1,4,7]]
  ks = matrix(CC, 3, 1, [1,1,1])
  bitangents = map(x->CC.(x), [ [1, 0, 0], [0,1,0], [0,0,1], [1,1,1]])
  bitangents = [bitangents ; mods_mat]
  F, u0, u1, u2 = riemann_model_from_moduli(mods)
  R = parent(u0)
  X = gens(R)
  t0, t1, t2 = X
  bitangents = [bitangents ; [[coeff(el, x) for x in X] for el in [u0, u1, u2]]]
  bitangents = [bitangents ; [[coeff(el, x) for x in X] for el in [t0+t1+u2, t0+u1+t2, u0+t1+t2]]]

  mods_mat = transpose(matrix(mods_mat))
# (3)
  for i in (1:3)
    new = u0/mods_mat[1,i] + ks[i,1]*(mods_mat[2,i]*t1 + mods_mat[3,i]*t2)
    push!(bitangents, [coeff(new, x) for x in X])
  end
# (4)
  for i in (1:3)
    new = u1/mods_mat[2,i] + ks[i,1]*(mods_mat[1,i]*t0 + mods_mat[3,i]*t2)
    push!(bitangents, [coeff(new, x) for x in X])
  end
# (5)
  for i in (1:3)
    new = u2/mods_mat[3,i] + ks[i,1]*(mods_mat[1,i]*t0 + mods_mat[2,i]*t1)
    push!(bitangents, [coeff(new, x) for x in X])
  end
# (6)
  modsinv = inv(mods_mat)

  D = diagonal_matrix([1/el for el in modsinv*CC.([1,1,1])])
  modstra = transpose(D*modsinv)
  Atra = transpose(matrix(CC, 3,3, [1/el for el in modstra]))
  lambdastra = solve(transpose(Atra), CC.([-1,-1,-1]))
  Ltra = diagonal_matrix(lambdastra)
  Btra = transpose(modstra)*Ltra
  kstra = solve(transpose(Btra), CC.([-1,-1,-1]))

  k = kstra[1]
  kp = kstra[2]

  M = matrix([CC.([1,1,1]), (k*modstra)[1,:], (kp*modstra)[2,:]])
  Mb = matrix([CC.([1,1,1]), transpose(Atra)[1,:], transpose(Atra)[2,:]])
  U = -Mb^(-1)*M
  u1tra = U[1,:]*inv(modstra)
  u2tra = U[2,:]*inv(modstra)
  u3tra = U[3,:]*inv(modstra)

  bitangents = [bitangents ; [u1tra, u2tra, u3tra]]
# (7)
  for i in (1:3)
    new = u0/(mods_mat[1,i]*(1-ks[i,1]*mods_mat[2,i]*mods_mat[3,i])) + u1/(mods_mat[2,i]*(1-ks[i,1]*mods_mat[1,i]*mods_mat[3,i])) + u2/(mods_mat[3,i]*(1-ks[i,1]*mods_mat[1,i]*mods_mat[2,i]))
    push!(bitangents, [coeff(new, x) for x in X])
  end
  return bitangents
end

function tritangent_planes_g4(tau::AcbMatrix, chars::Vector)
  
  result = []
  z = 
  thetas_plus_derivatives = theta_jets(z, tau, 1)
  for char in chars
    n = CharacteristicToInteger(char)
    Th_derivs = [thetas_plus_derivatives[n+1][i] : i in [2..5]]
    Th_derivs = Eltseq(Matrix(1, 4, Th_derivs)*(Pi1^-1))
    push!(result, Th_derivs)
  end

  return result
end



function lift_SL_n(A, n)
  p = characteristic(base_ring(A))
  @req base_ring(A) == GF(p) "Base ring of A needs to be a primitive finite field."

  n = number_of_rows(A)
  A_inv = A^(-1)
  col = findfirst(x !=0, A[1,:])
  entry = ZZ((Ainv[1, col]^(-1)))
  A_lift = A
  for i in (2:n)
    ZZpi, phi = residue_ring(ZZ, p^i)
    Alift = change_base_ring(ZZpi, change_base_ring(ZZ, A_lift))
    eps = ZZ((det(A_lift) - 1))
    Alift[col,1] -= eps*entry
  end
  return Alift
end

function _split_in_blocks(S::MatrixElem)
  A = S[1:4, 1:4]
	B = S[1:4, 5:8]
	C = S[5:8, 1:4]
	D = S[5:8, 5:8]
  return A, B, C, D
end

function reconstruct_g4_curve_generic(g4thetas)
  tritangents = compute_tritangents(g4thetas)
  bitangents = compute_bitangents(g4thetas)

  quadric, cubic = reconstruct_g4_curve_from_bi_tri_tangents([bitangents[i] for i in [10, 23, 4, 20,  17, 9, 12,  1, 5, 11]], tritangents)
  return [quadric, cubic]
end

#Should check if this is correct
function transform_theta_nulls(g4thetas, S)
  transformed_thetas = g4thetas
  for char in even_theta_characteristics(4)
    im_char = apply_transformation_to_char(S, char)
    transformed_thetas[map(x -> mod(x,2), 2*imchar)... ] = theta_HI(g4thetas, im_char)
  end
  return transformed_thetas
end

function rec_g4_curve_vanishing_theta_null(g4thetas, v)
	g = 4
	CC = parent(g4thetas[0,0,0,0,0,0,0,0])
	S = MapSympl(Vector([GF(2)! el : el in v[1] cat v[2]]))
  transform_theta_nulls(g4thetas, S)

  #I think this block is identical to the non-vanishing theta null case
  tritangents = compute_tritangents(g4thetas)

  #As we have one vanishing theta null, we can choose our Prym in such a way
  #that we get a genus 3 hyperelliptic curve.
  bitangents = compute_bitangents_hyp(g4thetas)
  bitangents =[bitangents[i] for i in  [24, 20, 21, 23, 17, 16, 15, 14, 19, 26 ]]
  
  r = length(tritangents)
  CC = parent(tritangents[1][1][1])
  prec = precision(CC)
  RR = ArbField(prec)
  CC4, (x, y, z, w) = polynomial_ring(CC, [:x, :y, :z, :w])
  X4 = matrix(CC4, 4, 1, [x, y, z, w])
  mats1new =[matrix(tritangents[i][1] * transpose(tritangents[i][2])) for i in (1:r)]
  mats1new =[(m + transpose(m))/2 for m in mats1new]
  mats1newx = matrix(CC4, 1, r,[(transpose(X4) * mats1new[i] *X4)[1,1] for i in (1:r)])

  Xnew = matrix([reduce(vcat,[[m[i,j] for j in (i:4)] for i in (1:4)]) for m in mats1new])
  Xnewsym = matrix([vec(collect((m))) for m in mats1new]  )

  setprecision(BigFloat, prec)
  Xnew_float = Complex{BigFloat}.(collect(Xnew))

  vi = permutedims(nullspace(transpose(Xnew_float)))

  CC3, X = polynomial_ring(CC, 3)
  
  fs = [sum([el[i]*X[i] for i in (1:3)]) for el in bitangents[1:r]]
  mons = monomials_of_degree(CC3, 2)

  fsq_mat = Vector{AcbFieldElem}[]
  for f in fs
    cs = []
    for m in mons
      push!(cs, coeff(f^2,m))
    end
    push!(fsq_mat, cs)
  end
  fsq_mat = matrix(fsq_mat)
  fsq_mat_float = Complex{BigFloat}.(collect(fsq_mat))
  si = permutedims(nullspace(transpose(fsq_mat_float)))
  sirows = nrows(si)
  
  N = hcat([diagm(vi[i,:])*fsq_mat_float for i in (1:nrows(vi))]...)
  #//TODO: Check singular values to see if rank is too small. If so then compute more tritangents.
  #DN = svd(N).S
  tolerance = 10^(-precision(BigFloat) * 0.9 *log(2)/log(10))
  gammaiinv = permutedims(nullspace(transpose(N), rtol = tolerance))
  @req nrows(gammaiinv) == 1 "Error in the numerical computation."
  gammaiinv = gammaiinv[1,:]
  
  F = svd(Xnew_float)
  DXnew, U, V = F.S, F.U, F.V
  Upart_float = U[1:7,:]
  Upart = matrix(CC.(Upart_float))
  phi = Upart_float*diagm(gammaiinv)*fsq_mat_float

  #Kernel is not deterministic
  
  Qpre = permutedims(nullspace(transpose(phi)))
  Qpre1_float = Qpre*Upart_float

  Qpre1 = CC.(Qpre1_float)

  Qnew = sum([Qpre1[1,i]*mats1new[i] for i in (1:r) ])
  dualelt = mats1newx*transpose(matrix(Upart))
  
  VCeta = transpose(matrix([vec(collect(mat)) for mat in mats1new]))
  VCeta_float = Complex{BigFloat}.(collect(VCeta))
  VCetaperp = CC.(permutedims(nullspace(transpose(VCeta_float))))


  VCetaperpmats = [matrix(CC, 4,4, VCetaperp[i,:]) for i in (1:nrows(VCetaperp))]
  VCetaperpmats =[(m + transpose(m))/2 for m in VCetaperpmats]
  Qsharp = (VCetaperpmats[1]^-1+VCetaperpmats[2]^-1)^-1
  
  cond = Upart*Xnewsym* matrix(CC, 16, 1, vec(collect(Qsharp)))
  phiext = [matrix(CC,phi) cond]
  phiTinv = transpose(phiext)^(-1)
  phiL = dualelt*phiTinv
  qdual = zero_matrix(CC4, 3,3)
  count = 1
  for i in (1:3)
    for j in (i:3)
      qdual[i,j] = phiL[1,count]
      qdual[j,i] = phiL[1, count]
      count += 1
    end
  end
  detqdual = det(qdual)

  #CHECK IF WE STILL NEED SQRT ON CONE or if it's automatic here as well.
  
  S:= NormalForm(Qnew);

  //Compute the matrix S2 whose inverse will transform the normal form into one where all coefficients are 1.

  S2 := S * Qnew * Transpose(S);
  
  _, ind := Min([Abs(S2[i,i]) : i in [1..4]]); //sometimes the smallest is not the last one

  for i in [1..4] do
    if i ne ind then 
      S2[i,i] := Sqrt(S2[i,i]);
    end if;
  end for;
  S2[ind,ind] := 1;

  L_swap := [1,2,3,4];
  L_swap[ind] := 4;
  L_swap[4] := ind;
  P_swap := PermutationMatrix(CC, L_swap);

  I:=CC.1;
//Coordinate Transformation that maps x^2 + y^2 +z^2 to xy - z^2.
  DiagToCone := Matrix(CC, 4, 4, [[1,0,0,0],[0,1/2*I,-1/2,0],[0,1/2*I,1/2,0], [0,0,0,1]])*P_swap;

//Complete Transformation
  QtoCone := DiagToCone * S2^(-1) * S; 


  v:=Matrix(CC4, [[CC4.1, CC4.2, CC4.3, CC4.4]]);

  //Apply coordinate transformation to detqdual to map the quadric to a cone
  detqdualoncone := Evaluate(detqdual, Eltseq((v * ChangeRing(QtoCone, CC4))[1]));
  
  //Pull back to P1 x P1 and take the square root there
  ConeCubic := ComputeSquareRootOnCone(detqdualoncone);
 
  //Reverse the coordinate transformation
  cubic := Evaluate(ConeCubic, Eltseq((v * ChangeRing(QtoCone^(-1), CC4))[1]));
  quadric:=(v*ChangeRing(Qnew, CC4) *Transpose(v))[1,1];
  return quadric, cubic
end

function find_delta(thetas)
  CC = parent(thetas[0,0,0,0,0,0,0,0])
  even_chars = even_theta_characteristics(4)
  v0s = []
  for cha in even_chars
    theta = thetas[cha]
    if contains(theta, zero(CC))
      push!(v0s, cha)
    end
  end
  return v0s
end


function reconstruct_curve_g4(thetas)
  v0s = find_delta(thetas)
  nr_of_zeros = length(v0s)
  if nr_of_zeros == 0
    return reconstruct_g4_curve_generic(thetas)
  end
  
   if nr_of_zeros == 1
    return rec_g4_curve_vanishing_theta0(thetas, v0s[1])
  end
  
  if nr_of_zeros == 10
    return reconstruct_g4_hypell(thetas, v0s)
  end
  
  error("Something went wrong. An impossible number of even theta characteristics is zero.")
end


function hard_coded_s1_s2()
output = 
[
    [
        [ [
            [
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 0, 0, 1)
            ],
            [
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ],
        [ [
            [
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0)
            ],
            [
                (1, 0, 1, 1, 1, 0, 0, 1),
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0)
            ],
            [
                (1, 1, 1, 1, 1, 0, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ],
        [ [
            [
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 0, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 1, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 1, 1, 0, 1, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 0, 1, 0, 0, 0, 0),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 0, 1, 0, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ 1, -1, ]
        ] ],
        [ [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 0, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0),
                (1, 1, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 1, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 1, 0, 1, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 1, 1, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 0, 1, 1),
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ 1, -1, ]
        ] ],
        [ [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 0, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (1, 1, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (1, 1, 1, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 1, 0, 1, 1),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (1, 1, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ] ],
        [ [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 0, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (1, 1, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 0, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 0, 1, 1)
            ],
            [
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 0, 0, 1, 1)
            ],
            [
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 1, 1, 0)
            ],
            [
                (1, 0, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ -1, 1, ]
        ] ],
        [ [
            [
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 1, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 1, 0)
            ],
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 1, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 1)
            ],
            [
                (1, 0, 1, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 1, 1, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 1, 0, 1, 0),
                (1, 0, 0, 1, 1, 0, 1, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 0, 0, 0, 0, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 1, 0, 1, 0),
                (1, 1, 0, 1, 1, 0, 1, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 0, 1, 0, 1, 0, 0),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 0, 1, 0, 1, 1, 1)
            ],
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (1, 0, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ],
        [ [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (1, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 1, 1, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 0, 1, 0)
            ],
            [
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 1),
                (1, 1, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 1, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 1, 1)
            ],
            [
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (1, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 0)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 0, 0, 0, 0, 0, 0)
            ],
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 0, 1, 0, 1, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (1, 0, 1, 1, 1, 0, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (1, 1, 0, 0, 0, 0, 0, 0)
            ],
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 0, 1, 0, 1, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (1, 1, 1, 1, 1, 0, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0)
            ],
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ 1, 1, ]
        ] ],
        [ [
            [
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 0)
            ],
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 1, 1, 1, 0, 1, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (1, 1, 0, 0, 0, 0, 0, 0)
            ],
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 0, 1, 0, 1, 1),
                (1, 1, 1, 1, 1, 0, 1, 0),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0)
            ],
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ 1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 0, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 1, 1, 1, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 1, 0)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 1, 1, 1, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 1, 0)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ],
        [ [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 1, 1, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (1, 0, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (1, 1, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 1, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 1, 0, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 0, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 0, 0, 0),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 1, 0, 1, 0),
                (1, 0, 1, 1, 1, 0, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 1, 0, 0, 0, 0, 0),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 1, 1, 0, 1, 0),
                (1, 1, 1, 1, 1, 0, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ],
        [ [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 1, 1, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (1, 0, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 0, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (1, 1, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 1, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ]
    ]
]
return output
end