@testset "CSAMaxOrd" begin
  
  function sum_of_two_squares(a::fmpz)
    for i=1:Int(root(a,2))
      for j=1:Int(root(a,2))
        if a==i^2+j^2
          return true
        end
      end
    end 
    return false
  end 
  
  Qx,x=PolynomialRing(FlintQQ, "x")
  for b in Hecke.squarefree_up_to(100)[2:end]
    K,a=NumberField(x^2-b)
    O=maximal_order(K);
    cocval=Array{nf_elem,2}(2, 2)
    G=[Hecke.NfToNfMor(K,K,a),Hecke.NfToNfMor(K,K,-a)]
    cocval[1,1]=K(1)
    cocval[1,2]=K(1)
    cocval[2,1]=K(1)
    cocval[2,2]=K(-1)
    A=Hecke.CrossedProductAlgebra(K,G,cocval)
    if Hecke.issplit(A)
      @test sum_of_two_squares(fmpz(b))
    else
      @test !sum_of_two_squares(fmpz(b))
    end
  end
  
  A=Hecke.quaternion_algebra(4,36)
  @test Hecke.issplit(A)
  A=Hecke.quaternion_algebra(-1,-1)
  O=Hecke.AlgAssOrd(A, [A[i] for i=1:4])
  @test Hecke.schur_index_at_real_plc(O)==2

end
