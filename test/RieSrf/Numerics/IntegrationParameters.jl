@testset "IntegrationParameters" begin
  @testset "Integration parameters and lazy construction" begin
    f = FAST_CURVES[5][2]                                 # f2, genus 2
    RS = _rs(f, 100)

    # construction is cheap: nothing expensive has been computed yet
    @test !isdefined(RS, :computational)                 # not even the model choice
    @test !isdefined(RSM.original_model(RS), :big_period_matrix)
    @test !isdefined(RSM.original_model(RS), :basis_of_differentials)
    @test RSM.resolved_integration_parameters(RS) === nothing
    @test occursin("Riemann surface", sprint(show, RS))  # show does not force the genus

    # defaults, keywords, parameters object (keywords override it)
    P = RSM.integration_parameters(RS)
    @test P.integration_method == "heuristic"
    @test P.int_style == "Mixed"
    @test P.midpoint_precision === :auto
    @test P.adaptive
    @test RSM.IntegrationParameters().superelliptic       # the default
    Q = RSM.IntegrationParameters(int_style = "GL", midpoint_precision = 100)
    RSq = RSM.riemann_surface(f, 100; parameters = Q, adaptive = false)
    Pq = RSM.integration_parameters(RSq)
    @test Pq.int_style == "GL" && Pq.midpoint_precision == 100 && !Pq.adaptive
    Pq.int_style = "DE"                                   # a copy is returned
    @test RSM.integration_parameters(RSq).int_style == "GL"

    # invalid values are refused
    @test_throws ArgumentError RSM.IntegrationParameters(int_style = "Simpson")
    @test_throws ArgumentError RSM.IntegrationParameters(integration_method = "exact")
    @test_throws ArgumentError RSM.IntegrationParameters(midpoint_precision = -1)
    @test_throws ArgumentError _rs(f, 100; chunk_len = 0)

    # changing is allowed before the computation, refused afterwards
    RSM.set_integration_parameters!(RS; midpoint_precision = 0, group_cost = 2)
    @test RSM.integration_parameters(RS).group_cost == 2.0
    @test_throws ArgumentError RSM.set_integration_parameters!(RS; no_such_parameter = 1)
    RSM.big_period_matrix(RS)
    R = RSM.resolved_integration_parameters(RS)
    @test R !== nothing && R.midpoint_precision == 0 && R.group_cost == 2.0
    @test_throws ArgumentError RSM.set_integration_parameters!(RS; adaptive = false)

    # precision management: target T >= prec + 10, retry switch
    @test RSM.IntegrationParameters().precision_retry     # the default
    C = RSM.computational_model(RS)
    @test C.target_precision >= 100 + 10
    @test C.computational_precision >= C.target_precision + 32
    @test C.precision_retries in (0, 1)
    @test RSM.IntegrationParameters().accuracy === :both   # the default
    @test_throws ArgumentError RSM.IntegrationParameters(accuracy = :tau)
    for acc in (:small, :big)
      RSb = _computed(_rs(f, 100; accuracy = acc))
      @test RSM.resolved_integration_parameters(RSb).accuracy === acc
      P = RSM.big_period_matrix(RSb)
      acc === :big && @test RSM._claimed_bits(P) >= 100
      acc === :small && @test RSM._claimed_bits(RSM.small_period_matrix(RSb)) >= 100
      test_same_result(RS, RSb)
    end
    RSn = _computed(_rs(f, 100; precision_retry = false))
    @test !RSM.resolved_integration_parameters(RSn).precision_retry
    @test RSM.computational_model(RSn).precision_retries == 0
    test_same_result(RS, RSn)
    # direct loop around infinity (off by default): agrees with the composed one
    @test !RSM.IntegrationParameters().direct_infinity
    @test C.infinity_check == 0
    RSd = _computed(_rs(f, 100; direct_infinity = true))
    @test RSM.computational_model(RSd).infinity_check == 1
    test_same_result(RS, RSd)

    # :auto is replaced by a concrete value, the user's setting stays :auto
    RSa = _computed(_rs(f, 100))
    @test RSM.resolved_integration_parameters(RSa).midpoint_precision isa Int
    @test RSM.integration_parameters(RSa).midpoint_precision === :auto

    # with_integration_parameters: a new, uncomputed surface; same bases, same result
    RS2 = RSM.with_integration_parameters(RS; adaptive = false)
    @test RS2 !== RS
    @test RSM.resolved_integration_parameters(RS2) === nothing
    test_same_result(RS, RS2)

    # lazily computed data through the accessors
    RS3 = _rs(f, 100)
    @test RSM.genus(RS3) == 2
    C3 = RSM.computational_model(RS3)
    @test !isdefined(C3, :big_period_matrix)              # the genus needs no periods
    @test RSM.critical_points(RS3) isa Vector             # special points only need the monodromy
    @test !isdefined(RSM.original_model(RS3), :big_period_matrix)
    test_sanity(_computed(RS3); expected_genus = 2)       # periods after the monodromy
  end
end
