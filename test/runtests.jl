using FirstOrderLogic
using Test

@testset "FirstOrderLogic.jl" begin
    # test parser
    @test isa(fol"f(R)", PredicateTerm)
    @test isa(fol"a(X) & b(Y)", AndTerm)
end
