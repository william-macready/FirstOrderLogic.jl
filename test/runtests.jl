using FirstOrderLogic
using Test

@testset "FirstOrderLogic.jl" begin
    # test parser on first order formulae
    @test isa(fol"f(R)", PredicateTerm)
    @test isa(fol"~f(R)", NegationTerm)
    @test isa(fol"a(X) & b(Y)", AndTerm)
    @test isa(fol"a(X)|b(Y)", OrTerm)
    @test isa(fol"![X,Y] : a(f(X),Y)", AQuantifierTerm)
    @test isa(fol"?[X,Y,Z] : (a(f(X)) & b(c(Y,Z)))", EQuantifierTerm)
    @test isa(fol"d(Z) & (a(f(X)) & b(c(Y,Z)))", AndTerm)
    # test parser on annotated first order formulae
    @test length(parseTPTP("test.p")) == 7
    # test parser on FOOL formula (with types and Boolean variables representing formulas)
    @test isa(fol"! [A: animal] : ? [H: human] : H = owner_of(A) ", AQuantifierTerm)

end
