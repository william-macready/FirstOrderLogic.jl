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
    @test isa((tptp"fof(union,axiom,
               ! [X,A,B] :
               ( member(X,union(A,B))
               <=> ( member(X,A)
               | member(X,B) ) ))."[2], AQuantifierTerm)

    @test length(parseTPTP("fofTest.p")) == 7
    # test parser on FOOL formula (with types and Boolean variables reifying formulas)
    @test isa(fol"! [A: animal] : ? [H: human] : H = owner_of(A) ", AQuantifierTerm)
    @test isa(fol" ! [X: $o]: (X | ~X)", AQuantifierTerm
    @test length(tptp"tff(imply_defn,axiom,
       ! [X: $o,Y: $o]: (imply(X,Y) <=> (~X | Y)) ).") == 2
    @test length(parseTPTP("../test/tffTest.p")) == 4
end
