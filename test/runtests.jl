using FirstOrderLogic
using Test

@testset "parser         tests" begin
  # test parser on simple first order formulae
  @test isa(fol"f(R)", PredicateTerm)
  @test isa(fol"~f(R)", NegationTerm)
  @test isa(fol"a(X) & b(Y)", AndTerm)
  @test isa(fol"a(X)|b(Y)", OrTerm)
  @test isa(fol"![X,Y] : a(f(X),Y)", AQuantifierTerm)
  @test isa(fol"?[X,Y,Z] : (a(f(X)) & b(c(Y,Z)))", EQuantifierTerm)
  @test isa(fol"d(Z) & (a(f(X)) & b(c(Y,Z)))", AndTerm)

  # test parser on annotated first order formulae
  @test isa(tptp"fof(union,axiom,
                 ! [X,A,B] :
                 ( member(X,union(A,B))
                 <=> ( member(X,A)
                 | member(X,B) ) ))."[2], AQuantifierTerm)
  @test length(parseTPTP("fofTest.p")) == 7

  # test parser on FOOL formula (with types and Boolean variables reifying formulas)
  @test isa(fol"! [A: animal] : ? [H: human] : H = owner_of(A) ", AQuantifierTerm)
  @test isa(fol" ! [X: $o]: (X | ~X)", AQuantifierTerm)
  @test length(parseTPTP("tffTest.p")) == 4

  # validate the environment created by tffTypeTest.p
  tmp = parseTPTP("tffTypeTest.p")
  en = FirstOrderLogic.e
  @test haskey(en,"A") && haskey(en,"C") && haskey(en,"D") && haskey(en,"H") &&
    haskey(en,"dog") && haskey(en,"cat") && haskey(en,"human") && haskey(en,"animal") &&
    haskey(en,"garfield") && haskey(en,"odie") && haskey(en,"jon") &&
    haskey(en,"chased") && haskey(en,"hates") && haskey(en,"owner_of") &&
    haskey(en,"cat_to_animal") && haskey(en,"dog_to_animal")

  # test the ingested SententialTerms for their type
  wellTyped = Vector{Bool}(undef, 0)
  for s in filter(x->isa(x[2],FirstOrderLogic.SententialTerm), tmp)
    push!(wellTyped, isWellTyped(s[2],FirstOrderLogic.e))
  end
  @test all(wellTyped)
end # parser tests


@testset "transformation tests" begin
  # conversion of FOOL to FOL
  f = parseTPTP("tffTest.p")[end][end]
  fol = FOOL2FOL!(f, FirstOrderLogic.e)
  @test isa(fol, AndTerm)

end # transformation tests
