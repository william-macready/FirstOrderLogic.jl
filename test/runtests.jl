using FirstOrderLogic
using Test

@testset "FirstOrderLogic.jl" begin
   isa(fol"f(R)", PredicateTerm)
end
