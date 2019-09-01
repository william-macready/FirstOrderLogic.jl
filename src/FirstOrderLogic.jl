module FirstOrderLogic

include("types")
include("transformations.jl")
include("FOLParser.jl")

export Variable, FunctionTerm, PredicateTerm, NegationTerm, AndTerm, OrTerm,
    AQuantifierTerm, EQuantifierTerm,
    parseTPTP, @fol_str, @tptp_str, simplify, negationNormalForm,
    prenexNormalForm, skolemNormalForm

end # module FirstOrderLogic
