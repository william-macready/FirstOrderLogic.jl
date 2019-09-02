module FirstOrderLogic

include("types.jl")
include("transformations.jl")
include("FOLParser.jl")

export Variable, FunctionTerm, PredicateTerm, NegationTerm, AndTerm, OrTerm,
    AQuantifierTerm, EQuantifierTerm,
    parseTPTP, @fol_str, @tptp_str, simplify, negationNormalForm,
    prenexNormalForm, skolemNormalForm

end # module FirstOrderLogic

#CODECOV_TOKEN="6737030d-0fee-4682-81d7-13552a275301"
