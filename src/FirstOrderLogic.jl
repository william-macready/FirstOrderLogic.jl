module FirstOrderLogic

include("types.jl")
include("transformations.jl")
include("parser.jl")

export Variable, FunctionTerm, PredicateTerm, NegationTerm, AndTerm, OrTerm,
    AQuantifierTerm, EQuantifierTerm,
    parseTPTP, @fol_str, @tptp_str, simplify, negationNormalForm,
    prenexNormalForm, skolemNormalForm

end # module FirstOrderLogic
