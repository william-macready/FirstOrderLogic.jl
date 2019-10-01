module FirstOrderLogic


include("types.jl")
include("Environment.jl")
using .Environment

include("transformations.jl")
include("parser.jl")
include("typeCheck.jl")

export Variable, FunctionTerm, PredicateTerm, NegationTerm, AndTerm, OrTerm,
  AQuantifierTerm, EQuantifierTerm,
  resetEnv!, isWellTyped,
  parseTPTP, @fol_str, @tptp_str, simplify, negationNormalForm,
  prenexNormalForm, skolemNormalForm

end # module FirstOrderLogic
