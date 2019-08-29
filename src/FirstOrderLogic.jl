module FirstOrderLogic

include("types.jl")
include("FOLParser.jl")
using .FOLParser

include("transformations.jl")

export parseTPTP, @fol_str, @tptp_str, simplify, negationNormalForm,
  prenexNormalForm, skolemNormalForm

end # module FirstOrderLogic
