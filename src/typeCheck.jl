"""
    outputType(s, e::Env)

Determine the output type for the sentential term `s` in the environment `e`
containing the type information. If `s` is not properly typed return nothing.
"""
outputType(s::Variable, e::Env) = get(e.userTypes, s.name, nothing)[1]
function outputType(s::Union{FunctionTerm,PredicateTerm}, e::Env)
  if isa(s, PredicateTerm) &&s.name.name == "=" # treat equality PredicateTerm
    oTypes = outputType.(s.args, Ref(e))
    all(oTypes .== Ref(oTypes[1])) ? BoolType() : nothing
  else
    if haskey(e, s)
      ts = e[s]    # the type of s
      if length(ts) == length(s.args)+1 && all(outputType.(s.args, Ref(e)) .== ts[1:end-1])
        ts[end]    # args are well-typed so return the output type
      else
        nothing    # args are not well-typed so return nothing
      end
    else           # can't find type in environment
      nothing
    end
  end
end
outputType(s::Union{NegationTerm,QuantifierTerm}, e::Env) =
  outputType(s.scope, e) == BoolType() ? BoolType() : nothing
outputType(j::JunctionTerm, e::Env) =
  all(outputType.(j.juncts, Ref(e)) .== Ref(BoolType())) ? BoolType() : nothing


"""
    isWellTyped(s, e::Env)

`true/false` depending on whether `s` is well-typed/ill-typed in environment
`e`.
"""
isWellTyped(s::SententialTerm, e::Env) = outputType(s, e) == BoolType()
isWellTyped(f::FunctionTerm, e::Env) =
  haskey(e,f) ? outputType(f, e) == e[f][end] : false
