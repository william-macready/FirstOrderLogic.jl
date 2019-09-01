# mechanism to generate fresh free variable and functor names
let
  varCount, funcCount = 0, 0

  global newVar(v::Variable) = Variable(v.name*"##"*string(varCount += 1))
  global newVar(f::Functor) = Functor(f.name * "#sk" * string(funcCount += 1))
  global newFunc(v::Variable) = Functor(lowercase(v.name)*"#sk"*string(funcCount += 1))
  global newFunc() = Functor("#f#"*string(funcCount += 1))
  global resetNew() = varCount = funcCount = 0
end


const global True = Functor("⊤")
const global False = Functor("⊥")

"""
   FOOL2FOL(a::AbstractLogicTerm)

Convert a FOOL logic expression to first order form. See [``` `A First Class Boolean Sort in First-Order
Theorem Proving and TPTP` ```](https://arxiv.org/pdf/1505.01682.pdf).
"""
function FOOL2FOL(a)
  defs = Vector{PredicateTerm}[]
  ret = f2f!(a, defs)
  newRet = isempty(defs) ? ret : push!(defs, ret)
  AndTerm(convert(Vector{typejoin(typeof.(newRet)...)}, newRet))
end
function f2f!(fp::Union{FunctionTerm,PredicateTerm}, defs) # replace formula in arguments of fp
  newArgs = similar(fp.args)
  for (i,a) in enumerate(fp.args)
    if isa(a, SententialTerm)
      fv, F = freeVar(a), FunctionTerm(newFunc(), fv)
      newArgs[i] = F
      eq = equalTerm(F,True)
      newFormula = AndTerm(OrTerm(Negation(a), eq), OrTerm(Negation(eq), a))
      push!(defs, isempty(fv) ? newFormula : AQuantifier(fv, newFormula))
    else
      newArgs[i] = a
    end
  end
  rootType(fp)(fp.name, newArgs)
end
f2f!(n::NegationTerm, defs) = NegationTerm(f2f!(n.scope, defs))
function f2f!(j::JunctionTerm, defs)
  newJuncts = map(x -> isa(x, Variable) ? equalTerm(x, True) : x, f2f!.(j.juncts, defs))
  rootType(j)(convert(Vector{typejoin(typeof.(newJuncts)...)}, newJuncts))
end
f2f!(q::QuantifierTerm, defs) = rootType(q)(q.variables, f2f!(q.scope, defs))


"""
    pullCommonQuantifiers(s::SententialTerm)

Pull out common quantifiers if possible; this is only useful before variable
renaming.
"""
pullCommonQuantifiers(p::PredicateTerm) = p
pullCommonQuantifiers(n::NegationTerm) = NegationTerm(pullCommonQuantifiers(n.scope))
function pullCommonQuantifiers(j::JunctionTerm)
  newJuncts = pullCommonQuantifiers.(j.juncts)
  QJ = pairedQuantifierType(j)
  if all(rootType.(newJuncts) .== QJ)
    commonVars = reduce((cs,vs) -> intersect(vs,cs), getproperty.(newJuncts[2:end], :variables);
    init = newJuncts[1].variables)
    if ~isempty(commonVars)
      newScope = [begin
                    diffVars = setdiff(j.variables, commonVars)
                    isempty(diffVars) ? j.scope :  QJ(diffVars, j.scope)
                  end for j in newJuncts]
      QJ(commonVars, rootType(j)(newScope))
    else
      rootType(j)(newJuncts...)
    end
  else
    rootType(j)(newJuncts...)
  end
end
pullCommonQuantifiers(q::QuantifierTerm) = rootType(q)(q.variables, pullCommonQuantifiers(q.scope))

"""
    simplify(s::SententialTerm)

Simplify the structure of s by removing double negations, aggregating nested
ands/ors and collecting quantified variabes in nested quantifiers

"""
simplify(p::Union{Variable,PredicateTerm}) = p
simplify(a::J) where {J<:JunctionTerm{<:LiteralTerm}} = a
function simplify(j::JunctionTerm)
  if length(j.juncts) == 1
    j.juncts[1]
  else
    J = rootType(j);  newJuncts = SententialTerm[]
    for c in j.juncts
      cs = simplify(c)
      rootType(cs) == J ? append!(newJuncts, cs.juncts) : push!(newJuncts, cs)
    end
  end
  J(newJuncts...)
end
function simplify(n::NegationTerm)
  ns = simplify(n.scope)
  isa(ns, NegationTerm) ? n′.scope : NegationTerm(ns)
end
function simplify(q::QuantifierTerm)
  Q = rootType(q);  s = simplify(q.scope)
  rootType(s) == Q ? Q(union(q.variables, s.variables), s.scope) : Q(q.variables, s)
end


"""
    negationNormalForm(s::SententialTerm)

Obtain the negation normal form by pushing negations inward.
"""
negationNormalForm(p::PredicateTerm)= p
negationNormalForm(a::JunctionTerm) = rootType(a)(negationNormalForm.(a.juncts))
negationNormalForm(q::QuantifierTerm) = rootType(q)(q.variables, negationNormalForm(q.scope))
negationNormalForm(n::NegationTerm) = nnf_(n.scope)

nnf_(p::PredicateTerm) = NegationTerm(p)
nnf_(n::NegationTerm) = negationNormalForm(n.scope)
nnf_(a::OrTerm) = AndTerm(negationNormalForm.(NegationTerm.(a.juncts)))
nnf_(a::AndTerm) = OrTerm(negationNormalForm.(NegationTerm.(a.juncts)))
nnf_(q::EQuantifierTerm) = AQuantifierTerm(q.variables, negationNormalForm(NegationTerm(q.scope)))
nnf_(q::AQuantifierTerm) = EQuantifierTerm(q.variables, negationNormalForm(NegationTerm(q.scope)))


"""
    renameVars(s::SententialTerm)

Standardize the names of all quantified variables so they are unique.
"""
renameVars(s::SententialTerm) = rename_(s, Set{Variable}(), Dict{Variable,Variable}())
rename_(p::PredicateTerm, seen, replacements) =
  PredicateTerm(p.name, [isa(a,Variable) ? get(replacements, a, a) : a for a in p.args])
rename_(n::NegationTerm, seen, replacements) = NegationTerm(rename_(n.scope, seen, replacements))
rename_(j::JunctionTerm, seen, replacements) = rootType(j)(rename_.(j.juncts, Ref(seen), Ref(replacements)))
function rename_(q::QuantifierTerm, seen, replacements)
  newVars = [v ∈ seen ? replacements[v] = newVar(v) : v for v in q.variables]
  rootType(q)(newVars, rename_(q.scope, union!(seen, Set(newVars)), replacements))
end


"""
   pullQuantifiers(s::SententialTerm)

Pull quantifiers outwards assuming that s has had it's variables standardized.
"""
pullQuantifiers(p::PredicateTerm) = p
pullQuantifiers(n::NegationTerm) = NegationTerm(pullQuantifiers(n.scope))
function pullQuantifiers(j::JunctionTerm)
  function pullThroughJunction(js, J) # pull quantifiers through junction J
    es, as = isa.(js, EQuantifierTerm), isa.(js, AQuantifierTerm)
    if any(es)  # pull existential quantifiers first to simplify Skolemization
      EVars = collect(Iterators.flatten(getproperty.(js[es], :variables)))
      scope = map((e,j) -> e ? j.scope : j, es, js)
      EQuantifierTerm(EVars, pullThroughJunction(scope, J))
    elseif any(as)
      AVars = collect(Iterators.flatten(getproperty.(js[as], :variables)))
      scope = map((a,j) -> a ? j.scope : j, as, js)
      AQuantifierTerm(AVars, pullThroughJunction(scope, J))
    else
      J(js)
    end
  end
  pullThroughJunction(pullQuantifiers.(j.juncts), rootType(j))
end
pullQuantifiers(q::QuantifierTerm) = rootType(q)(q.variables, pullQuantifiers(q.scope))


"""
    skolemize(s::SententialTerm)

Remove all existential quantifiers from s (which is assumed to be in
prenex normal form) by Skolemization
"""
skolemize(s::SententialTerm) = skolemize_(s, Dict{Variable,FunctionTerm}(), Variable[])
skolemize_(v::Variable, replacements, _) = get(replacements, v, v)
skolemize_(fp::Union{FunctionTerm,PredicateTerm}, replacements, previousAVars) =
  rootType(fp)(fp.name, skolemize_.(fp.args, Ref(replacements), Ref(previousAVars)))
skolemize_(n::NegationTerm, replacements, previousAVars) =
  NegationTerm(skolemize_(n.scope, replacements, previousAVars))
skolemize_(j::JunctionTerm, replacements, previousAVars) =
  rootType(j)(skolemize_.(j.juncts, Ref(replacements), Ref(previousAVars)))
skolemize_(a::AQuantifierTerm, replacements, previousAVars) =
  AQuantifierTerm(a.variables, skolemize_(a.scope, replacements, append!(previousAVars, a.variables)))
function skolemize_(e::EQuantifierTerm, replacements, previousAVars)
  setindex!.(Ref(replacements), FunctionTerm.(newFunc.(e.variables), Ref(previousAVars)), e.variables)
  skolemize_(e.scope, replacements, previousAVars)
end


"""
    prenexNormalForm(s::SententialTerm)

Convert s to prenex normal form.
"""
prenexNormalForm(s) = s |> negationNormalForm |> pullCommonQuantifiers |> renameVars |> pullQuantifiers |> distributeOrOverAnd


"""
    skolemNormalForm(s::SententialTerm)

Return Skolem normal form of s
"""
skolemNormalForm(s::SententialTerm) = s |> prenexNormalForm |> skolemize


"""
    stripQuantifiers(s::SententialTerm)

Remove all quantifiers from sentence s. This is useful when constructing the
universally quantified conjunction normal form.
"""
stripQuantifiers(p::PredicateTerm) = p
stripQUantifiers(n::NegationTerm) = NegationTerm(stripQuantifiers(n.scope))
stripQuantifiers(j::JunctionTerm) = rootType(j)(stripQuantifiers.(j.juncts))
stripQuantifiers(q::QuantifierTerm) = stripQuantifiers.(q.scope)


"""
    flatten(ls)

Utility to flatten a list of lists into a list.
"""
flatList(ls) = collect(Iterators.flatten(ls))

using IterTools

"""
    distributeOrOverAnd(s::SententialTerm)

Distribute ∨ over ∧ assuming we are in prenex normal form. This is used when
converting a sentence to clausal form.
"""
distributeOrOverAnd(l::LiteralTerm) = AndTerm(OrTerm([l]))
function distributeOrOverAnd(a::AndTerm)
  orTerms = mapreduce(j->distributeOrOverAnd(j).juncts, vcat, a.juncts; init=OrTerm[])
  AndTerm(orTerms)
end
function distributeOrOverAnd(o::OrTerm)
  clauseLiterals = reduce(o.juncts; init=Vector{Vector{LiteralTerm}}[]) do l,j
    jJuncts = getproperty.(distributeOrOverAnd(j).juncts, :juncts)
    push!(l, jJuncts)
  end
  clauses = [OrTerm(flatList(c)) for c in IterTools.ivec(Iterators.product(clauseLiterals...))]
  AndTerm(clauses)
end
distributeOrOverAnd(q::QuantifierTerm) = rootType(q)(q.variables, distributeOrOverAnd(q.scope))
