const global True  = ConstantTerm("⊤")
const global False = ConstantTerm("⊥")


"""
   FOOL2FOL!(a::AbstractLogicTerm, e::Env)

Convert a FOOL logic expression with associated Environment `e` to first order form. This
may modify the environment by introducing new typed `FunctionTerm`s. See [A First Class
Boolean Sort in First-Order Theorem Proving and TPTP](https://arxiv.org/pdf/1505.01682.pdf)
for details.
"""
function FOOL2FOL!(a, e=Env())
  # f2f! replaces all FOOL formula with FOL formula and adds new terms
  function f2f!(fp::Union{FunctionTerm,PredicateTerm}, defs, e::Env, boolContext)
    newArgs = similar(fp.args, Union{Variable,FunctionTerm})
    for (i,a) in enumerate(fp.args)
      a = f2f!(a, defs, e, false)  # recursively apply f2f!
      if typeof(a) <: Union{PredicateTerm,JunctionTerm,QuantifierTerm,NegationTerm}
        fv = freeVar(a)
        F = FunctionTerm(newFunctor(e), fv);  newArgs[i] = F
        eq = equalTerm(F, True)
        ts = getindex.(Ref(e), getproperty.(fv, :name))  # get argument types
        e[F.name.name] = tuple(getindex.(ts,1)..., BoolType())
        newFormula = AndTerm(OrTerm(NegationTerm(a), eq), OrTerm(NegationTerm(eq), a))
        push!(defs, isempty(fv) ? newFormula : AQuantifierTerm(fv, newFormula))
      else
        newArgs[i] = a
      end
    end
    rootType(fp)(fp.name, newArgs)
  end
  f2f!(n::NegationTerm, defs, e::Env, boolContext) = NegationTerm(f2f!(n.scope, defs, e, true))
  function f2f!(j::JunctionTerm, defs, e::Env, boolContext)
    newJuncts = map(x -> isa(x, Variable) ? equalTerm(x, True) : x, f2f!.(j.juncts, Ref(defs), Ref(e), true))
    rootType(j)(convert(Vector{typejoin(typeof.(newJuncts)...)}, newJuncts))
  end
  f2f!(q::QuantifierTerm, defs, e::Env, boolContext) = rootType(q)(q.variables, f2f!(q.scope, defs, e, true))
  f2f!(v::Variable, defs, e::Env, boolContext) = boolContext ? equalTerm(v, True) : v

  defs = Vector{SententialTerm}(undef, 0)
  ret = f2f!(a, defs, e, true)
  if isempty(defs)
    ret
  else
    push!(defs, ret)
    e[True.name.name] = BoolType();  e[False.name.name] = BoolType()
    AndTerm(convert(Vector{typejoin(typeof.(defs)...)}, defs))
  end
end


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
  isa(ns, NegationTerm) ? ns.scope : NegationTerm(ns)
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
function negationNormalForm(n::NegationTerm)
  nnf(p::PredicateTerm) = NegationTerm(p)
  nnf(n::NegationTerm) = negationNormalForm(n.scope)
  nnf(a::OrTerm) = AndTerm(negationNormalForm.(NegationTerm.(a.juncts)))
  nnf(a::AndTerm) = OrTerm(negationNormalForm.(NegationTerm.(a.juncts)))
  nnf(q::EQuantifierTerm) = AQuantifierTerm(q.variables, negationNormalForm(NegationTerm(q.scope)))
  nnf(q::AQuantifierTerm) = EQuantifierTerm(q.variables, negationNormalForm(NegationTerm(q.scope)))

  nnf(n.scope)
end


"""
    renameVars(s::SententialTerm, e=Env())

Standardize the names of all quantified variables so they are unique. Use new variable names
drawn from the environment `e`.
"""
function renameVars(s::SententialTerm, e=Env())
  rename_(p::PredicateTerm, seen, replacements) =
    PredicateTerm(p.name, [isa(a,Variable) ? get(replacements, a, a) : a for a in p.args])
  rename_(n::NegationTerm, seen, replacements) = NegationTerm(rename_(n.scope, seen, replacements))
  rename_(j::JunctionTerm, seen, replacements) = rootType(j)(rename_.(j.juncts, Ref(seen), Ref(replacements)))
  function rename_(q::QuantifierTerm, seen, replacements)
    newVars = [v ∈ seen ? replacements[v] = newVariable(v, e) : v for v in q.variables]
    rootType(q)(newVars, rename_(q.scope, union!(seen, Set(newVars)), replacements))
  end

  rename_(s, Set{Variable}(), Dict{Variable,Variable}())
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
    skolemize(s::SententialTerm, e=Env())

Remove all existential quantifiers from `s` (which is assumed to be in prenex normal form)
by Skolemization. We use the environment `e` to define new variables/functors.
"""
function skolemize(s::SententialTerm, e=Env())
  skolemize_(v::Variable, replacements, _) = get(replacements, v, v)
  skolemize_(fp::Union{FunctionTerm,PredicateTerm}, replacements, previousAVars) =
    rootType(fp)(fp.name, skolemize_.(fp.args, Ref(replacements), Ref(previousAVars)))
  skolemize_(n::NegationTerm, replacements, previousAVars) =
    NegationTerm(skolemize_(n.scope, replacements, previousAVars))
  skolemize_(j::JunctionTerm, replacements, previousAVars) =
    rootType(j)(skolemize_.(j.juncts, Ref(replacements), Ref(previousAVars)))
  skolemize_(a::AQuantifierTerm, replacements, previousAVars) =
    AQuantifierTerm(a.variables, skolemize_(a.scope, replacements, append!(previousAVars, a.variables)))
  function skolemize_(eq::EQuantifierTerm, replacements, previousAVars)
    setindex!.(Ref(replacements), FunctionTerm.(newFunctor.(eq.variables, e), Ref(previousAVars)), eq.variables)
    skolemize_(e.scope, replacements, previousAVars)
  end

  skolemize_(s, Dict{Variable,FunctionTerm}(), Variable[])
end


"""
    flatten(ls)

Utility to flatten a list of lists into a list.
"""
flatList(ls) = collect(Iterators.flatten(ls))


using IterTools


"""
    distributeOrOverAnd(s::SententialTerm)

Distribute ∨ over ∧ assuming we are in prenex normal form. This is used when
converting a sentence `s` to clausal form.
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


"""
    prenexNormalForm(s::SententialTerm, e=Env())

Convert `s` to prenex normal form. Use the environment `e` to define new variables/functors.
"""
prenexNormalForm(s, e=Env()) = s |> negationNormalForm |> pullCommonQuantifiers |>
  Base.Fix2(renameVars, e) |> pullQuantifiers |> distributeOrOverAnd |> simplify


"""
    skolemNormalForm(s::SententialTerm, e=Env())

Return the Skolem normal form of `s` using the environment `e` to define new
variables/functors. The result is in CNF form.
"""
skolemNormalForm(s::SententialTerm, e=Env()) = s |> Base.Fix2(prenexNormalForm, e) |> skolemize |> simplify


"""
    stripQuantifiers(s::SententialTerm)

Remove all quantifiers from sentence s. This is useful when constructing the
universally quantified conjunction normal form.
"""
stripQuantifiers(p::PredicateTerm) = p
stripQUantifiers(n::NegationTerm) = NegationTerm(stripQuantifiers(n.scope))
stripQuantifiers(j::JunctionTerm) = rootType(j)(stripQuantifiers.(j.juncts))
stripQuantifiers(q::QuantifierTerm) = stripQuantifiers.(q.scope)
