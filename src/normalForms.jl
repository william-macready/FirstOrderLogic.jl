# mechanism to generate fresh free variables
let
  varCount, funcCount = 0, 0

  global newVar(v::Variable) = Variable(v.name * "###" * string(varCount += 1))
  global newVar(f::Functor) = Functor(f.name * "#sk" * string(funcCount += 1))
  global resetNew() = varCount = funcCount = 0
end

"""
    standardizeVars(s::SententialTerm)

Standardize the names of all quantified variables.
"""
standardizeVars(s::SententialTerm) = standardize_(s, Set{Variable}(), Dict{Variable,Variable})
standardize_(p::PredicateTerm, seen, replacements) =
  PredicateTerm(p.name, [isa(a,Variable) ? get(replacements, a, a) : a for a in p.args])
standardize_(n::NegationTerm, seen, replacements) = NegationTerm(n.scope, replacements)
standardize_(j::JunctionTerm, seen, replacements) = rootType(j)(standardize_.(j.juncts, Ref(seen), Ref(replacements)))
function standardize_(q::QuantifierTerm, seen, replacements)
  newVars = [v ∈ seen ? (@show v; replacements[v] = newVar(v)) : v for v in q.variables]
  rootType(q)(newVars, standardize_(q.scope, union!(seen, newVars), replacements))
end

"""
    simplify(s::SententialTerm)

Simplify the structure of s by removing double negations, aggregating nested
ands/ors and collecting quantified variabes in nested quantifiers

"""
simplify(p::PredicateTerm) = p
simplify(a::J) where {J<:JunctionTerm{<:LiteralTerm}} = a
function simplify(j::JunctionTerm)
  J = rootType(j);  newJuncts = SententialTerm[]
  for c in j.juncts
    cs = simplify(c)
    rootType(cs) == J ? append!(newJuncts, cs.juncts) : push!(newJuncts, cs)
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
    nnf(s::SententialTerm)

Obtain the negation normal form by pushing negations inward.
"""
nnf(p::PredicateTerm)= p
nnf(a::JunctionTerm) = rootType(a)(nnf.(a.juncts))
nnf(q::QuantifierTerm) = rootType(q)(q.variables, nnf(q.scope))
nnf(n::NegationTerm) = nnf_(n.scope)

nnf_(a::OrTerm) = AndTerm(nnf.(NegationTerm.(a.juncts)))
nnf_(a::AndTerm) = OrTerm(nnf.(NegationTerm.(a.juncts)))
nnf_(q::EQuantifierTerm) = AQuantifierTerm(q.variables, nnf(NegationTerm(q.scope)))
nnf_(q::AQuantifierTerm) = EQuantifierTerm(q.variables, nnf(NegationTerm(q.scope)))
nnf_(n::NegationTerm) = nnf(n.scope)
nnf_(p::PredicateTerm) = NegationTerm(p)
