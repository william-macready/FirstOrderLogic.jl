using ParserCombinator

# subset of the grammar at http://www.tptp.org/TPTP/SyntaxBNF.html

spc = Drop(Star(Space()))
@with_pre spc begin
  # useful sundry things
  lowerAlpha, upperAlpha, numeric = p"[a-z]", p"[A-Z]", p"[0-9]"
  alphaNumeric = lowerAlpha | upperAlpha | numeric | p"_"
  lowerWord = lowerAlpha + Star(alphaNumeric) |> x -> string(x...)
  upperWord = upperAlpha + Star(alphaNumeric) |> x -> string(x...)
  integer = PInt32()
  atomicWord = lowerWord
  name = atomicWord | integer

  # logic definitions
  functor = atomicWord > Functor
  constant = functor
  proposition = constant > ConstantTerm
  variable = upperWord > Variable
  fofFunctionTerm = Delayed()
  fofTerm = fofFunctionTerm | variable
  fofArguments = PlusList(fofTerm, E",")
  fofPlainTerm = (functor + P"\s*\(" + fofArguments + P"\s*\)" |> x -> FunctionTerm(x[1],x[2:end])) | proposition
  fofFunctionTerm.matcher = fofPlainTerm
  fofPlainAtomicFormula = fofPlainTerm
  fofAtomicFormula = fofPlainAtomicFormula > x-> PredicateTerm(x.name,x.args)
  vLine = E"|"
  negatedAtomicFormula = E"~" + fofAtomicFormula |> x-> NegationTerm(PredicateTerm(x[1].name, x[1].args))
  dollarWord = P"\s*\$" + lowerWord
  atomicDefinedWord = dollarWord
  atomicSystemWord = P"\s*\$\$" + lowerWord
  definedFunctor = atomicDefinedWord
  definedConstant = definedFunctor
  systemFunctor = atomicSystemWord
  systemConstant = systemFunctor
  untypedAtom = constant | systemConstant
  atom = untypedAtom | definedConstant
  fofTerm = fofFunctionTerm | variable
  fofInfixUnary = (fofTerm + P"\s*!=" + fofTerm |> x -> NegationTerm(equalTerm(x[1],x[2])))

  # CNF formulae
  literal = fofAtomicFormula | negatedAtomicFormula | fofInfixUnary
  disjunction = Delayed()
  disjunction.matcher = literal | (literal + vLine + disjunction)
  cnfFormula = (disjunction | (E"(" + disjunction + E")")) |> x -> OrTerm(x...)

  # FOF formulae
  unaryConnective = E"~"
  nonassocConnective = p"\s*<=>" | p"\s*=>" | p"\s*<=" | p"\s*<~>" | p"\s*~\|" | p"\s*~&"
  fofQuantifier = p"\s*!" | p"\s*\?"
  fofVariableList = PlusList(variable, E",")

  fofUnitaryFormula = Delayed()
  fofUnaryFormula = (unaryConnective + fofUnitaryFormula > x-> NegationTerm(x)) | fofInfixUnary
  fofUnitFormula = fofUnitaryFormula | fofUnaryFormula
  fofQuantifiedFormula = fofQuantifier + P"\s*\[" + fofVariableList + P"\s*\]\s*:" + fofUnitFormula |>
    x -> (x[1]=="!" ? AQuantifierTerm : EQuantifierTerm)(x[2:end]...)
  fofLogicFormula = Delayed()
  fofUnitaryFormula.matcher =  (P"\s*\(" + fofLogicFormula + P"\s*\)\s*") |
    (fofAtomicFormula + spc) | (fofQuantifiedFormula + spc)
  fofOrFormula = fofUnitFormula + vLine + PlusList(fofUnitFormula, vLine) |> x-> OrTerm(x...)
  fofAndFormula = fofUnitFormula + P"\s*&\s*" + PlusList(fofUnitFormula, P"\s*&\s*") |> x-> AndTerm(x...)
  fofBinaryAssoc = fofOrFormula | fofAndFormula
  fofBinaryNonassoc = fofUnitFormula + nonassocConnective + fofUnitFormula |> x-> begin
    if x[2] == "=>"
      OrTerm([NegationTerm(x[1]), x[3]])
    elseif x[2] == "<=>"
      AndTerm([OrTerm([NegationTerm(x[1]), x[3]]), OrTerm([NegationTerm(x[3]), x[1]])])
    elseif x[2] == "<="
      OrTerm([NegationTerm(x[3]), x[1]])
    else
      error("$(x[2]) not implemented")
    end
  end
  fofBinaryFormula = fofBinaryAssoc | fofBinaryNonassoc
  fofLogicFormula.matcher = fofUnitaryFormula | fofBinaryFormula | fofUnaryFormula
  fofFormula = fofLogicFormula

  # TFF: typed formula with FOOL extensions
  infixInequality = P"\s*!="
  definedInfixPred = P"\s*="
  untypedAtom = constant
  typeFunctor = atomicWord
  typeConstant = typeFunctor
  definedType = atomicDefinedWord
  tfxUnitaryFormula = variable
  tffAtomicType = typeConstant | definedType
  tffTypedVariable = variable + P"\s*:" + tffAtomicType |> x -> (assignType(x[1], x[2]); x[1])
  tffVariable = tffTypedVariable | variable
  tffVariableList = PlusList(tffVariable, E",") |> x -> convert(Vector{Variable}, x)
  tffTerm = Delayed()
  tffArguments = PlusList(tffTerm, P"\s*,") |> x -> convert(Vector{typejoin(typeof.(x)...)}, x)
  tffPlainAtomic = (functor + P"\s*\(" + tffArguments + P"\s*\)\s*" |> x -> PredicateTerm(x[1], x[2])) |
      (constant > ConstantTerm)
  tffAtomicFormula = tffPlainAtomic
  tfxUnitaryFormula  = variable
  tffUnitaryFormula = Delayed()
  tffLogicFormula = Delayed()
  tffUnitaryTerm = tffAtomicFormula | variable | (P"\s*\(" + tffLogicFormula + P"\s*\)\s*")
  tffPreunitFormula = Delayed()
  tffPrefixUnary = unaryConnective + tffPreunitFormula > x -> NegationTerm(x)
  tffInfixUnary = tffUnitaryTerm  + infixInequality + tffUnitaryTerm |> x -> NegationTerm(equalTerm(x[1],x[2]))
  tffPreunitFormula.matcher = tffPrefixUnary | tffUnitaryFormula
  tffUnaryFormula = tffPrefixUnary | tffInfixUnary
  tffDefinedInfix = tffUnitaryTerm + definedInfixPred + tffUnitaryTerm |> x -> equalTerm(x[1],x[2])
  tffUnitFormula = tffUnitaryFormula | tffUnaryFormula | tffDefinedInfix
  tffQuantifiedFormula = fofQuantifier + P"\s*\[" + tffVariableList + P"\s*\]\s*:" + tffUnitFormula |>
     x -> (x[1]=="!" ? AQuantifierTerm : EQuantifierTerm)(x[2:end]...)
  tffUnitaryFormula.matcher = tffQuantifiedFormula | tffAtomicFormula | (P"\s*\(" + tffLogicFormula + P"\s*\)\s*") | tfxUnitaryFormula
  tffBinaryNonassoc = tffUnitFormula  + nonassocConnective + tffUnitFormula |> x -> begin
    if x[2] == "=>"
      OrTerm([NegationTerm(x[1]), x[3]])
    elseif x[2] == "<=>"
      AndTerm([OrTerm([NegationTerm(x[1]), x[3]]), OrTerm([NegationTerm(x[3]), x[1]])])
    elseif x[2] == "<="
      OrTerm([NegationTerm(x[3]), x[1]])
    else
      error("$(x[2]) not implemented")
    end
  end
  tffOrFormula = tffUnitFormula + vLine  + PlusList(tffUnitFormula, vLine) |> x -> OrTerm(x...)
  tffAndFormula = tffUnitFormula + P"\s*&"  + PlusList(tffUnitFormula, P"\s*&") |> x -> AndTerm(x...)
  tffBinaryAssoc = tffOrFormula | tffAndFormula

  tffUnitaryType = Delayed()
  tffXprodType = Delayed()
  tffXprodType.matcher = (tffUnitaryType + P"\s*\*" + tffAtomicType |> x -> x) |
    (tffXprodType + P"\s*\*" + tffAtomicType |> x -> [x[1]...,x[2]])
  tffUnitaryType.matcher = tffAtomicType | (P"\s*\(" + tffXprodType + P"\s*\)")
  tffMappingType = tffUnitaryType + P"\s*>" + tffAtomicType |> x -> isa(x[1], AbstractArray) ? [x[1]..., x[2]] : [x[1], x[2]]

  tffTopLevelType = Delayed()
  tffTopLevelType.matcher = tffMappingType | (P"\s*\(" + tffTopLevelType + P"\s*\)") | tffAtomicType

  tffAtomTyping = Delayed()
tffAtomTyping.matcher = (untypedAtom + P"\s*:" + tffTopLevelType |>
                         x -> begin
                         if isa(x[2], AbstractArray)
                         assignType(x[1], x[2]...)
                         else
                         assignType(x[1], x[2])
                         end
                         end) | (P"\s*\(" + tffAtomTyping + P"\s*\)")

  tffBinaryFormula = tffBinaryNonassoc | tffBinaryAssoc
  tffLogicFormula.matcher = tffUnitaryFormula | tffUnaryFormula | tffBinaryFormula | tffDefinedInfix
  tffTerm.matcher = tffLogicFormula
  tffSubtype = untypedAtom + P"\s*<<" + atom
  tffFormula = tffLogicFormula | tffAtomTyping | tffSubtype

  # top level
  formulaRole = e"axiom" | e"hypothesis" | e"definition" | e"assumption" |
    e"lemma" | e"theorem" | e"corollary" | e"conjecture" | e"negated_conjecture" |
    e"plain" | e"fi_domain" | e"fi_functors" | e"fi_predicates" | e"type" |
    e"unknown"
  cnfAnnotated = (P"\s*cnf\(" + name + P"\s*," + formulaRole + P"\s*," + cnfFormula + P"\s*\)\.\s*") |>
    x -> (Symbol(x[1]), x[3])
  fofAnnotated = (P"\s*fof\(" + name + P"\s*," + formulaRole + P"\s*," + fofFormula + P"\s*\)\.\s*") |>
    x -> (Symbol(x[1]), x[2] == "conjecture" ? NegationTerm(x[3]) : x[3])
  tffAnnotated = (P"\s*tff\(" + name + P"\s*," + formulaRole + P"\s*," + tffFormula + P"\s*\)\.\s*") |>
    x -> (Symbol(x[1]),  x[2] == "conjecture" ? NegationTerm(x[3]) : x[3])
  annotatedFormula = cnfAnnotated | fofAnnotated | tffAnnotated

  sqChar = p"([\40-\46\50-\133\135-\176]|[\\]['\\])"
  fileName = E"'" + Plus(sqChar) + E"'"
  includeRule = P"\s*include\(" + fileName + P"\s*\)\.\s*" > string
  commentLine = P"%([ -~])*"
  comment = commentLine
  tptpInput = annotatedFormula | (comment + spc) | includeRule

  tptpFile = Plus(tptpInput)
end


"""
    parseTPTP(io::IO), parseTPTP(fileName::AbstractString)

Read in the TPTP description at the given IO stream
"""
function parseTPTP(io::IO)
  ret = parse_one(read(io, String), tptpFile + Eos())
  close(io)
  ret
end
parseTPTP(fileName::AbstractString) = parseTPTP(open(fileName,"r"))

"""
    @fol_str(s)

Build the data structure representing the first order formula stored in TPTP
format in the string s. Note that \$ should not be escaped inside the fol_str
macro.
"""
macro fol_str(s)
  simplify(parse_one(s, tffFormula+Eos())[1])
end


"""
    @tptp_str(s)

Build the data structure representing the TPTP directive(s) in the string s.
Note that \$ should not be escaped inside the fol_str macro
"""
macro tptp_str(s)
  parse_one(s, tptpFile+Eos())
end
