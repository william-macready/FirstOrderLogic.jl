import Base: show, string, typejoin

abstract type AbstractLogicTerm end
abstract type SententialTerm{T<:AbstractLogicTerm} <: AbstractLogicTerm end
abstract type JunctionTerm{T<:AbstractLogicTerm} <: SententialTerm{T} end
abstract type QuantifierTerm{T<:AbstractLogicTerm} <: SententialTerm{T} end

# we make Variable <: SententialTerm to enable FOOL extensions
struct Variable <: SententialTerm{AbstractLogicTerm}
  name::String
end
Variable(name::AbstractString) = Variable(name)
Variable(v::Variable) = Variable(v.name)
Variable(name::AbstractString, t::Symbol) = Variable(name)
Variable(v::Variable, t::Symbol) = Variable(v.name)
string(v::Variable) = v.name

struct Functor <: AbstractLogicTerm
  name::String
end
string(f::Functor) = f.name

show(io::IO, q::AbstractLogicTerm) = print(io, string(q))

struct FunctionTerm <: AbstractLogicTerm
  name::Functor
  args::Vector{Union{FunctionTerm, Variable}}
end
FunctionTerm(n::AbstractString, args) = FunctionTerm(Functor(string(n)), args)
ConstantTerm(n::Functor) = FunctionTerm(n, Variable[])
ConstantTerm(n) = FunctionTerm(Functor(string(n)), Variable[])

function listString(xs::AbstractVector, head::AbstractString, sep::AbstractString, tail::AbstractString)
  foldl((x,y) -> x*sep*string(y), xs[2:end]; init=head*string(xs[1]))*tail
end

struct PredicateTerm{T<:AbstractLogicTerm} <: SententialTerm{T}
  name::Functor
  args::Vector{T}
end
PredicateTerm(n::String, args) = (println("im here $n $(typeof(args))"); r = PredicateTerm(Functor(n), args); @show r; r)

function equalTerm(t1::Union{PredicateTerm,FunctionTerm,Variable},
                   t2::Union{PredicateTerm,FunctionTerm,Variable})
  PredicateTerm(Functor("="), [t1,t2])
end

string(f::Union{FunctionTerm,PredicateTerm}) =
  isempty(f.args) ? string(f.name) : listString(f.args, string(f.name)*"(", ",", ")")

struct NegationTerm{T<:AbstractLogicTerm} <: SententialTerm{T}
  scope::T
end
string(n::NegationTerm) = "¬(" * string(n.scope) * ")"

const LiteralTerm = Union{PredicateTerm,NegationTerm{PredicateTerm}}

Base.typejoin(::Type{PredicateTerm},::Type{NegationTerm{PredicateTerm}}) = LiteralTerm

struct AndTerm{T<:AbstractLogicTerm} <: JunctionTerm{T}
  juncts::Vector{T}
end
AndTerm(s::T, ss...) where {T<:SententialTerm} =
  AndTerm{foldr((si,T)->typejoin(T,typeof(si)), ss; init=T)}([s; collect(ss)])
string(a::AndTerm) = listString(a.juncts, "(", ")∧(", ")")

struct OrTerm{T<:AbstractLogicTerm} <: JunctionTerm{T}
  juncts::Vector{T}
end
OrTerm(s::T, ss...) where {T<:SententialTerm} =
  OrTerm{foldr((si,T)->typejoin(T,typeof(si)), ss; init=T)}([s; collect(ss)])
string(a::OrTerm) = listString(a.juncts, "(", ")∨(", ")")

struct EQuantifierTerm{T<:AbstractLogicTerm} <: QuantifierTerm{T}
  variables::Vector{Variable}
  scope::T
end
function EQuantifierTerm(args...)
  x = collect(args);  EQuantifierTerm{typeof(x[end])}(x[1:end-1], x[end])
end
string(q::EQuantifierTerm) = "∃" * listString(q.variables, "", ",", "") * " " * string(q.scope)

struct AQuantifierTerm{T<:AbstractLogicTerm} <: QuantifierTerm{T}
  variables::Vector{Variable}
  scope::T
end
function AQuantifierTerm(args...)
  x = collect(args);  AQuantifierTerm{typeof(x[end])}(x[1:end-1], x[end])
end
string(q::AQuantifierTerm) = "∀" * listString(q.variables, "", ",", "") * " " * string(q.scope)


for T in (Variable,FunctionTerm,PredicateTerm,NegationTerm,AndTerm,OrTerm,AQuantifierTerm,EQuantifierTerm)
  @eval rootType(_::$T) = $T
end

pairedQuantifierType(_::AndTerm) = AQuantifierTerm
pairedQuantifierType(_::OrTerm) = EQuantifierTerm


"""
    freeVar(a::AbstractLogicTerm)

Return a Vector{Variable} of the free variables in a.
"""
freeVar(v::Variable) = [v]
freeVar(fp::Union{FunctionTerm,PredicateTerm}) = foldl((u,x) -> union!(u, freeVar(x)), fp.args; init=Variable[])
freeVar(n::NegationTerm) = freeVar(n.scope)
freeVar(j::JunctionTerm) = foldl((u,x) -> union!(u, freeVar(x)), j.juncts; init=Variable[])
freeVar(q::QuantifierTerm) = (vs =freeVar(q.scope); vq = q.variables; @show vs[1].type, vq[1].type, setdiff(vs,vq); setdiff(freeVar(q.scope), q.variables))

let
  # an assignment is a mapping from Variables and Functors to types
  # we also allow mapping from String to types to define type synonyms
  assignments = Dict{Union{Variable,Functor,String},Tuple{Vararg{String}}}()
  global assignType(k, vs::String...) = assignments[k] = vs
  global assignType(k, vs::Tuple{Vararg{String}}) = assignments[k] = vs
  global function showAssignment()
    for (k,v) in assignments
      typeString = if length(v) == 1
        v[1]
      elseif length(v) == 2
        v[1] * " -> " * v[end]
      else
        str = "("
        for t in v[1:end-2]
          str *= t * ", "
        end
        str * v[end-1] * ") -> " * v[end]
      end
      println("$k: $typeString")
    end
  end
  global typeOf(k) = assignments[k]
end
