"""
    Environment

Module pertinent to a sentential formula including mutable state (for new
variables and functors) and type information.
"""
module Environment

export BoolType, IntType, RationalType, RealType, Env, resetEnv!, userTypes,
  newVariable, newFunctor

import Base: length, show, haskey, setindex!, getindex
import FirstOrderLogic: Variable, Functor, FunctionTerm, PredicateTerm


abstract type PrimitiveType end

# the allowed logic types
struct InputType <: PrimitiveType end
show(io::IO, _::InputType) = print(io, "\$i")
struct BoolType <: PrimitiveType end
show(io::IO, _::BoolType) = print(io, "\$o")
struct IntType <: PrimitiveType  # we optionally allow an upper bound
  maxVal::Int
  IntType(d=0) = new(d)    # default to unbounded (indicated by 0)
end
show(io::IO, t::IntType) = t.maxVal>0 ? print(io, "\$int($(t.maxVal))") : print(io, "\$int")
struct RationalType <: PrimitiveType end
show(io::IO, _::RationalType) = print(io, "\$rat")
struct RealType <: PrimitiveType end
# user-defined types are composites of primitive types; function types are
# represented with the last tuple element determining the output and the
# other elements representing the inputs
show(io::IO, _::RealType) = print(io, "\$real")
struct UserType <: PrimitiveType end
show(io::IO, _::UserType) = print(io, "\$tType")


"""
    PrimitiveType(str)

Build a primitive logic type (\$i,\$o,\$int,\$rat,\$real,\$tType) based on the
strings representing TPTP types: `str`. `str` may be i, o, int, rat, real.
"""
function PrimitiveType(s::AbstractString)
  if s == "\$i"
    InputType()
  elseif s == "\$o"
    BoolType()
  elseif s == "\$int"
    IntType()
  elseif s == "\$rat"
    RationalType()
  elseif s == "\$real"
    RealType()
  elseif s == "\$tType"
    UserType()
  else
    s
  end
end
const CompositeType = Tuple{Vararg{Union{String,PrimitiveType}}}


"""
    Environment

Struct representing and environment associated with a TPTP
description. Environments include type information and mutable state used to
generate fresh variables and functors.
"""
mutable struct Env
  varCount::Int                         # unique variable id
  funcCount::Int                        # unique functor id
  userTypes::Dict{String,CompositeType} # user-defined type definitions
end
Env() = Env(0, 0, Dict{String,CompositeType}())


"""
    length(e::Env)

The number of defined symbols in the environment `e`
"""
length(e::Env) = length(e.userTypes)


"""
    resetEnv!(e::Env)

Reset the state and types in an environment `e`.
"""
function resetEnv!(e::Env)
  e.varCount = e.funcCount = 0
  e.userTypes = Dict{String,CompositeType}()
  e
end


"""
    setindex!(e::Env, v, k)

Record the user type identified by key `k` and type `v` in the environment
`e`. `v` may be a `CompositeType`, a `String` or `Vector{String}` which are
converted to `CompositeType`.
"""
setindex!(e::Env, v::Union{PrimitiveType,String}, k) = setindex!(e.userTypes, (v,), k)
setindex!(e::Env, v::CompositeType, k) = setindex!(e.userTypes, v, k)
setindex!(e::Env, v::AbstractString, k) = setindex!(e.userTypes, (PrimitiveType(v),), k)
function setindex!(e::Env, v::Vector{T}, k) where {T<:AbstractString}
  setindex!(e.userTypes, tuple(PrimitiveType.(v)...), k)
end


"""
    getindex(e::Env, k)

Get the type associated with key `k`.
"""
getindex(e::Env, fv::Union{Functor,Variable}) = getindex(e.userTypes, fv.name)
getindex(e::Env, fp::Union{FunctionTerm,PredicateTerm}) = getindex(e, fp.name)
getindex(e::Env, s::AbstractString) = getindex(e.userTypes,s)


haskey(e::Env, fv::Union{Functor,Variable}) = haskey(e.userTypes, fv.name)
haskey(e::Env, fp::Union{FunctionTerm,PredicateTerm}) = haskey(e, fp.name)
haskey(e::Env, s::AbstractString) = haskey(e.userTypes, s)


"""
    userTypes(e::Env)

Return the user types in the environment `e`.
"""
userTypes(e::Env) = e.userTypes


"""
    newVariable(vf, e::Env)

Create a fresh variable whose name is based on `vf` (either a `Variable` or
`Functor`) in the environment e.
"""
newVariable(v::Variable, e::Env) = Variable(v.name*"##"*string(e.varCount += 1))
newVariable(f::Functor, e::Env) = Functor(f.name * "#sk" * string(e.funcCount += 1))


"""
    newFunctor(v, e::Env), newFunctor(e::Env)

Create a fresh `Functor` whose name is based on `Variable` `vf` or using a
standard name in the environment e.
"""
newFunctor(v::Variable, e::Env) = Functor(lowercase(v.name)*"#sk"*string(e.funcCount += 1))
newFunctor(e::Env) = Functor("#f#"*string(e.funcCount += 1))

end # module Environment
