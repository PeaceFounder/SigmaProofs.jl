module Serializer

using CryptoGroups.Utils: @check
using CryptoPRG: HashSpec
using ..Parser: Tree, encode
using ..SigmaProofs: Simulator, Verifier, Proposition, Proof, proof_type
using InteractiveUtils: subtypes

global DEFAULT_VERIFIER::Type{<:Verifier} 

abstract type Path end

#Base.write(path::Path, data::Tree) = Base.write(path, encode(data))
#Base.write(path::Path, data::String) = Base.write(path, Vector{UInt8}(data))

_encode(x::Tree) = encode(x)
_encode(x::AbstractString) = Vector{UInt8}(x)
_encode(x::Vector{UInt8}) = x

Base.write(path::Path, data) = Base.write(path, _encode(data))


struct LocalPath <: Path
    path::String
end

Base.joinpath(path::LocalPath, args...) = LocalPath(joinpath(path.path, args...))
Base.write(path::LocalPath, data::Vector{UInt8}) = write(path.path, data)
Base.read(path::LocalPath) = read(path.path)
Base.mkdir(path::LocalPath) = mkdir(path.path)
Base.mkpath(path::LocalPath) = mkpath(path.path)
Base.isfile(path::LocalPath) = isfile(path.path)


struct PathHasher <: Path
    path::String
    hasher::HashSpec
    digests::Vector{Pair{String, Vector{UInt8}}}
end

PathHasher(hasher::HashSpec) = PathHasher("", hasher, [])

Base.joinpath(path::PathHasher, args...) = PathHasher(joinpath(path.path, args...), path.hasher, path.digests)
Base.write(path::PathHasher, data::Vector{UInt8}) = (push!(path.digests, path.path => path.hasher(data)); path)
Base.mkdir(path::PathHasher) = nothing
Base.mkpath(path::PathHasher) = nothing


load(type::Type, dir::String; kwargs...) = load(type, LocalPath(dir); kwargs...)

save(obj, dir::String) = save(obj, LocalPath(dir))


save(obj::Proof, ::Type{<:Proposition}, path::Path) = save(obj, path)

function save(obj::Simulator{P}, path::Path) where P <: Proposition

    save(obj.proposition, path)

    mkdir(joinpath(path, "nizkp"))
    save(obj.proof, P, joinpath(path, "nizkp"))

    verifier_path = joinpath(path, treespec(obj.verifier))
    save(obj.verifier, verifier_path; name = string(nameof(P)))

    return
end

load(::Type{P}, ::Type{<:Proposition}, path::Path) where P <: Proof = load(P, path)

function load(::Type{Simulator{P}}, path::Path; verifier_type = DEFAULT_VERIFIER) where P <: Proposition

    proposition = load(P, path)
    proof = load(proof_type(proposition), P, joinpath(path, "nizkp"))
    verifier = load(verifier_type, joinpath(path, treespec(verifier_type)))

    return Simulator(proposition, proof, verifier)
end


load(path::Path) = load(get_simulator_type(path), path)
load(path::String) = load(LocalPath(path))


treespec(::T) where T <: Union{Proposition, Proof, Verifier, Simulator} = treespec(T)
treespec(::Type{T}, ::Type{<:Proposition}) where T <: Proof = treespec(T) # This allows prefix specialization
treespec(::Type{Simulator{P}}) where P <: Proposition = (treespec(DEFAULT_VERIFIER), treespec(P)..., joinpath.("nizkp", treespec(proof_type(P), P))...)

treespec(::Type{Simulator}) = error("Tree specification for $(typeof(obj)) is not specified. Specify it by providing `treespec` argument manually to digest.")


function digest(obj::Union{Proposition, Proof, Simulator, Verifier} , hasher::HashSpec; treespec=treespec(obj))

    path_hasher = PathHasher(hasher)
    save(obj, path_hasher)

    @check length(path_hasher.digests) == length(treespec) "`treespec` is not compatable with $(typeof(obj)) output."

    digests = Vector{UInt8}[]

    for i in treespec
        
        N = findfirst(x -> first(x) == i, path_hasher.digests)
        @assert !isnothing(N) "$i is not written in $(typeof(obj)) output."
        push!(digests, last(path_hasher.digests[N]))
        
    end

    return hasher(vcat(digests...))
end

# This puts in assumption here
function get_simulator_type(dir::Path)
    
    xmlpath = joinpath(dir, "protInfo.xml")

    if !isfile(xmlpath)
        error("protInfo.xml not found in $dir")
    end

    xml = read(xmlpath) |> String
    name = match(r"<name>(.*?)</name>", xml)[1] |> Symbol

    # Now I need to list all subtypes of proposition

    types = subtypes(Proposition)
    N = findfirst(x -> nameof(x) == name, types)

    @assert !isnothing(N) "Simualtor type $name not found"

    return Simulator{types[N]}
end

get_simulator_type(dir::String) = get_simulator_type(LocalPath(dir))

digest(dir::Path, hasher::HashSpec) = digest(get_simulator_type(dir), dir, hasher)
digest(dir::AbstractString, hasher::HashSpec) = digest(get_simulator_type(dir), LocalPath(dir), hasher)

function digest(::Type{S}, dir::Path, hasher::HashSpec) where S <: Simulator
    
    digests = []

    for path in treespec(S)

        bytes = read(joinpath(dir, path))
        push!(digests, hasher(bytes))

    end

    return hasher(vcat(digests...))
end

digest(::Type{S}, dir::AbstractString, hasher::HashSpec) where S <: Simulator = digest(S, LocalPath(dir), hasher)


end
