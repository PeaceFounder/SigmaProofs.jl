module LogProofs

using CryptoGroups: Group, order, octet
using CryptoGroups.Utils: int2octet

using CryptoPRG.Verificatum: ROPRG, PRG, HashSpec, bitlength
using ..Serializer: Serializer, Path
import ..SigmaProofs: prove, verify, proof_type
using ..SigmaProofs: Proposition, Verifier, Proof, Simulator, challenge, Parser, gen_roprg
using Base.Iterators: flatten
using ..SigmaProofs.Parser: Tree


struct LogKnowledge{G <: Group} <: Proposition
    g::G
    y::G
end

struct SchnorrProof{G <: Group} <: Proof 
    R::G
    s::BigInt
end

proof_type(::Type{LogKnowledge{G}}) where G <: Group = SchnorrProof{G}

function prove(proposition::LogKnowledge{G}, verifier::Verifier, x::Integer; suffix = nothing) where G <: Group

    (; g, y) = proposition

    # we can construct proof deterministically without relying on randomness source
    roprg = gen_roprg([octet(y)..., int2octet(x)...])
    #prg = PRG(HashSpec("sha256"), [octet(y)..., int2octet(x)...])

    r = rand(roprg(:x), 2:order(G) - 1)

    R = g^r

    #c = challenge(verifier, proposition, R; filter(!isnothing, (;suffix))...) 
    c = isnothing(suffix) ? challenge(verifier, proposition, R) : challenge(verifier, proposition, R; suffix)

    s = (r + c * x) % order(G)

    return SchnorrProof(R, s)
end

function verify(proposition::LogKnowledge, proof::SchnorrProof, verifier::Verifier; suffix = nothing)

    (; g, y) = proposition
    (; R, s) = proof

    #c = challenge(verifier, proposition, R; filter(!isnothing, (;suffix))...)
    c = isnothing(suffix) ? challenge(verifier, proposition, R) : challenge(verifier, proposition, R; suffix)

    return g^s == R * y^c
end


# Proposition is that g .^ x = y
struct LogEquality{G <: Group} <: Proposition
    g::Vector{G}
    y::Vector{G}
end

Base.length(proposition::LogEquality) = length(proposition.g)

struct ChaumPedersenProof{G} <: Proof
    commitment::Vector{G}
    response::BigInt
end

proof_type(::Type{LogEquality{G}}) where G <: Group = ChaumPedersenProof{G}

Base.:(==)(x::T, y::T) where T <: ChaumPedersenProof = x.commitment == y.commitment && x.response == y.response




function prove(proposition::LogEquality{G}, verifier::Verifier, power::Integer; roprg = gen_roprg())::ChaumPedersenProof where G <: Group

    (; g, y) = proposition

    q = order(G)

    s = rand(roprg(:r), 2:q - 1) 
    
    commitment = g .^ s

    c = challenge(verifier, proposition, commitment)

    response = s + c * power
    
    return ChaumPedersenProof(commitment, mod(response, q))    
end

verify(proposition::LogEquality, power::Integer)::Bool = proposition.g .^ power == proposition.y

function verify(proposition::LogEquality, proof::ChaumPedersenProof, verifier::Verifier)::Bool

    (; g, y) = proposition
    (; commitment, response) = proof

    c = challenge(verifier, proposition, commitment)

    for i in 1:length(proposition)
        g[i] ^ response == commitment[i] * y[i] ^ c || return false
    end

    return true
end


function exponentiate(g::Vector{<:Group}, power::Integer)::LogEquality
    y = g .^ power
    return LogEquality(g, y)
end

function exponentiate(g::Vector{<:Group}, power::Integer, verifier::Verifier)::Simulator

    proposition = exponentiate(g, power)
    proof = prove(proposition, verifier, power)

    return Simulator(proposition, proof, verifier)
end



# ToDo
function Serializer.save(proof::ChaumPedersenProof, dir::Path; prefix = "ChaumPedersen") 

    (; commitment, response) = proof

    L = bitlength(commitment[1])

    write(joinpath(dir, "$(prefix)Commitment.bt"), Tree(commitment))
    write(joinpath(dir, "$(prefix)Reply.bt"), Tree(response; L))

    return
end


function Serializer.load(::Type{ChaumPedersenProof{G}}, dir::Path; prefix = "ChaumPedersen") where G <: Group
# I could use kwargs for save and load with ChaumPedersenProof
# Or perhaps it is better to leave it as ChaumPedersenCommitment.bt and ChaumPedersenReply.bt
# I could also have a prefix argument! prefix = "Decryption"|"DecryptionInv"|"ChaumPedersen"

    #G = typeof(g)

    τ_tree = Parser.decode(read(joinpath(dir, "$(prefix)Commitment.bt")))
    τ = convert(Vector{G}, τ_tree)

    r_tree = Parser.decode(read(joinpath(dir, "$(prefix)Reply.bt")))
    r = convert(BigInt, r_tree)

    #return DecryptionProof(τ, r)
    return ChaumPedersenProof(τ, r)
end

Serializer.treespec(::Type{ChaumPedersenProof}; prefix = "ChaumPedersen") = (
    "$(prefix)Commitment.bt",
    "$(prefix)Reply.bt"
)



end
