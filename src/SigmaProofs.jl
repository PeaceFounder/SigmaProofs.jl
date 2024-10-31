module SigmaProofs

using Random: RandomDevice
using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: ROPRG, PRG

include("ElGamal.jl")
include("Parser.jl")

abstract type Proposition end
abstract type Verifier end
abstract type Proof end

proof_type(::T) where T <: Proposition = proof_type(T)

struct Simulator{T<:Proposition}
    proposition::T
    proof::Proof
    verifier::Verifier

    function Simulator(proposition::Proposition, proof::Proof, verifier::Verifier)

        # Alternative is to do conversion here if necessary
        @assert isvalid(typeof(proof), proposition) "Inconsistent simulator"

        return new{typeof(proposition)}(proposition, proof, verifier)
    end
end

Base.:(==)(x::T, y::T) where T <: Simulator = x.proposition == y.proposition && x.proof == y.proof && x.verifier == y.verifier

verify(simulator::Simulator) = verify(simulator.proposition, simulator.proof, simulator.verifier)
proof_type(::Simulator{T}) where T <: Proposition = proof_type(T)

Base.isvalid(P::Type{<:Proof}, ::T) where T <: Proposition = P == proof_type(T)

function challenge end
function prove end
function generator_basis end

function gen_roprg(ρ::AbstractVector{UInt8})

    rohash = HashSpec("sha256")
    prghash = HashSpec("sha256")
    roprg = ROPRG(ρ, rohash, prghash)

    return roprg
end

gen_roprg() = gen_roprg(rand(RandomDevice(), UInt8, 32))

gen_roprg(prg::PRG) = gen_roprg(prg.s)


include("Serializer.jl")
include("LogProofs.jl")
include("DecryptionProofs.jl")
include("CommitmentShuffle.jl")
include("RangeProofs.jl")
include("SecretSharing.jl")
include("Verificatum/Verificatum.jl")

# It is highly unlikelly that one would need to work with multiple verifier implementations 
# at the same time for the same object. This can be reconsidered in the future.
Serializer.DEFAULT_VERIFIER = Verificatum.ProtocolSpec

end
