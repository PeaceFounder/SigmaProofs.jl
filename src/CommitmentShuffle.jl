module CommitmentShuffle

using CryptoGroups
using ..SigmaProofs: Proposition, Proof, Verifier, Simulator, challenge, generator_basis, gen_roprg
using ..SigmaProofs.LogProofs: SchnorrProof, LogKnowledge
import ..SigmaProofs: prove, verify, proof_type

# This document lays out a draft protocol that is designed to achieve information-theoretic security for a shuffle. The goal is to ensure long-lasting privacy if cryptogrpahically relevant quantum computer ever gets built in the future (which is unlikelly). The protocol requires interaction from the secret owners and hence it can not be used in cascade in a simple way, but it's outputs can be passed further down the line in ordinary ElGamal reencryption shuffle methods as implemented in ShuffleProofs. The everlating privacy in this way ends up being ensured by one authorithy which in if corrupt in the presence of quantum computer could link individual voters to votes and hence significatnly reduces the risk as there is no near term incentives for a corrupt authorithy to keep this data. 

# Note that this is a preliminary draft, and the protocol may not be sound and have already been revised multiple times because of that. There’s also possibility that similar protocols may already exist in published literature which would be good to know.

# Goal: This protocol creates a system where each member gets a new, unlinkable public key, while allowing for public verification 
# that each member received exactly one key, without revealing which key belongs to which member.

# 1. Setup:
#    - A verifiable generator list is established
#    - A blinding generator 'h' is set

# 2. Dealer-member interaction:
#    - Dealer sends a verifiably random generator g_i to each member
#    - Member generates x_i and β_i
#    - Member computes:
#      * u_i <- g_i^x
#      * C = h^β * u_i
#      * PoK{(x): u_i = g_i^x_i)
#    - Member sends back to dealer:
#      * Signed {C}
#      * β_i
#      * u_i
#      * PoK{(x): u_i <- g_i^x_i)
#    - Dealer publishes the commitment on a public bulletin board

# 3. Dealer's consistency proof:
#    - Dealer generates a secret vector r_i
#    - Computes A <- h^r * ∏ u_i^s_i
#    - Computes e_i from anouncement A using Fiat-Shamir transform
#    - Computes secrets:
#      * z = r + \sum_i \beta_i * e_i
#      * w_i = s_i + e_i 
#    - Announces on public bulletin board:
#      * Shuffled list of (u_i, g_i, PoK{(x_i): u_i = g_i^x_i}, w_i) and anouncement A, z

# 4. Verification process:
#    - Verify that every g_i was generated verifiably random
#    - Verify PoK for every generator used in the commitment proof PoK{(x): u_i = g_i^x_i}
#    - Compute e_i from A
#    - Check that h^z * ∏ u_i^(s_i) = A * ∏ C_i^e_i

# This protocol aims to ensure everlasting privacy in a braiding scheme by using generalized Pedersen commitments and zero-knowledge proofs. It allows members to participate individually with a dealer over a confidential quantum-resistant channel, addressing the potential threat of future quantum computers breaking the privacy of current cryptographic schemes.

# For convenience, in the case of braiding, this can be part of the registration protocol. Each member generates a list of key commitments by selecting verifiable generators at random locally, as well as the blinding factors. They then deliver the membership certificate that lists commitments along with the secrets via a quantum-resistant channel. The coresponding authetification can be performed via ordinary public key cryptography as currently there is no cryptographically relevant quantum computer that could compromise that and it does not help adversary in the future to break ever lasting privacy. 

# WARNING: THIS PROTOCOL IS CREATION OF MY OWN AND HAS NOT BEEN CHECKED RIGOROUSLY THAT IT IS BINDING

struct CommittedRow{G <: Group, T}
    g::G
    u::G
    m::T # Can be arbitrary type. A single group element, or ElGamalRow that can be passed further down to a mix cascade. 
    pok::SchnorrProof{G}
end

Base.isless(x::T, y::T) where T <: CommittedRow = isless(x.u, y.u)

function verify(row::CommittedRow, verifier::Verifier)

    (; m, g, u, pok) = row
    proposition = LogKnowledge(g, u)

    return verify(proposition, pok, verifier; suffix = m)
end

# perhaps naming it as dercom, derive_commit
function commit(m::G, g::G, h::G, verifier::Verifier; roprg = gen_roprg(), x = rand(roprg(:x), 2:order(G)-1)) where G <: Group

    u = g^x
    β = rand(roprg(:β), 2:order(G)-1)
    
    C = h^β * u

    pok = prove(LogKnowledge(g, u), verifier, x; suffix = m) 

    row = CommittedRow(g, u, m, pok)

    return row, C, β
end

isbinding(row::CommittedRow{G}, C::G, h::G, β::Integer) where G <: Group = h^β * row.u == C

struct Shuffle{G<:Group} <: Proposition # What is shown on public buletin board
    h::G
    𝐂::Vector{G} # need to be individually signed
    rows::Vector{<:CommittedRow{G}}
end

Base.length(proposition::Shuffle) = length(proposition.𝐂)

struct ShuffleProof{G<:Group} <: Proof
    A::G
    z::BigInt
    𝐰::Vector{BigInt} 
end

proof_type(::Type{Shuffle{G}}) where G <: Group = ShuffleProof{G}

function verify(proposition::Shuffle{G}, proof::ShuffleProof{G}, verifier::Verifier; nmax = 10 * length(proposition)) where G <: Group

    (; h, 𝐂, rows) = proposition
    (; A, z, 𝐰) = proof

    𝐠 = (i.g for i in rows)

    basis = generator_basis(verifier, G, nmax)

    h in 𝐠 && return false # blinding factor can't be one of the generators
    length(unique(𝐠)) == length(𝐠) || return false # every generator must be unique

    all(x -> x.g in basis, rows) || return false # generator not in basis

    all(x -> verify(x, verifier), rows) || return false # pok for committed value exponent

    # Now we have established that 𝐮 forms an independet generator basis set

    𝐞 = challenge(verifier, proposition, A)
    𝐮 = (x.u for x in rows)
    h^z * prod(𝐮 .^ 𝐰) == A * prod(𝐂 .^ 𝐞) || return false

    # Hence the vector (𝐠, 𝐮) is consistent with commitment vector 𝐂

    return true
end


# The blinding factors are for commitment order
# the proofs pok can be  oermuted sepereatelly in place

function prove(proposition::Shuffle{G}, verifier::Verifier, 𝛃::Vector{<:Integer}, 𝛙::Vector{<:Integer}; roprg = gen_roprg()) where G

    (; h, rows, 𝐂) = proposition
    𝐮 = (x.u for x in rows)

    𝐬 = rand(roprg(:𝐬), 2:order(G) - 1, length(𝛃))
    r = rand(roprg(:r), 2:order(G) - 1)

    A = h^r * prod(𝐮 .^ 𝐬)
    
    𝐞 = challenge(verifier, proposition, A)

    z = r + sum(𝛃 .* 𝐞)
    𝐰 = 𝐬 .+ view(𝐞, 𝛙)

    return ShuffleProof(A, z, 𝐰)
end 


function shuffle(rows::Vector{<:CommittedRow{G}}, h::G, 𝐂::Vector{G}, 𝛃::Vector{<:Integer}, verifier::Verifier; 𝛙 = sortperm(rows)) where G <: Group

    proposition = Shuffle(h, 𝐂, rows[𝛙])
    proof = prove(proposition, verifier, 𝛃, 𝛙)

    return Simulator(proposition, proof, verifier)
end


end
