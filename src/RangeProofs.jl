module RangeProofs

using CryptoGroups
using CryptoGroups.Utils: @check
using ..SigmaProofs: Proposition, Proof, Verifier
using ..SigmaProofs.LogProofs: ChaumPedersenProof

# TODO: NEED TO DO TDD TO GET THE CODE IN WORKING STATE

# A range proof is a cryptographic technique that demonstrates a secret message belongs to a set of group elements defined by a specific range of exponents, without revealing the actual message. This code focuses on a simplified version for a single bit, as described in reference [1]. This implementation proves two statements in parallel, with one serving as a "dummy" statement, exemplifying a basic form of OR composition in cryptography. This approach represents one of the simplest examples of OR composition. For those interested in exploring more complex OR and AND compositions in cryptographic protocols, lecture notes [2] provides a good starting point.

# Although more efficient techniques like Bulletproofs exist for range proofs, this simpler version of range proofs remains widely used, particularly in electronic voting systems. This is due to the typically small ranges in voting scenarios (such as yes/no questions) and the need for straightforward encoding to easily match decrypted elements back to their original range. As a general principle, it's often advisable to implement prototypes using this simpler version before considering more complex optimization techniques to reduce proof size. This approach allows for easier development, testing, and verification of the core functionality before introducing additional complexities.

# [1]: Ronald Cramer, Rosario Gennaro, and Berry Schoenmakers. 1997. A secure and optimally efficient multi-authority election scheme. In Proceedings of the 16th annual international conference on Theory and application of cryptographic techniques (EUROCRYPT'97). Springer-Verlag, Berlin, Heidelberg, 103–118. https://link.springer.com/chapter/10.1007/3-540-69053-0_9

# [2] Schoenmakers, B. (2024). Lecture Notes Cryptographic Protocols (Version 1.9). Department of Mathematics and Computer Science, Technical University of Eindhoven.


# To encode larger ranges we can make proofs with 𝐺, 𝐺^2, 𝐺^4 and then do homomoprhic sum.
# For this to work we need to modify the proof a little by transforming v=-1 case to v=0 case
struct ElGamalBitRange{G<:Group} <: Proposition
    g::G # Generator
    h::G # The public key; It happens to be used in pedersen commitment which may be wrong!!!
    𝐺::G # The message used, may need to be chose independently from the generator
    x::G
    y::G
end

struct ElGamalBitProof{G<:Group} <: Proof
    # Commitment
    a₁::G
    b₁::G
    a₂::G
    b₂::G

    # Response
    d₁::BigInt
    d₂::BigInt
    r₁::BigInt
    r₂::BigInt
end



function prove(proposition::ElGamalBitRange{G}, verifier::Verifier, v::Int, α::BigInt) where G <: Group

    (; g, h, 𝐺, x, y) = proposition

    𝑤 = rand(2:order(G)-1)

    if v == 1

        r₁ = rand(2:order(G)-1)
        d₁ = rand(2:order(G)-1)
        
        #a₁ = g^r₁ * x^d₁ # Why not
        a₁ = g^(r₁ + α * d₁)
        b₁ = h^r₁ * (y*𝐺)^d₁
        #b₁ = h^r₁ * (y/𝐺)^d₁

        a₂ = g^𝑤
        b₂ = h^𝑤

        c = challenge(verifier, proposition, a₁, b₁, a₂, b₂)
        
        d₂ = c - d₁
        r₂ = 𝑤 - α * d₂

    elseif v == -1

        r₂ = rand(2:order(G)-1)
        d₂ = rand(2:order(G)-1)

        a₁ = g^𝑤
        b₁ = h^𝑤

        a₂ = g^r₂ * x^d₂
        b₂ = h^r₂ * (y/𝐺)^d₂
        #b₂ = h^r₂ * (y * 𝐺)^d₂

        c = challenge(verifier, proposition, a₁, b₁, a₂, b₂)

        d₁ = c - d₂
        r₁ = 𝑤 - α * d₁
        
    else
        error("v must be +-1")
    end

    return ElGamalBitProof(a₁, b₁, a₂, b₂, d₁, d₂, r₁, r₂)
end


function verify(proposition::ElGamalBitRange{G}, proof::ElGamalBitProof{G}, verifier::Verifier) where G <: Group

    (; g, h, 𝐺, x, y) = proposition
    (; a₁, b₁, a₂, b₂, d₁, d₂, r₁, r₂) = proof

    c = challenge(verifier, proposition, a₁, b₁, a₂, b₂)

    c == d₁ + d₂ || return false

    a₁ == g^r₁ * x^d₁ || return false
    b₁ == h^r₁ * (y * 𝐺)^d₁ || return false
    #b₁ == h^r₁ * (y / 𝐺)^d₁ || return false

    a₂ == g^r₂ * x^d₂ || return false
    b₂ == h^r₂ * (y/G)^d₂ || return false
    #b₂ == h^r₂ * (y * G)^d₂ || return false

    return true
end


function bitenc(g::G, pk::G, value::Bool, verifier::Verifier; 𝐺::G = g, α = rand(2:order(G)-1))::Simulator where G <: Group

    x = g^α
    y = value ? pk^α * 𝐺 : pk^α / 𝐺

    proposition = ElGamalBitRange(g, pk, 𝐺, x, y)

    proof = prove(proposition, verifier, value, α)
    
    return Simulator(proposition, proof, verifier)
end



abstract type RangeCommitProof{G<:Group} <: Proof end

# To encode larger ranges we can make proofs with 𝐺, 𝐺^2, 𝐺^4 and then do homomoprhic sum.
# For this to work we need to modify the proof a little by transforming v=-1 case to v=0 case
struct BitCommit{G<:Group} <: Proposition
    g::G # Generator
    h::G # The public key; It happens to be used in pedersen commitment which may be wrong!!!
    𝐺::G # The message used, may need to be chose independently from the generator
    y::G
end

struct BitProof{G<:Group} <: RangeCommitProof{G}
    # Commitment
    b₁::G
    b₂::G

    # Response
    d₁::BigInt
    d₂::BigInt
    r₁::BigInt
    r₂::BigInt
end


function prove(proposition::BitCommit{G}, verifier::Verifier, v::Bool, α::BigInt) where G <: Group

    (; g, h, 𝐺, x, y) = proposition

    𝑤 = rand(2:order(G)-1)

    if v == 1

        r₁ = rand(2:order(G)-1)
        d₁ = rand(2:order(G)-1)
        
        b₁ = h^r₁ * y^d₁
        b₂ = h^𝑤

        c = challenge(verifier, proposition, b₁, b₂)
        
        d₂ = c - d₁
        r₂ = 𝑤 - α * d₂

    elseif v == 0

        r₂ = rand(2:order(G)-1)
        d₂ = rand(2:order(G)-1)

        b₁ = h^𝑤
        b₂ = h^r₂ * (y/𝐺)^d₂

        c = challenge(verifier, proposition, b₁, b₂)

        d₁ = c - d₂
        r₁ = 𝑤 - α * d₁
        
    else
        error("v must be {0, 1}")
    end

    return BitProof(b₁, b₂, d₁, d₂, r₁, r₂)
end


function verify(proposition::BitCommit{G}, proof::BitProof{G}, verifier::Verifier) where G <: Group

    (; g, h, 𝐺, x, y) = proposition
    (; b₁, b₂, d₁, d₂, r₁, r₂) = proof

    c = challenge(verifier, proposition, b₁, b₂)

    c == d₁ + d₂ || return false

    b₁ == h^r₁ * y^d₁ || return false
    b₂ == h^r₂ * (y/G)^d₂ || return false

    return true
end


function bitcommit(g::G, pk::G, value::Bool, verifier::Verifier; 𝐺::G = g, α = rand(2:order(G)-1))::Simulator where G <: Group

    #x = g^α
    y = value ? pk^α * 𝐺 : pk^α 

    proposition = BitCommit(g, pk, 𝐺, y)

    proof = prove(proposition, verifier, value, α)
    
    return Simulator(proposition, proof, verifier)
end


# struct ElGamalRange <: Proposition
#     range::
#     g::G
#     h::G
#     𝐺::G
#     x::G
#     y::G
# end


# BitCommit

# NRangeCommit

# RangeCommit

# BitRangeProof

# bitenc

# nbitenc # would use a BitCommit
# rangeenc # also would use a BitCommit




struct NRangeCommit{G<:Group} <: Proposition
    n::Int # 0 < ν < 2^n
    g::G
    h::G
    𝐺::G
    y::G
end


struct NRangeProof{G<:Group} <: RangeCommitProof{G}
    bitcommits::Vector{G}
    bitproofs::Vector{BitProof{G}}
end


function prove(proposition::NRangeCommit{G}, verifier::Verifier, v::Int, α::Integer) where G <: Group

    (; n, g, h, 𝐺) = proposition

    ### Need a way to extract the bit from v

    bits = G[]
    proofs = BitProof{G}[]

    α_vec = rand(n+1, 2:order(G)-1)
    α_rest = sum(α_vec[2:end]) % order(G)
    α_vec[1] = α - α_rest % order(G) # This would ensure that resulting encryption is done with α

    for i in 0:n
        
        𝐺ᵢ = 𝐺^(2^i)
        value = v >> i % Bool
        
        simulator = bitcommit(g, h, value, verifier; 𝐺, α = α_vec[i])
        
        push!(proofs, simulator.proof)
        
        (; y) = simulator.proposition

        push!(bits, y)
    end

    return NRangeProof(encbits, bitproofs, verifier)
end


function verify(proposition::NRangeCommit{G}, proof::NRangeProof{G}, verifier::Verifier) where G <: Group

    (; n, g, h, 𝐺, y) = proposition
    (; bitcommits, bitproofs) = proof

    for (yi, bitproof, i) in zip(bitcommits, bitproofs, 0:n)
        
        𝐺ᵢ = 𝐺^(2^i)

        bitproposition = BitCommit(g, h, 𝐺ᵢ, yi)
        verify(bitproposition, bitproof, verifier) || return false
    end

    return true
end


function rangecommit(n::Int, g::G, pk::G, value::Int, verifier::Verifier; 𝐺::G = g, α = rand(2:order(G)-1))::Simulator where G <: Group
    @check 0 < value < 2^n

    y = pk^α * 𝐺^value

    proposition = NRangeCommit(n, g, h, 𝐺, y)
    proof = prove(proposition, verifier, v, α)

    return Simulator(proposition, proof, verifier)
end


struct RangeCommit{G<:Group} <: Proposition
    range::UnitRange # For the begining we shall assume that min is 0
    g::G
    h::G
    𝐺::G
    y::G
end

struct RangeProof{G<:Group} <: RangeCommitProof{G}
    left::NRangeProof{G}
    right::NRangeProof{G}
end


function prove(proposition::RangeCommit{G}, verifier::Verifier, value::Int; α = rand(2:order(G) - 1)) where G <: Group

    (; range, g, h, 𝐺, y) = proposition

    @assert minimum(range) == 0 "Not Implemented"

    n = bitlength(maximum(range) - minimum(range))
    
    Δ = 2^n - maximum(range) # Let's now consider minimum(range) == 0

    y = h^α * 𝐺^value

    left_proposition = NRangeCommit(n, g, h, 𝐺, y)
    left_proof = prove(left_proposition, verifer, value, α)

    right_proposition = NRangeCommit(n, g, h, 𝐺, y * 𝐺^Δ)
    right_proof = prove(right_proposition, verifer, value + Δ, α)
    
    return RangeProof(left_proof, right_proof)
end


function verify(proposition::RangeCommit{G}, proof::RangeProof{G}, verifier::Verifier) where G <: Group

    (; range, g, h, 𝐺, y) = proposition

    Δ = 2^n - maximum(range)

    left_proposition = NRange(n, g, h, 𝐺, y)
    verify(left_proposition, proof.left, verifier) || return false

    right_proposition = NRange(n, g, h, 𝐺, y * 𝐺^Δ)
    verify(right_proposition, proof.right, verifier) || return false

    # The link is established through the construction

    return true
end


function rangecommit(range::UnitRange, g::G, pk::G, value::Int, verifier::Verifier; 𝐺::G = g, α = rand(2:order(G)-1))::Simulator where G <: Group
    
    @check minimum(range) == 0 "Not implemented"
    @check minimum(range) < value < maximum(range)

    y = pk^α * 𝐺^value

    proposition = Range(range, g, h, 𝐺, y)
    proof = prove(proposition, verifier, v, α)

    return Simulator(proposition, proof, verifier)
end


# This proof ensures that ElGamal encryption is correct and is represeted as e = (a, b) = (g^α, pk^α * h^m)
# as long as h is independent generator from g. This proof is intended to be combined with range proof that 
# is only done on `b` coordinate treating it as blinded commitment. 
struct ElGamalEnc{G <: Group} <: Proposition
    g::G
    pk::G
    h::G
    x::G
    y::G
end


struct ElGamalEncProof{G <: Group} <: Proof
    t₁::G
    t₂::G
    s₁::BigInt
    s₂::BigInt
end


function prove(proposition::ElGamalEnc{G}, verifier::Verifier, m::Int, α::BigInt) where G <: Group

    (; g, pk, h, x, y) = proposition

    r₁ = rand(2:order(G)-2)
    r₂ = rand(2:order(G)-2)

    t₁ = g^r₁
    t₂ = pk^r₁ * h^r₂

    c = challenge(proposition, verifier, t₁, t₂)    

    s₁ = r₁ + α * c
    s₂ = r₂ + c * m

    return ElGamalEncProof(t₁, t₂, s₁, s₂)
end


function verify(proposition::ElGamalEnc{G}, proof::ElGamalEncProof{G}, verifier::Verifier) where G <: Group

    (; g, pk, h, x, y) = proposition
    (; t₁, t₂, s₁, s₂) = proof

    c = challenge(proposition, verifier, t₁, t₂)

    g^s₁ == t₁ * a^c || return false
    pk^s₁ * h^s₂ == t₂ * b^c || return false

    return true
end


function enc(g::G, pk::G, h::G, m::Int, verifier::Verifier; α = rand(2:order(G) - 1)) where G <: Group

    x = g^α
    y = iszero(m) ? pk^α : pk^α * h^m
    
    proposition = ElGamalEnc(g, pk, h, x, y)
    proof = prove(proposition, verifier, m, α)

    return Simulator(proposition, proof, verifier)
end


struct ElGamalRange{G<:Group} <: Proposition
    range::Union{Bool, Int, UnitRange}
    g::G
    pk::G
    h::G
    x::G
    y::G
end


struct ElGamalRangeProof{G<:Group} <: Proof
    encryption::ElGamalEncProof{G}
    range::RangeCommitProof{G}
end


_range_proposition(::Bool, g::G, pk::G, 𝐺::G, y::G) where G <: Group = BitCommit(g, pk, 𝐺, y)
_range_proposition(n::Int, g::G, pk::G, 𝐺::G, y::G) where G <: Group = NRangeCommit(n, g, pk, 𝐺, y)
_range_proposition(range::UnitRange, g::G, pk::G, 𝐺::G, y::G) where G <: Group = RangeCommit(range, g, pk, 𝐺, y)


function prove(proposition::ElGamalRange{G}, verifier::Verifier, v::Int; α = rand(2:order(G) - 1)) where G <: Group

    (; range, g, pk, h, x, y) = proposition

    encryption_prop = ElGamalEnc(g, pk, h, x, y)
    encryption_proof = prove(encryption_prop, verifier, v, α)

    range_prop = _range_proposition(range, g, pk, h, y)
    range_proof = prove(range_prop, verifier, v; α)

    return ElGamalRangeProof(encryption_proof, range_proof)
end


function verify(proposition::ElGamalRange{G}, proof::ElGamalRangeProof{G}, verifier::Verifier) where G <: Group

    (; range, g, pk, h, x, y) = proposition

    encryption_prop = ElGamalEnc(g, pk, h, x, y)
    verify(encryption_prop, proof.encryption, verifier) || return false

    range_prop = _range_proposition(range, g, pk, h, y)
    verify(range_prop, proof.range, verifier) || return false

    return true
end


function rangeenc(range, g::G, pk::G, value::Int, verifier::Verifier; 𝐺::G = g, α = rand(2:order(G)-1)) where G <: Group

    x = g^α
    y = pk^α * h^value
    
    proposition = ElGamalRange(range, g, pk, 𝐺, x, y)
    proof = prove(proposition, verifier, value; α)

    return Simulator(proposition, proof, verifier)
end


### Now let's implement plaintext equivalence proofs
# only works as long as message is encrypted in an independent generator from g, pk
struct PlaintextEquivalence{G<:Group} <: Proposition
    g::G
    pk::G
    a::G
    b::G
    a′::G
    b′::G
end

# 
struct PlaintextEquivalenceProof{G<:Group} <: Proof
    blinding_factor::G
    blinded_ax::G
    blinded_ax′::G
    exponentiation::ChaumPedersenProof{G}
end


function prove(proposition::PlaintextEquivalence{G}, verifier::Verifier, power::BigInt; β = rand(2:order(G)-1)) where G <: Group

    (; g, pk, a, b, a′, b′) = proposition

    # a random generator is actually better here, as it prevents to learn plaintext if LogEquality have been     
    # obtained from a distributed execution
    blinding_factor = g^β 
    
    blinded_a = blinding_factor * a
    blinded_a′ = blinding_factor * a′

    simulator = exponentiate([g, blinded_a, blinded_a′], power, verifier)

    blinded_ax = simulator.proposition.pk[2]
    blinded_ax′ = simulator.proposition.pk[3]

    return PlainTextEquivalenceProof(blinding_factor, blinded_ax, blinded_ax′, simulator.proof)
end


function verify(proposition::PlaintextEquivalence{G}, proof::PlaintextEquivalenceProof{G}, verifier::Verifier) where G <: Group

    (; g, pk, a, b, a′, b′) = proposition
    (; blinding_factor, blinded_ax, blinded_ax′) = proof

    b/blinded_ax == b′/blinded_ax′ || return false

    g_vec = [g, blinding_factor * a, blinding_factor * a′]
    y_vec = [pk, blinded_ax, blinded_ax′]

    proposition = LogEquality(g_vec, y_vec)

    verify(proposition, proof.exponentiation, verifer) || return false

    return true
end


function substitute(g::G, pk::G, a::G, b::G, power::BigInt, α::BigInt, verifier::Verifier) where G <: Group 

    m = b / a^power

    a′ = g^α
    b′ = pk^α * m
    
    proposition = PlaintextEquivalence(g, pk, a, b, a′, b′)

    proof = prove(proposition, verifier, power)

    return Simulator(proposition, proof, verifier)
end


end
