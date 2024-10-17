module RangeProofs

using CryptoGroups
using CryptoGroups.Utils: @check
using ..SigmaProofs: Proposition, Proof, Verifier, Simulator, challenge
using ..SigmaProofs.LogProofs: ChaumPedersenProof, exponentiate, LogEquality
import ..SigmaProofs: proof_type, prove, verify, gen_roprg
using CryptoPRG: bitlength

# A range proof is a cryptographic technique that demonstrates a secret message belongs to a set of group elements defined by a specific range of exponents, without revealing the actual message. This code focuses on a simplified version for a single bit, as described in reference [1]. This implementation proves two statements in parallel, with one serving as a "dummy" statement, exemplifying a basic form of OR composition in cryptography. This approach represents one of the simplest examples of OR composition. For those interested in exploring more complex OR and AND compositions in cryptographic protocols, lecture notes [2] provides a good starting point.

# Although more efficient techniques like Bulletproofs exist for range proofs, this simpler version of range proofs remains widely used, particularly in electronic voting systems. This is due to the typically small ranges in voting scenarios (such as yes/no questions) and the need for straightforward encoding to easily match decrypted elements back to their original range. As a general principle, it's often advisable to implement prototypes using this simpler version before considering more complex optimization techniques to reduce proof size. This approach allows for easier development, testing, and verification of the core functionality before introducing additional complexities.

# [1]: Ronald Cramer, Rosario Gennaro, and Berry Schoenmakers. 1997. A secure and optimally efficient multi-authority election scheme. In Proceedings of the 16th annual international conference on Theory and application of cryptographic techniques (EUROCRYPT'97). Springer-Verlag, Berlin, Heidelberg, 103–118. https://link.springer.com/chapter/10.1007/3-540-69053-0_9

# [2] Schoenmakers, B. (2024). Lecture Notes Cryptographic Protocols (Version 1.9). Department of Mathematics and Computer Science, Technical University of Eindhoven.

struct ElGamalBitRange{G<:Group} <: Proposition
    g::G 
    h::G # public key
    𝐺::G # message base
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

proof_type(::Type{ElGamalBitRange{G}}) where G <: Group = ElGamalBitProof{G}

function prove(proposition::ElGamalBitRange{G}, verifier::Verifier, v::Integer, α::Integer; roprg = gen_roprg()) where G <: Group

    (; g, h, 𝐺, x, y) = proposition

    𝑤 = rand(roprg(:𝑤), 2:order(G)-1)

    if v == 1

        r₁ = rand(roprg(:r), 2:order(G)-1)
        d₁ = rand(roprg(:d), 2:order(G)-1)
        
        a₁ = g^(r₁ + α * d₁)
        b₁ = h^r₁ * (y*𝐺)^d₁

        a₂ = g^𝑤
        b₂ = h^𝑤

        c = challenge(verifier, proposition, a₁, b₁, a₂, b₂)
        
        d₂ = c - d₁
        r₂ = 𝑤 - α * d₂

    elseif v == -1

        r₂ = rand(roprg(:r), 2:order(G)-1)
        d₂ = rand(roprg(:d), 2:order(G)-1)

        a₁ = g^𝑤
        b₁ = h^𝑤

        a₂ = g^r₂ * x^d₂
        b₂ = h^r₂ * (y/𝐺)^d₂

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

    a₂ == g^r₂ * x^d₂ || return false
    b₂ == h^r₂ * (y/𝐺)^d₂ || return false

    return true
end


function bitenc(g::G, pk::G, value::Bool, verifier::Verifier; roprg = gen_roprg(), 𝐺::G = g, α = rand(roprg(:α), 2:order(G)-1))::Simulator where G <: Group

    x = g^α
    y = value ? pk^α * 𝐺 : pk^α / 𝐺

    proposition = ElGamalBitRange(g, pk, 𝐺, x, y)

    proof = prove(proposition, verifier, value ? 1 : -1, α; roprg)
    
    return Simulator(proposition, proof, verifier)
end


abstract type RangeCommitProof{G<:Group} <: Proof end

# To encode larger ranges we can make proofs with 𝐺, 𝐺^2, 𝐺^4 and then do homomoprhic sum.
# For this to work we need to modify the proof a little by transforming v=-1 case to v=0 case
struct BitCommit{G<:Group} <: Proposition
    g::G # Redundant!!! # Generator
    h::G # The public key; It happens to be used in pedersen commitment which may be wrong!!!
    #𝐺::G # The message used, may need to be chose independently from the generator
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

proof_type(::Type{BitCommit{G}}) where G <: Group = BitProof{G}

function prove(proposition::BitCommit{G}, verifier::Verifier, v::Bool, α::Integer; roprg = gen_roprg()) where G <: Group

    (; g, h, y) = proposition

    𝑤 = rand(roprg(:𝑤), 2:order(G)-1)

    if v == 1

        r₁ = rand(roprg(:r), 2:order(G)-1)
        d₁ = rand(roprg(:d), 2:order(G)-1)
        
        b₁ = h^r₁ * y^d₁
        b₂ = h^𝑤

        c = challenge(verifier, proposition, b₁, b₂)
        
        d₂ = c - d₁
        r₂ = 𝑤 - α * d₂

    elseif v == 0

        r₂ = rand(roprg(:r), 2:order(G)-1)
        d₂ = rand(roprg(:d), 2:order(G)-1)

        b₁ = h^𝑤
        b₂ = h^r₂ * (y/g)^d₂

        c = challenge(verifier, proposition, b₁, b₂)

        d₁ = c - d₂
        r₁ = 𝑤 - α * d₁
        
    else
        error("v must be {0, 1}")
    end

    return BitProof(b₁, b₂, d₁, d₂, r₁, r₂)
end


function verify(proposition::BitCommit{G}, proof::BitProof{G}, verifier::Verifier) where G <: Group

    (; g, h, y) = proposition
    (; b₁, b₂, d₁, d₂, r₁, r₂) = proof

    c = challenge(verifier, proposition, b₁, b₂)

    c == d₁ + d₂ || return false

    b₁ == h^r₁ * y^d₁ || return false
    b₂ == h^r₂ * (y/g)^d₂ || return false

    return true
end


function bitcommit(g::G, pk::G, value::Bool, verifier::Verifier; roprg = gen_roprg(), α = rand(roprg(:α), 2:order(G)-1))::Simulator where G <: Group

    y = value ? pk^α * g : pk^α 

    proposition = BitCommit(g, pk, y)

    proof = prove(proposition, verifier, value, α; roprg)
    
    return Simulator(proposition, proof, verifier)
end


struct NRangeCommit{G<:Group} <: Proposition
    n::Int # 0 < ν < 2^n
    g::G ## Redundant!!!
    h::G
    #𝐺::G # I could replace 𝐺 with g
    y::G
end


struct NRangeProof{G<:Group} <: RangeCommitProof{G}
    bitcommits::Vector{G}
    bitproofs::Vector{BitProof{G}}
end

proof_type(::Type{NRangeCommit{G}}) where G <: Group = NRangeProof{G}

function prove(proposition::NRangeCommit{G}, verifier::Verifier, v::Int; roprg = gen_roprg(), α = rand(roprg(:α), 2:order(G) - 1)) where G <: Group

    (; n, g, h) = proposition

    ### Need a way to extract the bit from v

    encbits = G[]
    bitproofs = BitProof{G}[]

    α_vec = rand(roprg(:α_vec), 2:order(G)-1, n)
    α_rest = sum(α_vec[2:end]) % order(G)
    α_vec[1] = mod(α - α_rest, order(G)) # This would ensure that resulting encryption is done with α

    for i in 0:n - 1
        
        gᵢ = g^(2^i)
        value = v >> i % Bool
        
        # We can't past roprg here directly as that would prodce collisions
        simulator = bitcommit(gᵢ, h, value, verifier; α = α_vec[i + 1], roprg = gen_roprg(roprg("bitcommit_$i"))) 
        
        push!(bitproofs, simulator.proof)
        
        (; y) = simulator.proposition

        push!(encbits, y)
    end

    return NRangeProof(encbits, bitproofs)
end


function verify(proposition::NRangeCommit{G}, proof::NRangeProof{G}, verifier::Verifier) where G <: Group

    (; n, g, h, y) = proposition
    (; bitcommits, bitproofs) = proof

    prod(bitcommits) == y || return false

    for (yi, bitproof, i) in zip(bitcommits, bitproofs, 0:n-1)
        
        gᵢ = g^(2^i)

        bitproposition = BitCommit(gᵢ, h, yi)
        verify(bitproposition, bitproof, verifier) || return false
    end

    return true
end


function rangecommit(n::Int, g::G, pk::G, value::Int, verifier::Verifier; roprg = gen_roprg(), α = rand(roprg(:α), 2:order(G)-1), skip_checks = false)::Simulator where G <: Group
    skip_checks || @check 0 <= value < 2^n

    y = pk^α * (iszero(value) ? one(G) : g^value)

    proposition = NRangeCommit(n, g, pk, y)
    proof = prove(proposition, verifier, value; α, roprg)

    return Simulator(proposition, proof, verifier)
end


struct RangeCommit{G<:Group} <: Proposition
    range::UnitRange # For the begining we shall assume that min is 0
    g::G
    h::G
    y::G
end

struct RangeProof{G<:Group} <: RangeCommitProof{G}
    left::NRangeProof{G}
    right::NRangeProof{G}
end

proof_type(::Type{RangeCommit{G}}) where G <: Group = RangeProof{G}

function prove(proposition::RangeCommit{G}, verifier::Verifier, value::Integer; roprg = gen_roprg(), α = rand(roprg(:α), 2:order(G) - 1)) where G <: Group

    (; range, g, h, y) = proposition

    n = bitlength(maximum(range) - minimum(range)) # TODO: may need +1 here; need to test that in a loop
    
    Δ_l = minimum(range)
    Δ_r = maximum(range) - 2^n + 1

    y = h^α * g^value
    
    g_l = iszero(Δ_l) ? one(G) : g^Δ_l
    g_r = iszero(Δ_r) ? one(G) : g^Δ_r

    left_proposition = NRangeCommit(n, g, h, y / g_l)
    left_proof = prove(left_proposition, verifier, value - Δ_l; α, roprg = gen_roprg(roprg(:left)))

    right_proposition = NRangeCommit(n, g, h, y / g_r)
    right_proof = prove(right_proposition, verifier, value - Δ_r; α, roprg = gen_roprg(roprg(:right)))
    
    return RangeProof(left_proof, right_proof)
end


function verify(proposition::RangeCommit{G}, proof::RangeProof{G}, verifier::Verifier) where G <: Group

    (; range, g, h, y) = proposition

    n  = bitlength(maximum(range) - minimum(range))

    Δ = 2^n - (maximum(range) - minimum(range)) # the gap

    Δ_l = minimum(range)
    Δ_r = maximum(range) - 2^n + 1

    g_l = iszero(Δ_l) ? one(G) : g^Δ_l
    g_r = iszero(Δ_r) ? one(G) : g^Δ_r

    left_proposition = NRangeCommit(n, g, h, y / g_l)
    verify(left_proposition, proof.left, verifier) || return false

    right_proposition = NRangeCommit(n, g, h, y / g_r)
    verify(right_proposition, proof.right, verifier) || return false

    # The link is established through the construction

    return true
end


function rangecommit(range::UnitRange, g::G, pk::G, value::Int, verifier::Verifier; roprg = gen_roprg(), α = rand(roprg(:α), 2:order(G)-1), skip_checks = false)::Simulator where G <: Group
    
    skip_checks || @check minimum(range) <= value <= maximum(range)

    y = pk^α * g^value

    proposition = RangeCommit(range, g, pk, y)
    proof = prove(proposition, verifier, value; α, roprg)

    return Simulator(proposition, proof, verifier)
end


# This proof ensures that ElGamal encryption is correct and is represeted as e = (a, b) = (g^α, pk^α * h^m)
# as long as h is independent generator from g. This proof is intended to be combined with range proof that 
# is only done on `b` coordinate treating it as blinded commitment. 
struct ElGamalEnc{G <: Group} <: Proposition
    g::G
    pk::G
    h::G
    a::G
    b::G
end

struct ElGamalEncProof{G <: Group} <: Proof
    t₁::G
    t₂::G
    s₁::BigInt
    s₂::BigInt
end

proof_type(::Type{ElGamalEnc{G}}) where G <: Group = ElGamalEncProof{G}

function prove(proposition::ElGamalEnc{G}, verifier::Verifier, m::Int, α::BigInt; roprg = gen_roprg()) where G <: Group

    (; g, pk, h, a, b) = proposition

    r₁ = rand(roprg(:r₁), 2:order(G)-2)
    r₂ = rand(roprg(:r₂), 2:order(G)-2)

    t₁ = g^r₁
    t₂ = pk^r₁ * h^r₂

    c = challenge(verifier, proposition, t₁, t₂)  

    s₁ = r₁ + α * c
    s₂ = r₂ + c * m

    return ElGamalEncProof(t₁, t₂, s₁, s₂)
end


function verify(proposition::ElGamalEnc{G}, proof::ElGamalEncProof{G}, verifier::Verifier) where G <: Group

    (; g, pk, h, a, b) = proposition
    (; t₁, t₂, s₁, s₂) = proof

    c = challenge(verifier, proposition, t₁, t₂)

    g^s₁ == t₁ * a^c || return false
    pk^s₁ * h^s₂ == t₂ * b^c || return false

    return true
end


function elgamalenc(g::G, pk::G, 𝐺::G, m::Int, verifier::Verifier; roprg = gen_roprg(), α = rand(roprg(:α), 2:order(G) - 1)) where G <: Group

    a = g^α
    b = iszero(m) ? pk^α : pk^α * 𝐺^m
    
    proposition = ElGamalEnc(g, pk, 𝐺, a, b)
    proof = prove(proposition, verifier, m, α; roprg)

    return Simulator(proposition, proof, verifier)
end

struct ElGamalRange{G<:Group} <: Proposition
    range::Union{Bool, Int, UnitRange}
    g::G
    pk::G
    𝐺::G
    x::G
    y::G
end

struct ElGamalRangeProof{G<:Group} <: Proof
    encryption::ElGamalEncProof{G}
    range::RangeCommitProof{G}
end

proof_type(::Type{ElGamalRange{G}}) where G <: Group = ElGamalRangeProof{G}

_range_proposition(::Bool, g::G, pk::G, y::G) where G <: Group = BitCommit(g, pk, y)
_range_proposition(n::Int, g::G, pk::G, y::G) where G <: Group = NRangeCommit(n, g, pk, y)
_range_proposition(range::UnitRange, g::G, pk::G, y::G) where G <: Group = RangeCommit(range, g, pk, y)


function prove(proposition::ElGamalRange{G}, verifier::Verifier, v::Int; α = rand(2:order(G) - 1), roprg = gen_roprg()) where G <: Group

    (; range, g, pk, 𝐺, x, y) = proposition

    encryption_prop = ElGamalEnc(g, pk, 𝐺, x, y)
    encryption_proof = prove(encryption_prop, verifier, v, α; roprg)

    range_prop = _range_proposition(range, 𝐺, pk, y)
    range_proof = prove(range_prop, verifier, v; α, roprg)

    return ElGamalRangeProof(encryption_proof, range_proof)
end


function verify(proposition::ElGamalRange{G}, proof::ElGamalRangeProof{G}, verifier::Verifier) where G <: Group

    (; range, g, pk, 𝐺, x, y) = proposition

    encryption_prop = ElGamalEnc(g, pk, 𝐺, x, y)
    verify(encryption_prop, proof.encryption, verifier) || return false

    range_prop = _range_proposition(range, 𝐺, pk, y)
    verify(range_prop, proof.range, verifier) || return false

    return true
end


function rangeenc(range, g::G, pk::G, value::Integer, verifier::Verifier; roprg = gen_roprg(), 𝐺::G = g, α = rand(roprg(:α), 2:order(G)-1)) where G <: Group

    x = g^α
    y = pk^α * 𝐺^value
    
    proposition = ElGamalRange(range, g, pk, 𝐺, x, y)
    proof = prove(proposition, verifier, value; α, roprg)

    return Simulator(proposition, proof, verifier)
end


### Now let's implement plaintext equivalence proofs
# In case one can ensure that the input cyphertexts are correct ElGamal encryptions this is unnecessary as
# one then simply proves `dec(e1/e2) = 1`. To perform this proof one does not need to know the blinding factors, but the knowledge
# of the exponent of encrypted value is necessary. Depending of available knowledge this proposition can have multiple proof types.
struct PlaintextEquivalence{G<:Group} <: Proposition
    g::G
    pk::G
    a::G
    b::G
    a′::G
    b′::G
end

struct PlaintextEquivalenceProof{G<:Group} <: Proof
    blinding_factor::G
    blinded_ax::G
    blinded_ax′::G
    exponentiation::ChaumPedersenProof{G}
end

proof_type(::Type{PlaintextEquivalence{G}}) where G <: Group = PlaintextEquivalenceProof{G}

function prove(proposition::PlaintextEquivalence{G}, verifier::Verifier, power::Integer; roprg = gen_roprg(), β = rand(roprg(:β), 2:order(G)-1)) where G <: Group

    (; g, pk, a, b, a′, b′) = proposition

    # a random generator is actually better here, as it prevents to learn plaintext if LogEquality have been     
    # obtained from a distributed execution
    blinding_factor = g^β 
    
    blinded_a = blinding_factor * a
    blinded_a′ = blinding_factor * a′

    simulator = exponentiate([g, blinded_a, blinded_a′], power, verifier; roprg)

    blinded_ax = simulator.proposition.y[2]
    blinded_ax′ = simulator.proposition.y[3]

    return PlaintextEquivalenceProof(blinding_factor, blinded_ax, blinded_ax′, simulator.proof)
end


function verify(proposition::PlaintextEquivalence{G}, proof::PlaintextEquivalenceProof{G}, verifier::Verifier) where G <: Group

    (; g, pk, a, b, a′, b′) = proposition
    (; blinding_factor, blinded_ax, blinded_ax′) = proof

    b/blinded_ax == b′/blinded_ax′ || return false

    g_vec = [g, blinding_factor * a, blinding_factor * a′]
    y_vec = [pk, blinded_ax, blinded_ax′]

    proposition = LogEquality(g_vec, y_vec)

    verify(proposition, proof.exponentiation, verifier) || return false

    return true
end


function resetenc(g::G, pk::G, a::G, b::G, power::Integer, α::Integer, verifier::Verifier; roprg = gen_roprg()) where G <: Group 

    m = b / a^power

    a′ = g^α
    b′ = pk^α * m
    
    proposition = PlaintextEquivalence(g, pk, a, b, a′, b′)

    proof = prove(proposition, verifier, power; roprg)

    return Simulator(proposition, proof, verifier)
end


struct VickreyAuction{G<:Group} <: Proposition
    g::G
    h::G # blinding generator
    bids::Vector{G}
    value_win::Int
    winner::Int
    second::Int 
end

struct VickreyAuctionProof{G<:Group} <: Proof
    n::Int # necessary bitrange for the proofs; note it can reveal max_bid and hence may need to be set with a prove method
    β::BigInt # The blinding factor for the second largest bid
    range_win::NRangeProof{G}
    range_losses::Vector{NRangeProof{G}}
end

proof_type(::Type{<:VickreyAuction{G}}) where G <: Group = VickreyAuctionProof{G}

function prove(proposition::VickreyAuction{G}, verifier::Verifier, 𝛃::Vector{<:Integer}; values = decrypt_bids(proposition, 𝛃), n = bitlength(maximum(values))) where G <: Group

    (; g, h, bids, winner, second, value_win) = proposition

    value_max = values[winner]
    
    range_win = rangecommit(n, g, h, values[winner] - values[second], verifier; α = 𝛃[winner] - 𝛃[second])

    range_losses = NRangeProof{G}[]

    for (i, (valuei, βi)) in enumerate(zip(values, 𝛃))

        if i == winner || i == second
            continue
        end

        range = rangecommit(n, g, h, values[second] - valuei, verifier; α = 𝛃[second] - βi)

        push!(range_losses, range.proof)
    end

    return VickreyAuctionProof(n, 𝛃[second], range_win.proof, range_losses)
end


function verify(proposition::VickreyAuction{G}, proof::VickreyAuctionProof{G}, verifier::Verifier) where G <: Group

    (; g, h, bids, value_win, winner, second) = proposition
    (; n, β, range_win, range_losses) = proof
    
    bids[second] == h^β * g^value_win || return false

    proposition_win = NRangeCommit(n, g, h, bids[winner]/bids[second])

    verify(proposition_win, range_win, verifier) || return false

    for (i, bid) in enumerate(bids)
        i in (winner, second) && continue

        proposition = NRangeCommit(n, g, h, bids[second]/bid)
        verify(proposition, range_losses[i - count(j -> j < i, (winner, second))], verifier) || return false
    end

    return true
end


function decrypt_bid(b, β, g, h; n = 5)

    m = b / h^β
    
    isone(m) && return 0

    for i in 1:2^n
        g^i == m && return i
    end

    error("Value not in range") # In practice thoose are decrypted as a proof
end

function decrypt_bids(proposition, 𝛃; n = 5)

    (; bids, g, h) = proposition

    return decrypt_bid.(bids, 𝛃, g, h; n)
end


function vickrey_auction(bids::Vector{G}, g::G, h::G, 𝛃::Vector{<:Integer}, verifier::Verifier) where G <: Group

    values = [decrypt_bid(bidi, βi, g, h) for (bidi, βi) in zip(bids, 𝛃)]

    (value_max, winner) = findmax(values)
    (value_win, second) = findmax(values) do x
        if x == value_max
            return 0
        else
            return x
        end
    end

    proposition = VickreyAuction(g, h, bids, value_win, winner, second)

    proof = prove(proposition, verifier, 𝛃; values)

    return Simulator(proposition, proof, verifier)
end


end
